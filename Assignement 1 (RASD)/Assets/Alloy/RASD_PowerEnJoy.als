/** SIGNATURES **/
/* Default Classes */
sig Stringa {}

sig Currency {}

sig Time {}

/* Custom Classes */
sig PaymentInformation {}

sig User {
	id: one Int,
	name: one Stringa,
	email: one Stringa,
	password: one Stringa,
	phoneNumber: one Stringa,
	paymentInformation: one PaymentInformation,
	fiscalCode: one Stringa,
	driverLicense: one Stringa,

	currentReservation: lone Reservation
} {
	id > 0
	email != password
}
	
sig Payment {
	id: Int,
	total: lone Currency,

	reservation: one Reservation
} {
	id > 0
}

sig Reservation {
	id: Int,
	startTime: one Time,

	user: one User,
	payment: one Payment,
	car: one Car,
	ride: lone Ride
} {
	id > 0
	car.status = INUSE or car.status = RESERVED
}

sig Ride {
	id: one Int,
	peopleCarried: one Int,
	startTime: one Time,
	endTime: lone Time, // zero if Ride isn't finished yet
} {
	id > 0
	peopleCarried > 0 and peopleCarried < 6
	startTime != endTime
}

sig Car {
	id: one Int,
	licensePlate: one Stringa,
	status: one CarStatus,
	plugged: Bool,
	battery: Int,

	currentRide: lone Ride,
	currentReservation: lone Reservation, 
	currentAddress: one Address
} {
	id > 0
	// battery range from 0 (0% of battery charge) to 6 (100% of battery charge)
	battery >= 0 and battery <= 6
	// 1 is considered 20% of battery charge
	(battery < 1 and status = OUTOFPOWER) or
		(battery > 0 and (status = AVAILABLE or status = RESERVED or status = INUSE))
}

sig Address {
	streetName: one Stringa,
	streetNumber: one Int,
	coordinates: one Stringa,

	car: set Car
} {
	streetNumber > 0
}

abstract sig SafeZone {
	id: one Int,
	zoneCoordinates: set Stringa,

	address: set Address
} {
	id > 0
	#address > 0
}

sig Normal extends SafeZone {}

sig Special extends SafeZone {
	parkingSpotQty: one Int
} {
	id > 0
	parkingSpotQty > 0
}

one sig MaintenanceService {
	car: set Car
}

abstract sig Discount {
	payment: set Payment
}

lone sig moreThanThreePassengers extends Discount {}

lone sig moreThanHalfBattery extends Discount {}

lone sig carPluggedInSpecialSafeZone extends Discount {}

// more than 3Km constraint is not modelled
lone sig moreThanThreeKmToSpecialSafeZoneOrBatteryLessThanTwenty extends Discount {}

/* Enums */
enum CarStatus {
	AVAILABLE,
	RESERVED,
	INUSE,
	OUTOFPOWER
}

enum Sign {
	POSITIVE,
	NEGATIVE
}

enum Bool {
	TRUE ,
	FALSE
}

/** FACTS **/
/* Duplicated instances */
// each User is not duplicated
fact noDuplicatedUsers {
	no u1, u2 : User |
		u1 != u2 and
		(u1.id = u2.id or // unique id
		u1.fiscalCode = u2.fiscalCode or // unique fiscalCode
		u1.email = u2.email or // unique email
		u1.driverLicense = u2.driverLicense) // unique driverLicense
}

// each Payment is not duplicated
fact noDuplicatedPayment {
	no p1, p2: Payment | p1 != p2 and p1.id = p2.id
}

// each Reservation is not duplicated
fact noDuplicatedReservation {
	no r1, r2: Reservation | r1 != r2 and r1.id = r2.id
}

// each Ride is not duplicated
fact noDuplicatedRide {
	no r1, r2: Ride | r1 != r2 and r1.id = r2.id
}

// each Car is not duplicated
fact noDuplicatedCar {
	no c1, c2: Car | c1 != c2 and
		(c1.id = c2.id or // unique id
		c1.licensePlate = c2.licensePlate) // unique licensePlate
}

// each SafeZone is not duplicated
fact noDuplicatedSafeZone {
	no s1, s2: SafeZone | s1 != s2 and s1.id = s2.id
}

// each Address is not duplicated
fact noDuplicateAddress {
	no a1, a2: Address | a1 != a2 and a1.coordinates = a2.coordinates
}

/* Relations */
// oneToOne biijective relation between Payment and Reservation
fact samePaymentAsReservation {
	all p: Payment | p.reservation.payment = p
}

// oneToOne biijective relation between Reservation and Car
fact sameReservationAsCar {
	all r: Reservation | r.car.currentReservation = r
	all c: Car | #{c.currentReservation} > 0 implies c.currentReservation.car = c
}

// oneToMany biijective relation between Car and Address
fact sameCarAsAddress {
	all c: Car | c in c.currentAddress.car
	
	all a: Address |
		let carWithThisAddress = {c: Car | c.currentAddress = a} |
		a.car = carWithThisAddress
}

// oneToOne biijective relation between Reservation and User
fact sameReservationAsUser {
	all r: Reservation | r.user.currentReservation = r
}

/* Domain Rules */
// PaymentInformation are present in the same number as the Users
fact nameNumberPaymentInformationAndUsers {
	#PaymentInformation = #User
}

// Users don't share PaymentInformation
fact noSharedPaymentInformationByUsers {
	no u1, u2: User | u1 != u2 and u1.paymentInformation = u2.paymentInformation
}

// Users don't share Reservations
fact noSharedCurrentReservationByUsers {
	no u1, u2: User | u1 != u2 and u1.currentReservation = u2.currentReservation
}

// Reservations don't share Cars
fact noSharedCarByReservations {
	no r1, r2: Reservation| r1 != r2 and r1.car = r2.car
}

// Reservations don't share Rides
fact noSharedRideByReservations {
	no r1, r2: Reservation | r1 != r2 and r1.ride = r2.ride
}

// SafeZones don't share Addresses
fact noShareAddressBySafeZone {
	no s1, s2: SafeZone | s1 != s2 and #(s1.address & s2.address) > 0
}

// MaintenanceService is connected with all Car that are OUTOFPOWER and are not plugged to the grid
fact maintenanceServiceConnectedOnlyWithOutOfPowerCars {
	all m: MaintenanceService, c: Car | (c.status = OUTOFPOWER and c.plugged = FALSE) implies
		c in m.car else !(c in m.car)
}

// Only Car that are INUSE can be connected to a Reservation with a Ride
fact onlyInUseCarHasARide {
	no c: Car | (c.status = OUTOFPOWER or c.status = AVAILABLE or c.status = RESERVED) and
	#c.currentRide > 0
}

// RESERVED Car can't have a Ride
fact reservationWithRideHasInUseCar {
	all r: Reservation | r.car.status = RESERVED implies
		#r.ride = 0 else #r.ride > 0
}

// every Ride belongs to a Reservation
fact rideShouldBeReferenced {
	#{c: Car | c.status = INUSE} = #Ride
}

// every parked Car (so with status AVAILABLE or OUTOFPOWER) is parked in a SafeZone
fact carsAreParkedInASafeZone {
	all c: Car | (c.status = AVAILABLE or c.status = OUTOFPOWER) implies
		one s: SafeZone | c.currentAddress in  s.address
}

// there can't be more Car than available ParkingSpotQty in a Special SafeZone
fact numberOfCarLessThanSpecialSafeZoneParkingSpotQty {
	all s: Special, c: Car | c.status != INUSE implies
		#((c.currentAddress)->(s.address)) <= s.parkingSpotQty
}

// a Car can be plugged only in a Special SafeZone
fact pluggedCarOnlyInSpecialSafeZone {
	all c: Car, s: Special | c.currentAddress in s.address implies
		(c.plugged = TRUE or c.plugged = FALSE) else c.plugged = FALSE
}

/* Existential */
// for PowerEnJoy to work it is needed at least one PowerEnJoy Car
fact atLeastACar {
	#Car > 0
}

// for PowerEnJoy to work it is needed at least one Special SafeZone
fact atLeastASpecialSafeZone {
	#Special > 0
}

/* Discounts */
// apply a discount of -10% if there are more than 3 people in a Car
fact moreThanThreePassengersDiscount {
	no d: moreThanThreePassengers, p: Payment |
		p.reservation.ride.peopleCarried <= 3 and p in d.payment
}

// apply a discount of -20% if Car's battery is greater than 50%
fact moreThanHalfBatteryDiscount {
	no d: moreThanHalfBattery, p: Payment |
		p.reservation.car.battery <= 3 and p in d.payment // range of battery is 0 to 6 where 3 is half
}

// apply a discount of -30% if Car is plugged in a Special SafeZone
fact  carPluggedInSpecialSafeZoneDiscount {
	no d: carPluggedInSpecialSafeZone, p: Payment |
		p.reservation.car.plugged = FALSE and p in d.payment
}

// apply a discount of +30% if a Car is parked with less than 20% of battery charge
fact moreThanThreeKmToSpecialSafeZoneOrBatteryLessThanTwentyDiscount {
	no d: moreThanThreeKmToSpecialSafeZoneOrBatteryLessThanTwenty, p: Payment, s: Special |
		p.reservation.car.battery > 1 and p.reservation.car.currentAddress in s.address and
		p in d.payment // range of battery is 0 to 6 where 1 is considered 20%
}

/** ASSERTIONS **/
// all INUSE Car should be connected with a Reservation with a Ride
assert inUseCarsHaveARide {
	no c: Car | c.status = RESERVED and #{c.currentReservation.ride} > 0
}

// AVAILABLE or OUTOFPOWER should not be Reserved
assert noOutOfPowerOrAvailableCarReserved {
	no c: Car, u: User | (c.status = AVAILABLE or c.status = OUTOFPOWER) and
		u.currentReservation.car = c
}

// the number of the Reservations should be less or equal to the number of the Users
assert reservationNumberLessOrEqualThanUsers {
	#Reservation <= #User
}

// the number of the Payments should be less or equal to the number of the Reservations
assert paymentNumberLessOrEqualThanReservation {
	#Payment <= #Reservation
}

/** PREDICATES **/
pred maintenanceServiceServedCar {
	#{c: Car | c.status = OUTOFPOWER} = 1
	#{MaintenanceService.car} = 1
}

pred show {
	#{c: Car | c.status = AVAILABLE} > 0
	#{c: Car | c.status = RESERVED} > 0
	#{c: Car | c.status = INUSE} > 0
	#{c: Car | c.status = OUTOFPOWER} > 0

	#{c: Car | c.plugged = TRUE} > 0
	#{c: Car | c.plugged = FALSE} > 0

	#User > 2
	#Reservation > 0
	#MaintenanceService.car > 0
	#{d: Discount | #{d.payment} > 0} > 2
	#SafeZone > 3
}

pred generalRasdExample {
	#Car = 3
	#User = 2
	#Reservation > 0
	#MaintenanceService.car = 0
	#{d: Discount | #{d.payment} > 0} > 0
	#SafeZone = 2
	#Address = 3
}

pred discountsAndMaintenanceServiceRasdExample {
	#{d: Discount | #{d.payment} > 0} = 2
	#MaintenanceService.car = 2
	#Address = 2
	#Car = 3
}

/** RUN AND CHECKS **/
// OK
check inUseCarsHaveARide for 15

// OK
check noOutOfPowerOrAvailableCarReserved for 15

// OK
check reservationNumberLessOrEqualThanUsers for 15

// OK
check paymentNumberLessOrEqualThanReservation for 15

// OK
run maintenanceServiceServedCar for 15

// OK
run show for 20

// OK
run generalRasdExample for 20

// OK
run discountsAndMaintenanceServiceRasdExample for 20
