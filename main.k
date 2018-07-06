Import Algorithm
Import Exception

Package Sequence {
	Type Infinite-Length
	Type Lazy

	Cons(len state accessor iterator) {
		Equal-Type(len #0) : nil
			Make(Lazy len state accessor iterator)
	}

	Infinite-Constructor(iterator) {
		state => Cons(Infinite-Length state '_ iterator)
	}

	Length(seq) {
		(l _) = Break(Lazy seq)

		Length = Throw:Type-Error("Sequence of unknown length")
		Length = Arity(seq)
		Length = l
	}

	State/Accessor/Iterator(seq) {
		(_ State Accessor Iterator) = Break(Lazy seq)
	}

	Current(seq) {
		(_ s a i) = Break(Lazy seq)
		Current = Require(s Throw:Type-Error("Empty sequence"))
		Current = a(s)
	}

	Next(seq) {
		(l s a i) = Break(Lazy seq)
		Next = Require(l nil)
		Next = Cons(l - #1 i(s) a i)
	}

	Force(seq) {
		Algorithm:Map('_ seq)
	}

	Take(count seq) {
		Cons(
			Min(Length(seq) count)
			(count seq)
			(c s) => :First(s)
			(c s) => When(c > #1 (c - #1 :Rest(s)))
		)
	}

	Skip(count seq) {
		Algorithm:Iterate(count :Rest seq)
	}

	Concat(a b) {
		Nil?(a) : b
		Cons(
			Length(a) + Length(b)
			(a b)
			(a b) => :First(a)
			((a b) _) => Concat(:Rest(a) b))
	}

	Array-View(Xs) {
		Cons(
			Infinite-Length
			(0i Xs)
			(i xs) => Select(xs i)
			(i xs) => (i + #1 xs))
	}

	Array-Cycle(Xs) {
		Cons(
			Infinite-Length
			(0i Xs)
			(i xs) => Select-Wrap(xs i)
			(i xs) => (i + #1 xs))
	}

	Map(fn seq) {
		Cons(
			Length(seq)
			(fn seq)
			(f s) => f(:First(s))
			(f s) => (f :Rest(s)))
	}

	Accumulate(fn seed seq) {
		Cons(
			Length(seq)
			(fn seed seq) 
			(_ s _) => s
			(f sd sq) => (f f(sd :First(sq)) :Rest(sq)))
	}

	Zip(lists) {
		smap = Algorithm:Map
		Zip = Throw:Type-Error("Can't Zip " lists)
		len = Algorithm:Reduce(Min smap(Length lists))
		Zip = Cons(
			len 
			(len lists)
			(l ls) => smap(:First ls)
			(l ls) => When(l > #0 (l - #1 smap(:Rest ls))))
	}
}

Package Range {
	Count(start step) {
		Use Sequence
		Cons(
			Infinite-Length
			start '_ (+ step))
	}

	Geometric(start coef) {
		Use Sequence 
		Cons(
			Infinite-Length 
			start '_ (* coef))
	}
}

Package Format {
	Text(seq) {
		(l s a i) = Break(Sequence:Lazy seq)		
		When(Equal-Type(l Sequence:Infinite-Length) ("Infinite sequence from " s)
			 Otherwise Require(l Sequence:Force(seq)))
	}
}

Package Algorithm {
	Reduce(fn seq) {
		When(Equal-Type(Sequence:Length(seq) Sequence:Infinite-Length) 
				Throw:Type-Error("Reduction of an infinite sequence"))
	}

	Map(fn seq) {
		When(Equal-Type(Sequence:Length(seq) Sequence:Infinite-Length) 
				Throw:Type-Error("Algorithm:Map of an infinite sequence will not terminate. Use Sequence:Map!"))		
	}
}

Package Actions {
	For(seq body) {
		(l s a i) = Break(Sequence:Lazy seq)		
		When(Equal-Type(l Sequence:Infinite-Length) "Infinite sequence from " s
			 Otherwise For(Sequence:Force(seq) body))
	}
}

Add(a b) {
	When(
		Equal-Type(a Sequence:Infinite-Length)  a
		Equal-Type(b Sequence:Infinite-Length)  b
	)
}

Sub(a b) {
	When(
		Equal-Type(a Sequence:Infinite-Length) a)
}

Min(a b) {
	When(
		Equal-Type(a Sequence:Infinite-Length) b
		Equal-Type(b Sequence:Infinite-Length) a)
}

Package Fallback {
	First(seq) {
		Sequence:Current(seq)
	}

	Rest(seq) {
		Sequence:Next(seq)
	}
}