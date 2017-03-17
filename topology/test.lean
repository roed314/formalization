/-
Copyright (c) 2017, Thomas C. Hales. All rights reserved.

Experiments with definitions in Lean.
-/

/-
XX general questions
What is the difference between Type and Sort?
We could use a "synonym" variant of definition.

XX how do I make or destruct a new type?
definition new_int : Type := int

XX unknown how to make abbreviation, gives errors.

Is "def" the same as definition?

XX construct an inverse function, using choice

XX wish list: declare types interoperable,

XX open is keyword, cannot be used with topology.
-/

----- Sets

namespace set

variables {α β : Type}

definition unions (s : set (set α)) : set α :=
{ a | ∃ u, a ∈ u ∧ u ∈ s }

definition inters (s : set (set α)) : set α :=
{ a | ∀ u, u ∈ s → a ∈ u }

definition disjoint (a b : set α) : Prop := (a ∩ b = ∅)

-- set.image
-- definition image (f : α → β) : set β :=
-- { b | ∃ a, f a = b }

definition preimage (f : α → β) (B : set β): set α :=
{ x | f x ∈  B }

-- set.compl
-- definition complement (A : set α) : set α :=
-- { x | ¬ x ∈ A }

definition univ (α : Type) : set α :=
{ x : α | true}

definition cover (S : set (set α)) : Prop :=
unions S = univ α 

definition subcover (T S : set (set α)) : Prop :=
cover T ∧ cover S ∧ T ⊆ S 

definition refinement (T S : set (set α)) : Prop :=
cover T ∧ cover S ∧ (∀ t, ∃ s, t ∈ T → s ∈ S ∧ t ⊆ s)

definition symmetric_difference (t s  : set α) : set α :=
set.union (set.diff s t) (set.diff t s)

definition increasing_nat (a : ℕ → ℕ) : Prop :=
(∀ i j, i < j → a i < a j)

definition subsequence (a b : ℕ → α) : Prop := 
(∃ k, increasing_nat k ∧ a = b ∘ k)

-- XX no HOL-Light style set notation.
-- { (a,b) | phi(a,b) }
-- { X | y | z }

definition graph (f : α → β) : set (α × β) :=
{z | ∃ a b, b = f a ∧ z = (a,b)}

definition id (x : α) : α :=
x

definition involution (f : α → α) : Prop :=
(f ∘ f = id)

definition fixed_point (f : α → α) (a : α) : Prop :=
(f a = a)

definition idempotent (f : α → α) : Prop :=
(f ∘ f = f)

definition permutation (f : α → α) : Prop :=
function.bijective f 

-- XX doesn't work
-- definition iterate  : (α → α) → ℕ → α → α 
-- | iterate f 0 x := x
-- | iterate f (succ n) x := f  ((iterate f n) x)

-- function.injective
-- definition injective (f : α → β) : Prop :=
-- (∀ x y, f x = f y → x = y)

-- function.surjective 
-- definition onto (f : α → β) : Prop :=
-- (∀ b : β, ∃ a : α, f a = b)

-- function bijective
-- definition bijective (f : α → β) : Prop :=
-- function.injective f ∧ function.surjective f

-- cardinalities

definition countably_infinite (α : Type) : Prop :=
(∃ f : ℕ → α, function.bijective f)

definition infinite (α : Type) : Prop :=
(∀ f : α → α, function.injective f → function.bijective f)

definition finite (α : Type) : Prop :=
(¬ (infinite α ))

definition cofinite (S : set α) : Prop :=
finite (subtype { x | ¬ (x∈ S)})

-- XX would like to define straight cardinal
-- This is the HOL-Light style definition HAS_CARD

definition has_cardinality (α : Type) (n : nat) :=
(∃ f : ((subtype {m | m < n}) → α), function.bijective f)

definition countable (α : Type) : Prop :=
finite α ∨ countably_infinite α

-- synonym
definition denumerable (α : Type) : Prop :=
countable α

definition equipollent (α β : Type) : Prop :=
(∃ f : α → β, function.bijective f)

definition smaller_cardinal_than (α β : Type) : Prop :=
(¬ equipollent α β ∧ ∃ f : α → β, function.injective f)


-- from logic.lean:

-- reflexive, symmetric, transitive, equivalence, total,
-- mk_equivalence, irreflexive, anti_symmetric, empty_relation, subrelation,
-- inv_image

-- synonym total-order, chain, linear_order, chain_order

def universal_relation := λ a b : α, true

-- synonym inv_image = restriction, trace

--- XX how to deal with terminology:
--- ≼ : precedes, smaller than, littler than, is less than, is earlier than
--- ≺ : strictly precedes, etc.
--- ≻ strictly succeeds etc. 

variables {γ : Type}
variables (r : γ → γ → Prop)

definition preorder :=
reflexive r ∧ transitive r

definition total_preorder :=
preorder r ∧ total r

definition directed_order :=
(∀ x1 x2, ∃ y, r x1 y ∧ r x2 y)

-- synonym directed_order directed set

definition comparable x y :=
(r x y ∨ r y x)

definition poset :=
(reflexive r) ∧ (transitive r) ∧ (anti_symmetric r)

-- synonym poset = partially_ordered_set
-- Here the set is the type, no need to distinguish
-- between the set and relation

definition order_interval (r : subtype poset) (a b : β)  :=
{ x  | r^.elt_of a x ∧ r^.elt_of x b }

definition order_bounded (r : subtype poset) X  :=
(∃ a b : β, X ⊆ order_interval r a b)

definition lower_set (r : subtype poset) (S : set γ) :=
(∀ x s, r^.elt_of x s ∧ s ∈ S → x ∈ S)

-- synonym lower_set = initial_segment = order_ideal

definition proper_lower_set (r : subtype poset) (S : set γ) :=
lower_set r S ∧ (S ≠ univ γ)

definition set_of_predecessors (r : subtype poset) (w : γ) :=
{ x | r^.elt_of x w ∧ x ≠ w }

-- synonym pre {r} x = set_of_predecessors 

definition principal_lower_set (r : subtype poset) (w : γ) :=
{ x | r^.elt_of x w }

definition increasing (r : subtype (@poset β)) (s : subtype (@poset γ)) (p : β → γ) :=
(∀ x y, r^.elt_of x y → s^.elt_of (p x) (p y))

definition decreasing (r : subtype (@poset β)) (s : subtype (@poset γ)) (p : β → γ) :=
(∀ x y, r^.elt_of x y → s^.elt_of (p y) (p x))

definition monotone 
increasing r s p ∨ decreasing r s p

definition order_isomorphism (r : subtype (@poset β)) (s : subtype (@poset γ)) (p : β → γ) :=
(function.bijective p ∧ (∀ x y, r^.elt_of x y ↔ s^.elt_of (p x) (p y)))

definition upper_bound (r : subtype (@poset β)) (S : set β) z :=
(∀ s ∈ S, r^.elt_of s z)

definition bounded_above (r : subtype (@poset β)) (S : set β) :=
(∃ z, upper_bound r S z)

definition lower_bound (r : subtype (@poset β)) (S : set β) z :=
(∀ s ∈ S, r^.elt_of z s)

definition bounded_below (r : subtype (@poset β)) (S : set β) : Prop :=
(∃ z, lower_bound r S z)

-- synonym maximum, greatest element, largest, biggest, highest, last, max
definition maximum (r: subtype (@poset β)) (S : set β) (z : β) : Prop :=
(z ∈ S ∧ upper_bound r S z)

-- synonym least, smallest, littlest, lowest, first element, min
definition minimum (r: subtype (@poset β)) (S : set β) (z : β) : Prop :=
(z ∈ S ∧ lower_bound r S z)

-- synonym least upper bound, supremum, sup, join of S
definition least_upper_bound (r : subtype (@poset β)) (S : set β) (z : β) : Prop :=
bounded_above r S ∧  minimum r { x | upper_bound r S x } z

-- synonym greatest_lower_bound, infimum, inf, meet of S
definition greatest_lower_bound (r : subtype (@poset β)) (S : set β) (z : β) : Prop :=
bounded_below r S ∧  maximum r { x | upper_bound r S x } z

definition maximal (r : subtype (@poset β)) (S : set β) (z : β) : Prop :=
(z ∈ S ∧ ∀ s, r^.elt_of z s → z = s)

definition minimal (r : subtype (@poset β)) (S : set β) (z : β) : Prop :=
(z ∈ S ∧ ∀ s, r^.elt_of s z → z = s)

-- synonym woset, well-ordered set
definition well_ordering (r : subtype (@poset β)) :=
(∀ S : set β, S ≠ ∅ → ∃ s : β, minimum r S s)

-- definition lexicographical_order (Λ : subtype (@poset β)) (S : β → subtype (@poset γ)) : (subtype (@poset (β → γ))) :=

definition moore_collection (C : set (set β)) : Prop :=
(univ β ∈ C) ∧ (∀ D, D ⊆ C → inters D ∈ C)

definition dedekind_complete_poset (r : subtype (@poset β)) : Prop :=
 ∀ S, bounded_above r S ∧ S ≠ ∅ → ∃ z, least_upper_bound r S z

-- XX give meet and join notation for a lattice
definition lattice (r : subtype (@poset β)) : Prop :=
(∀ x y : β, ∃ z, least_upper_bound r { x, y } z) ∧
(∀ x y : β, ∃ z, greatest_lower_bound r { x, y } z)

-- synonym order_complete, complete_lattice, complete

definition complete (r : subtype (@poset β)) : Prop :=
(∀ S : set β, ∃ z1 z2, least_upper_bound r S z1 ∧ greatest_lower_bound r S z2)







check order_interval

check inv_image
check reflexive
check preorder

end set


/- 
  reals
-/

namespace real

variable { α : Type }

definition denom : Type := subtype { d : int | ¬ (d = 0) }

constant dest_denom (r : denom) : int

structure ipair : Type :=
(n : int)
(d : denom)

-- r1^.n .... ipair.n r1

definition rat_equiv (r1 r2 : ipair ) : Prop :=
  r1^.n * dest_denom (r2^.d) = r2^.n * dest_denom (r1^.d)

check rat_equiv

constant isequiv : equivalence rat_equiv

definition setd : setoid ipair := 
setoid.mk rat_equiv isequiv

definition rat : Type := quotient setd

constant rat_le (r1 r2 : rat) : Prop

-- XX can I use beta-reduced form of p 1 here, for coercion?

constant one_ne_zero : (¬ 1 = 0)


-- construct reals 

constant real : Type

constant real_zero : real

constant real_one : real

constant real_le : real → real → Prop

constant real_lt : real → real → Prop

constant real_add : real → real → real

constant real_abs : real → real

constant real_max : real → real → real

definition nonempty {α : Type} (S : set α) : Prop :=
(S ≠ ∅)

-- XX also need bounded below, or - infinity
constant real_inf : (subtype (@nonempty real)) → real

-- XX also need bounded above, or + infinity
constant real_sup : (subtype (@nonempty real)) → real

-- XX what do the angle brackets mean here?

instance : has_le real := ⟨real_le⟩

instance : has_lt real := ⟨real_lt⟩

instance : has_zero real := ⟨real_zero⟩

instance : has_one real := ⟨real_one⟩

instance : has_add real := ⟨real_add⟩

end real



namespace analysis

open classical real

variables { α β : Type }

definition quasi_pseudo_metric (d: α → α → real) : Prop :=
(∀ x y, d x y ≥ 0) ∧
(∀ x, d x x = 0) ∧
(∀ x y z, d x y ≤ d x z + d z y)

definition pseudo_metric (d : α → α → real) : Prop :=
(quasi_pseudo_metric d) ∧
(∀ x y, d x y = d y x)

definition metric  (d : α → α → real) : Prop :=
(pseudo_metric d) ∧
(∀ x y, (x = y) ↔ d x y = 0)

-- use subtype (metric) instead
-- structure metric_space { α : Type } :=
-- (d : α → α → real)
-- (m : metric d)

-- check subtype
-- print fields subtype

definition isometry (f : α → β)  (da db : subtype (pseudo_metric)) : Prop :=
(∀ x y, db^.elt_of (f x) (f y) = da^.elt_of x y)

-- XX would like to coerce out the ^.elt_of

definition isolated_point (da : subtype metric) (x : α) : Prop :=
(∃ r, r > 0 ∧ ∀ y, da^.elt_of x y < r → x = y)

-- XX using classical logic, Lean should know that (x=y) is decidable.

definition kronecker_metric (α : Type) : α → α → real :=
(λ x y, if (x=y) then 1 else 0)

-- XX abbrev not found.
-- abbreviation discrete_metric := kronecke_metric

definition ultrametric (d : α → α → real) : Prop :=
(metric d) ∧
(∀ x y z, d x y ≤ real_max (d x z) (d z y))

-- any collection of pseudo_metrics is a gauge

definition gauge (D : set (subtype (@pseudo_metric α))) : Prop :=
true

check λ d, subtype.elt_of d
check λ (x : α) y (d: subtype metric), (d^.elt_of x y < 0)
check λ (x : α) (y : α) d D, (subtype.elt_of d x y > 0) ∧ (d ∈ (D : set (subtype (@metric α))))

-- XX not clear why d^.elt_of x y is rejected:

definition separating_gauge (D : set (subtype (@pseudo_metric α))) : Prop :=
(∀ (x : α) (y : α), (x ≠ y) → ∃ d ∈ D, d^.elt_of x y > 0)

-- XX what does this mean. nonempty is in logic.lean? 
-- Here S is proof of the prop nonempty real.
check (λ S : nonempty real, S)
---- XX
check real_inf

-- would like to write 
-- definition distance_to_set (d: property (@pseudo_metric α)) (x : α) (S : property (@real.nonempty α)) : real :=
-- real_inf { d x s | s ∈ S }
-- definition diameter (d: property (@pseudo_metric α)) (S : property (@real.nonempty α)) : real :=
-- real_sup { d x y | x ∈ S ∧ y ∈ S }
-- XX do we need bounded as part of def of diameter?, or allow + infinity?

definition distance_to_set (d: subtype (@pseudo_metric α)) (x : α) (S : subtype (@real.nonempty α)) : real :=
real_inf (set.image (λ s,  d^.elt_of x s^.elt_of))

-----


-- check set
-- check subtype
-- print prefix set



end analysis


--- Topology definitions from HOL-Light



namespace topology

  open classical
  open set -- lean/library/data/set/basic.lean lean/library/init/data/set.lean

  variable {A : Type}

  -- definition (L:(A->Prop)->Prop) is a topology if
  -- (1) the empty set $∅$ is an element of $L$,
  -- (2) If $s$ and $t$ are elements of $L$, then the intersection of $s$ and $t$ is an element of $L$, and
  -- (3) If $k$ is a subset of $L$, then the unions of $k$ is an element of $L$.

structure topological_space : Type :=
(opens : set(set A))
(empty : ∅ ∈ opens)
(inter : ∀ s t, s ∈ opens ∧ t ∈ opens → s ∩ t ∈ opens)
(unions : ∀ k, k ⊆ opens → unions k ∈ opens)

-- instance : has_mem A (topological_space A)

--  definition is_topology (L: (A->Prop)->Prop) : Prop :=
--    ∅ ∈ L ∧ 
--    (∀ s t, s ∈ L ∧ t ∈ L → (s ∩ t) ∈ L) ∧ 
--    (∀ k, k ⊂ L →  

end topology

print fields topology.space
print classes
print has_mem
print instances has_mem
