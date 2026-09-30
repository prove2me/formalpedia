-- Prove2me | solution 1 for NumberField.restrictScalars_eq_pow_inertiaDeg
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:17:12.678055+00:00
-- url     : https://prove2.me/submissions/c65996a9-a486-4fa6-b9c3-a60b433198c2

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Mathlib.Algebra.CharP.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Unramified.Locus

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Frobenius elements for a group acting on a ring extension

This file supplements Mathlib's `IsArithFrobAt` API with facts about a monoid or group acting on
a commutative ring extension `S/R`. All of them are stated at ring level, so they are available
independently of any number-field or Legendre-symbol specialization.

Two are properties of a single Frobenius element. The defining congruence has `#(R ⧸ Q ∩ R)` as
its exponent, so it makes that residue ring finite and therefore forces `Q ≠ ⊥` over an infinite
base. Iterating it `n` times replaces the exponent by its `n`-th power, which is what a Frobenius
over an intermediate ring of residue degree `n` is required to satisfy.

For an ideal `p` of `R`, an element `σ` of the acting group cuts out the set of primes of `S` above
`p` that admit `σ` as an arithmetic Frobenius. These sets need not be disjoint: at a ramified prime
several elements are a Frobenius at once, so this is a family of fibers rather than a partition.
Disjointness at a prime `Q` is what `IsArithFrobAt.eq_of_isUnramifiedAt` below supplies, under
hypotheses of its own: a faithful action, `S` Noetherian, `Q.primeCompl ≤ S⁰`, and
`Algebra.IsUnramifiedAt R Q`. Exhaustion of the primes above `p` needs a Frobenius to exist at
each of them, which again carries hypotheses of its own, such as those of
`IsArithFrobAt.exists_of_isInvariant`.

## Main results

* `IsArithFrobAt.eq_of_isUnramifiedAt` — a Frobenius element is unique for a faithful action at an
  unramified prime of a Noetherian ring whose prime complement consists of non-zero-divisors.
* `IsArithFrobAt.ne_bot` — a prime carrying a Frobenius element over an infinite base ring is
  nonzero.
* `IsArithFrobAt.mk_pow_smul` — the `n`-th power of a Frobenius element acts on the residue ring
  by the `q ^ n`-th power map.
* `Ideal.nonempty_frobenius_fiber_equiv_of_isConj` — conjugate elements have equipotent fibers
  above a fixed ideal of the base, as a bijection between them.
* `Ideal.frobenius_fiber_card_eq_of_isConj` — the `Nat.card` form of that equipotence.

The equipotence is the "distributed evenly" step of Chebotarev's density theorem: where the fibers
do partition the primes above `p`, it is what lets a count over a whole conjugacy class be
recovered from the count at a single representative. Because `S` is an arbitrary commutative ring
the fibers may be infinite, and `Nat.card` is `0` on an infinite type; the bijection is therefore
the primary statement and the `Nat.card` identity is derived from it.

## Implementation notes

The bijection realizing the equipotence is not conjugation itself but the pointwise action
`P ↦ c • P` of a witnessing element `c`; Mathlib's `IsArithFrobAt.conj` is what transports the
Frobenius condition along it, sending a Frobenius `σ` at `P` to the Frobenius `c * σ * c⁻¹` at
`c • P`.

The source states the equipotence for the rings of integers of a Galois extension of number
fields and under an unramifiedness hypothesis on `p` that it never uses. Both restrictions are
dropped here: the transport argument uses only the generic Frobenius group-action API, and it is
available at every prime.

## References

* Sharifi, *Algebraic Number Theory*, Theorem 7.2.2 (p. 143).
* Stevenhagen–Lenstra, *Chebotarëv and his density theorem*, Appendix.
* Birkbeck–Brasca, [chebotarev-density](https://github.com/CBirkbeck/chebotarev-density)
  (Apache-2.0), commit `8575c9df1ae0a61120ab5c964c7911414254bec7`, file
  `CebotarevDensity/FixedFieldDensity.lean`, declaration `frobeniusFibre_card_eq_of_isConj`
  (source line 54). The transport argument of `nonempty_frobenius_fiber_equiv_of_isConj` below,
  and the statement of the `frobenius_fiber_card_eq_of_isConj` derived from it, are adapted from
  that declaration; the source states only the `Nat.card` form.
-/

 section

open nonZeroDivisors

open scoped Pointwise

namespace Ideal



/-- **A prime carrying an arithmetic Frobenius over an infinite base is nonzero.** The defining
congruence has the cardinality of `R ⧸ Q ∩ R` as its exponent, so it forces that residue ring to
be finite; over an infinite `R` this rules out `Q = ⊥`. -/
theorem _root_.IsArithFrobAt.ne_bot {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [FaithfulSMul R S] [Infinite R] [Monoid G] [MulSemiringAction G S] [SMulCommClass G R S]
    {Q : Ideal S} {σ : G} (H : _root_.IsArithFrobAt R σ Q) : Q ≠ ⊥ := by
  rintro rfl
  have hfin : Finite (R ⧸ Ideal.under R (⊥ : Ideal S)) := H.finite_quotient
  rw [Ideal.under_bot] at hfin
  have : Finite R := Finite.of_equiv _ (RingEquiv.quotientBot R).toEquiv
  exact not_finite R

/-- **Powers of an arithmetic Frobenius raise the exponent.** If `σ` is an arithmetic Frobenius at
`Q`, then `σ ^ n` acts on the residue ring `S ⧸ Q` as the `q ^ n`-th power map, where
`q = #(R ⧸ Q ∩ R)`.

This is the congruence a tower formula rests on: over an intermediate ring whose prime below `Q`
has residue ring of cardinality `q ^ n`, the `n`-th power of a Frobenius over the base satisfies
the defining congruence of a Frobenius over that intermediate ring. -/
theorem _root_.IsArithFrobAt.mk_pow_smul {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Monoid G] [MulSemiringAction G S] [SMulCommClass G R S] {Q : Ideal S} {σ : G}
    (H : _root_.IsArithFrobAt R σ Q) (n : ℕ) (x : S) :
    Ideal.Quotient.mk Q ((σ ^ n) • x) =
      Ideal.Quotient.mk Q x ^ Nat.card (R ⧸ Q.under R) ^ n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hstep : Ideal.Quotient.mk Q (σ • x) =
        Ideal.Quotient.mk Q x ^ Nat.card (R ⧸ Q.under R) := H.mk_apply x
    rw [pow_succ, mul_smul, ih (σ • x), hstep, ← pow_mul]
    ring

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
  [MulSemiringAction G S] [SMulCommClass G R S]







end Ideal

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Ramification and inertia counting criteria

This file records Galois consequences of the fundamental identity for primes in finite
extensions of domains. First, in a Galois extension the number of primes above a prime ideal is
maximal exactly when the common ramification index and inertia degree are both `1`. Second, the
cardinality of the inertia subgroup of a prime `P` upstairs is the ramification index of `P`
itself over the base, rather than the `Ideal.ramificationIdxIn` of the prime below it.

The rest of the file is about how inertia subgroups vary with the prime. Translating a prime by
`σ` conjugates its inertia subgroup by `σ`, since `τ • x - x ∈ σ • P` says exactly
`(σ⁻¹ τ σ) • y - y ∈ P` after the substitution `x = σ • y`. Because the Galois group acts
transitively on the primes above a fixed prime of the base, a *commutative* Galois group therefore
has one inertia subgroup per prime of the base, not one per prime upstairs. That uniformity is
what lets a statement about ramification in an intermediate field be tested at a single prime
upstairs.

## Main results

* `TauCeti.RamificationInertia.ncard_primesOver_eq_natCard_iff_of_isGaloisGroup`:
  the domain/flat Galois counting criterion.
* `Ideal.card_inertia_eq_ramificationIdx`: the un-`In` form of the inertia count.
* `Ideal.mem_inertia_pointwise_smul_iff`: translation conjugates inertia subgroups.
* `Ideal.inertia_pointwise_smul`: for a commutative Galois group, translation leaves the inertia
  subgroup unchanged.
* `Ideal.inertia_eq_of_liesOver`: for a commutative Galois group, all the primes above a fixed
  prime of the base have the same inertia subgroup.
* `Ideal.isUnramifiedAt_pointwise_smul_iff`: unramifiedness is invariant under translation by
  an algebra automorphism.
* `Ideal.isUnramifiedAt_of_isUnramifiedAt_of_isGaloisGroup`: unramifiedness transfers between
  primes above the same base prime in a Galois extension.

## Provenance

Built directly on Mathlib's unramifiedness transport
(`AlgEquiv.isUnramifiedAt_of_eq_comap`), on its Galois fundamental identity
(`Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`), on its inertia count
(`Ideal.card_inertia_eq_ramificationIdxIn`), and on its transitivity statement
(`Ideal.exists_smul_eq_of_isGaloisGroup`).
-/

 section

open Ideal Module

namespace Ideal

open scoped Pointwise

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]





end Ideal

namespace Ideal

/-- The cardinality of the inertia subgroup of `P` is the ramification index of `P` over `R`.
This is `Ideal.card_inertia_eq_ramificationIdxIn` stated with the ramification index of `P`
itself rather than with `Ideal.ramificationIdxIn` of the ideal below it. -/
theorem card_inertia_eq_ramificationIdx (R : Type*) {S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsDomain R] [IsDomain S] [Module.Finite R S] [Module.Flat R S] (G : Type*)
    [Group G] [Finite G] [MulSemiringAction G S] [IsGaloisGroup G R S] (P : Ideal S) [P.IsPrime]
    [PerfectField (P.under R).ResidueField] :
    Nat.card (P.inertia G) = P.ramificationIdx R :=
  (card_inertia_eq_ramificationIdxIn (G := G) (P.under R) P).trans
    (ramificationIdxIn_eq_ramificationIdx (P.under R) P G)

end Ideal

namespace TauCeti.RamificationInertia



end TauCeti.RamificationInertia

namespace Ideal

section Inertia

open scoped Pointwise

variable {S : Type*} [CommRing S] {G : Type*} [Group G] [MulSemiringAction G S]



variable (σ : G) (P : Ideal S)



end Inertia

section InertiaOver

open scoped Pointwise

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : Ideal A) (P Q : Ideal B)
  [P.IsPrime] [P.LiesOver p] [Q.IsPrime] [Q.LiesOver p] (G : Type*) [Group G] [Finite G]
  [IsMulCommutative G] [MulSemiringAction G B] [IsGaloisGroup G A B]



end InertiaOver

end Ideal

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The Frobenius, the inertia subgroup, and the decomposition group

Let `L / K` be a finite Galois extension of number fields with Galois group `G = Gal(L/K)`, and
let `Q` be a nonzero prime of `𝓞 L` lying over `𝔭 = Q ∩ 𝓞 K`. Mathlib's `IsArithFrobAt`
expresses that an element `σ ∈ G` satisfies `σ x ≡ x ^ #(𝓞 K ⧸ 𝔭) (mod Q)`. Tau Ceti's
`NumberField.exists_isArithFrobAt` supplies such an element, and
`NumberField.isArithFrobAt_eq_of_isUnramifiedAt` proves it unique when `L / K` is unramified at
`Q`. This file identifies what that element is. In general, a Frobenius at `Q` together with the
inertia subgroup of `Q` generates the decomposition group of `Q`; at an unramified prime the
inertia subgroup is trivial, and the Frobenius alone generates the decomposition group, mapping
to the Frobenius automorphism of the residue extension.

The link is Mathlib's `Ideal.Quotient.stabilizerHom`, the action of the decomposition group
`MulAction.stabilizer G Q` on the residue extension `(𝓞 L ⧸ Q) / (𝓞 K ⧸ 𝔭)`. Its kernel is the
inertia subgroup, which is trivial exactly when `Q` is unramified, because the cardinality of the
inertia subgroup is the ramification index (`Ideal.card_inertia_eq_ramificationIdx`). So at an
unramified prime the decomposition group embeds in the residue Galois group, and a Frobenius
element is precisely a preimage of the residue Frobenius `x ↦ x ^ #(𝓞 K ⧸ 𝔭)`. Counting through
that embedding turns the classical facts about finite fields into facts about `G`:

* the order of a Frobenius element is the inertia degree `f(Q/𝔭)`;
* the decomposition group has cardinality `f(Q/𝔭)` as well, so the embedding is an isomorphism;
* consequently the decomposition group is `⟨σ⟩`, and it is cyclic.

The last section transports these statements along the action of `G` on the primes above `𝔭`.
Unramifiedness is invariant under that action, and the Frobenius at `τ • Q` is the conjugate
`τ σ τ⁻¹`: Mathlib's `IsArithFrobAt.conj` gives one inclusion and uniqueness at the unramified
prime `τ • Q` gives the other.

## Main results

* `Ideal.isUnramifiedAt_iff_inertia_eq_bot`: unramifiedness at `Q` is triviality of the
  inertia subgroup of `Q` in `Gal(L/K)`.
* `Ideal.stabilizerHom_eq_frobeniusAlgEquivOfAlgebraic`: a Frobenius element at `Q` acts on
  the residue field `𝓞 L ⧸ Q` as the residue Frobenius.
* `Ideal.orderOf_eq_inertiaDeg_of_isArithFrobAt`: a Frobenius element at an unramified `Q`
  has order the inertia degree of `Q` over `𝓞 K`.
* `Ideal.zpowers_eq_stabilizer_of_isArithFrobAt`: a Frobenius element at an unramified `Q`
  generates the decomposition group of `Q`.
* `Ideal.card_stabilizer_eq_inertiaDeg_of_isUnramifiedAt`: the decomposition group of an
  unramified `Q` has order the inertia degree of `Q` over `𝓞 K`.
* `Ideal.stabilizerEquivResidueAut`: the decomposition group of an unramified prime is
  isomorphic to the automorphism group of the residue extension.
* `Ideal.isCyclic_stabilizer_of_isUnramifiedAt`: the decomposition group of an unramified
  prime is cyclic.
* `Ideal.zpowers_sup_inertia_eq_stabilizer_of_isArithFrobAt`: at any nonzero prime `Q`, a
  Frobenius element together with the inertia subgroup generates the decomposition group.
* `Ideal.orbit_stabilizer_eq_orbit_zpowers_of_isArithFrobAt`: on a set where the inertia
  subgroup acts trivially, the orbits of the decomposition group are those of any Frobenius.
* `Ideal.isArithFrobAt_pointwise_smul_iff_eq_conj`: the Frobenius elements at `τ • Q` are
  exactly the conjugates `τ σ τ⁻¹` of the Frobenius elements `σ` at an unramified `Q`.

## Implementation notes

`FiniteField.frobeniusAlgEquivOfAlgebraic` is stated for a `Fintype` base field, so the residue
identification supplies that instance internally through `Fintype.ofFinite`. Residue rings are
made into fields by the local instance `Ideal.Quotient.field`, following Mathlib's own
ramification files.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9.
-/

 section

open _root_.Ideal _root_.Module

open scoped _root_.NumberField _root_.Pointwise

namespace Ideal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-! ### Unramifiedness and the inertia subgroup -/

/-- **Unramified means trivial inertia.** For a finite Galois extension `L / K` of number fields,
`L / K` is unramified at a prime `Q` of `𝓞 L` exactly when the inertia subgroup of `Q` in
`Gal(L/K)` is trivial.

This is the group-theoretic reading of `Ideal.card_inertia_eq_ramificationIdx`: the inertia
subgroup has as many elements as the ramification index of `Q` over `𝓞 K`. -/
theorem isUnramifiedAt_iff_inertia_eq_bot (Q : Ideal (𝓞 L)) [Q.IsPrime] :
    Algebra.IsUnramifiedAt (𝓞 K) Q ↔ Q.inertia (L ≃ₐ[K] L) = ⊥ := by
  rw [← Ideal.ramificationIdx_eq_one_iff (R := 𝓞 K) (q := Q),
    ← Ideal.card_inertia_eq_ramificationIdx (𝓞 K) (L ≃ₐ[K] L) Q]
  exact ⟨Subgroup.eq_bot_of_card_eq _, fun h ↦ by rw [h]; simp⟩

/-! ### The decomposition group at an unramified prime -/

/-- **The decomposition group of an unramified prime embeds in the residue Galois group.**
Mathlib's `Ideal.Quotient.stabilizerHom` has the inertia subgroup as its kernel, and that
subgroup is trivial at an unramified prime. -/
theorem stabilizerHom_injective_of_isUnramifiedAt (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Algebra.IsUnramifiedAt (𝓞 K) Q] :
    Function.Injective (Ideal.Quotient.stabilizerHom Q (Q.under (𝓞 K)) (L ≃ₐ[K] L)) := by
  rw [← MonoidHom.ker_eq_bot_iff, Ideal.Quotient.ker_stabilizerHom, eq_bot_iff]
  intro σ hσ
  have hσ' : (σ : L ≃ₐ[K] L) ∈ Q.inertia (L ≃ₐ[K] L) := Ideal.coe_mem_inertia.mpr hσ
  rw [(isUnramifiedAt_iff_inertia_eq_bot Q).mp ‹_›, Subgroup.mem_bot] at hσ'
  exact Subgroup.mem_bot.mpr (Subtype.ext hσ')







attribute [local instance] Ideal.Quotient.field











/-! ### The decomposition group at a possibly ramified prime -/







/-! ### Conjugation along the fibre -/



end Ideal

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Raising the base field: the tower formula for arithmetic Frobenius elements

Let `K ⊆ M ⊆ L` be number fields with `L / K` and `L / M` Galois, let `Q` be a prime of `𝓞 L`
unramified over `𝓞 K`, and write `𝔓 = Q ∩ 𝓞 M` and `𝔭 = Q ∩ 𝓞 K`. An arithmetic Frobenius
`σ ∈ Gal(L/K)` at `Q` acts on the residue field by `x ↦ x ^ 𝔑𝔭`, while an arithmetic Frobenius
`τ ∈ Gal(L/M)` at `Q` acts by `x ↦ x ^ 𝔑𝔓`. Since `𝔑𝔓 = 𝔑𝔭 ^ f(𝔓/𝔭)`, the two are related by

```text
AlgEquiv.restrictScalars K τ = σ ^ f(𝔓/𝔭).
```

The exponent is a **power**, the residue degree of the intermediate prime over the base, and never
an inverse. In particular `σ ^ f(𝔓/𝔭)` fixes `M` pointwise even though `M / K` need not be normal
and `σ` itself need not preserve `M`.

This is the second of the two tower laws for Frobenius elements. The first, restriction along a
normal subextension, takes no power at all and is
`IsArithFrobAt.restrictNormal` in `TauCeti.NumberTheory.NumberField.Frobenius.Restriction`.

## The two hypotheses that are not decoration

The statement is *relative to one prime `Q` of `L`*. Replacing `σ` by an arbitrary conjugate — an
arbitrary representative of the Artin class of `𝔭` — makes it false when `M / K` is not normal: a
conjugate need not stabilize `Q`, so its `f`-th power need not fix `M` pointwise, and it is then
the restriction of no element of `Gal(L/M)` at all.

Unramifiedness of `Q` over `𝓞 K` is likewise essential. At a ramified prime a Frobenius lift is
determined only modulo inertia, so there is no equality of automorphisms to prove; the statement
would have to be made in the quotient by the inertia subgroup, or about a coset. Here
unramifiedness enters through `Ideal.stabilizerHom_injective_of_isUnramifiedAt`: the decomposition
group of `Q` embeds into the automorphism group of the residue extension, so an element of
`Gal(L/K)` stabilizing `Q` is pinned down by its residue action, and both `σ ^ f(𝔓/𝔭)` and
`AlgEquiv.restrictScalars K τ` act by `x ↦ x ^ 𝔑𝔓`.

## Main results

* `NumberField.restrictScalars_eq_pow_inertiaDeg`: an arithmetic Frobenius of `Gal(L/M)` at `Q`
  restricts to the `f(𝔓/𝔭)`-th power of an arithmetic Frobenius of `Gal(L/K)` at `Q`.
* `NumberField.isArithFrobAt_iff_restrictScalars_eq_pow_inertiaDeg`: that power characterizes the
  relative Frobenius among the elements of `Gal(L/M)` after restriction to `Gal(L/K)`.
* `NumberField.restrictScalars_arithFrobAt_eq_pow_inertiaDeg`: the same formula for Mathlib's
  coherently chosen `arithFrobAt`, which is what the Artin symbol is built from.
* `NumberField.exists_isArithFrobAt_pow_inertiaDeg`: the existence form of the tower formula,
  stated for prime ideals `𝔓` and `𝔭` presented by their defining equations.
* `NumberField.pow_inertiaDeg_apply_algebraMap`: the `f(𝔓/𝔭)`-th power of `σ` fixes `M`
  pointwise.
* `NumberField.restrictScalars_eq_of_inertiaDeg_eq_one`: at residue degree one the restriction
  of the relative Frobenius is `σ` itself, with no power.
* `NumberField.isArithFrobAt_restrictScalars_of_inertiaDeg_eq_one`: the same at residue degree
  one, concluding that the restriction is an arithmetic Frobenius rather than assuming one.
* `NumberField.isArithFrobAt_int_of_absNorm_eq`: a relative Frobenius above an ideal of absolute
  norm `p` is also a Frobenius over the ideal `(p)` of `ℤ`.
* `NumberField.isArithFrobAt_one_of_pow_eq_one` and
  `NumberField.isArithFrobAt_eq_one_of_pow_eq_one`: when an absolute Frobenius at `Q` has order
  dividing `n` and the residue field of `Q ∩ 𝓞 M` has `p ^ n` elements, the relative Frobenius
  of `Gal(L/M)` at `Q` is the identity.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9.
-/

 section

open Ideal

open scoped NumberField Pointwise

namespace NumberField
end NumberField
section NumberField
open NumberField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] {M : Type*} [Field M] [NumberField M] [Algebra K M] [Algebra M L]
  [IsScalarTower K M L] {Q : Ideal (𝓞 L)} [Q.IsPrime]



/-- **Raising the base field raises the Frobenius to the residue degree.** For number fields
`K ⊆ M ⊆ L` with `L / K` and `L / M` Galois and `Q` a prime of `𝓞 L` unramified over `𝓞 K`, the
restriction to `Gal(L/K)` of an arithmetic Frobenius `τ ∈ Gal(L/M)` at `Q` is the
`f(𝔓/𝔭)`-th power of an arithmetic Frobenius `σ ∈ Gal(L/K)` at `Q`, where
`𝔓 = Q ∩ 𝓞 M` and `𝔭 = Q ∩ 𝓞 K`.

The exponent is the residue degree of `𝔓` over `𝓞 K`, and it is a power: the residue field of `𝔓`
has `𝔑𝔭 ^ f(𝔓/𝔭)` elements, so the two Frobenius elements have residue actions `x ↦ x ^ 𝔑𝔭` and
`x ↦ x ^ 𝔑𝔭 ^ f(𝔓/𝔭)`. Both sides are read inside `Gal(L/K)`, where `τ` is placed by
`AlgEquiv.restrictScalars`. -/
theorem solution [_root_.Algebra.IsUnramifiedAt (𝓞 K) Q]
    {σ : L ≃ₐ[K] L} (hσ : _root_.IsArithFrobAt (𝓞 K) σ Q)
    {τ : L ≃ₐ[M] L} (hτ : _root_.IsArithFrobAt (𝓞 M) τ Q) :
    _root_.AlgEquiv.restrictScalars K τ = σ ^ (Q.under (𝓞 M)).inertiaDeg (𝓞 K) := by
  have _ : Q.IsMaximal := _root_.Ring.DimensionLEOne.maximalOfPrime hσ.ne_bot _root_.inferInstance
  have _ : (Q.under (𝓞 M)).IsMaximal := _root_.Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
  have _ : (Q.under (𝓞 K)).IsMaximal := _root_.Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
  have _ : (Q.under (𝓞 M)).LiesOver (Q.under (𝓞 K)) := ⟨by rw [_root_.Ideal.under_under]⟩
  -- The residue field of `𝔓` has `𝔑𝔭 ^ f(𝔓/𝔭)` elements.
  have hcard : _root_.Nat.card (𝓞 M ⧸ Q.under (𝓞 M)) =
      _root_.Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) ^ (Q.under (𝓞 M)).inertiaDeg (𝓞 K) := by
    have := _root_.Ideal.cardQuot_pow_inertiaDeg (R := 𝓞 K) (S := 𝓞 M)
      (Q.under (𝓞 K)) (Q.under (𝓞 M))
    simpa [_root_.Submodule.cardQuot_apply] using this.symm
  have hrestrict (x : 𝓞 L) : (_root_.AlgEquiv.restrictScalars K τ) • x = τ • x := by
    -- No public lemma states this for the induced actions on `𝓞 L`; it is definitional because
    -- `AlgEquiv.restrictScalars` preserves the underlying ring equivalence.
    rfl
  have hrestrictQ : (_root_.AlgEquiv.restrictScalars K τ) • Q = τ • Q := by
    rw [_root_.Ideal.pointwise_smul_def, _root_.Ideal.pointwise_smul_def]
    apply _root_.congrArg fun f ↦ Q.map f
    ext x
    exact _root_.congrArg (_root_.Algebra.algebraMap (𝓞 L) L) (hrestrict x)
  have hcong (x : 𝓞 L) :
      (_root_.AlgEquiv.restrictScalars K τ) • x -
        (σ ^ (Q.under (𝓞 M)).inertiaDeg (𝓞 K)) • x ∈ Q := by
    have hres : _root_.Ideal.Quotient.mk Q (τ • x) =
        _root_.Ideal.Quotient.mk Q x ^ _root_.Nat.card (𝓞 M ⧸ Q.under (𝓞 M)) := hτ.mk_apply x
    rw [← _root_.Ideal.Quotient.eq, hrestrict, hσ.mk_pow_smul, hres, hcard]
  have key : _root_.Ideal.Quotient.stabilizerHom Q (Q.under (𝓞 K)) (L ≃ₐ[K] L)
      ⟨_root_.AlgEquiv.restrictScalars K τ, by
        rw [_root_.MulAction.mem_stabilizer_iff, hrestrictQ]
        exact MulAction.mem_stabilizer_iff.mp hτ.mem_stabilizer⟩ =
      _root_.Ideal.Quotient.stabilizerHom Q (Q.under (𝓞 K)) (L ≃ₐ[K] L)
        ⟨σ ^ (Q.under (𝓞 M)).inertiaDeg (𝓞 K), _root_.pow_mem hσ.mem_stabilizer _⟩ := by
    ext x
    obtain ⟨x, rfl⟩ := _root_.Ideal.Quotient.mk_surjective x
    simpa [_root_.MulAction.subgroup_smul_def, _root_.Ideal.Quotient.eq] using hcong x
  exact _root_.congrArg _root_.Subtype.val (_root_.Ideal.stabilizerHom_injective_of_isUnramifiedAt Q key)













/-! ### Trivial relative Frobenius elements

A prime that is already inert enough over `ℚ` has trivial relative Frobenius: if the absolute
Frobenius `ρ` at `Q` has `ρ ^ n = 1` and the residue field of `Q ∩ 𝓞 M` has `p ^ n` elements, then
the residue action of the relative Frobenius, raising to the power `p ^ n`, is the identity.
-/





end NumberField

end
end
