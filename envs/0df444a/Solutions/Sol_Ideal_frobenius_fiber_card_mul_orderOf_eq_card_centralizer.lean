-- Prove2me | solution 1 for Ideal.frobenius_fiber_card_mul_orderOf_eq_card_centralizer
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:22:40.505123+00:00
-- url     : https://prove2.me/submissions/1f2a6f1c-ff13-4790-b726-4d80e4eb84e6

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
import Theorems.Thm_Ideal_frobenius_fiber_eq_orbit_centralizer

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

omit [IsGalois K L] in
/-- **A Frobenius element induces the residue Frobenius.** The action of an arithmetic Frobenius
`σ` at `Q` on the residue field `𝓞 L ⧸ Q` is the `#(𝓞 K ⧸ 𝔭)`-power map, that is
`FiniteField.frobeniusAlgEquivOfAlgebraic` of the residue extension.

This is the defining congruence `σ x ≡ x ^ #(𝓞 K ⧸ 𝔭) (mod Q)` read as an equality of
automorphisms of `𝓞 L ⧸ Q`; no unramifiedness is needed. -/
theorem stabilizerHom_eq_frobeniusAlgEquivOfAlgebraic (Q : Ideal (𝓞 L)) [Q.IsPrime]
    (hQ : Q ≠ ⊥) {σ : L ≃ₐ[K] L} (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    let _ : Q.IsMaximal := (inferInstance : Q.IsPrime).isMaximal hQ
    letI := Fintype.ofFinite (𝓞 K ⧸ Q.under (𝓞 K))
    Ideal.Quotient.stabilizerHom Q (Q.under (𝓞 K)) (L ≃ₐ[K] L) ⟨σ, hσ.mem_stabilizer⟩ =
      FiniteField.frobeniusAlgEquivOfAlgebraic (𝓞 K ⧸ Q.under (𝓞 K)) (𝓞 L ⧸ Q) := by
  let _ : Q.IsMaximal := (inferInstance : Q.IsPrime).isMaximal hQ
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.stabilizerHom_apply, FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
    ← @Nat.card_eq_fintype_card _ (Fintype.ofFinite _)]
  simpa [MulAction.subgroup_smul_def, MulSemiringAction.toAlgHom_apply] using hσ.mk_apply x

/-- **The order of a Frobenius element is the inertia degree.** For `Q` unramified over `𝓞 K`, an
arithmetic Frobenius `σ` at `Q` has `orderOf σ = f(Q / 𝔭)`.

The decomposition group injects into the residue Galois group, where the image of `σ` is the
residue Frobenius; that automorphism has order the degree of the residue extension, which is the
inertia degree. -/
theorem orderOf_eq_inertiaDeg_of_isArithFrobAt (Q : Ideal (𝓞 L)) [Q.IsPrime]
    (hQ : Q ≠ ⊥) [Algebra.IsUnramifiedAt (𝓞 K) Q] {σ : L ≃ₐ[K] L}
    (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    orderOf σ = Q.inertiaDeg (𝓞 K) := by
  let _ : Q.IsMaximal := (inferInstance : Q.IsPrime).isMaximal hQ
  have : Fintype (𝓞 K ⧸ Q.under (𝓞 K)) := Fintype.ofFinite _
  have key : orderOf (⟨σ, hσ.mem_stabilizer⟩ : MulAction.stabilizer (L ≃ₐ[K] L) Q) =
      Q.inertiaDeg (𝓞 K) := by
    rw [← orderOf_injective _ (stabilizerHom_injective_of_isUnramifiedAt Q),
      stabilizerHom_eq_frobeniusAlgEquivOfAlgebraic Q hQ hσ,
      FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
      Ideal.inertiaDeg_eq_of_isMaximal (Q.under (𝓞 K)) Q]
  exact (Subgroup.orderOf_coe (⟨σ, hσ.mem_stabilizer⟩ :
    MulAction.stabilizer (L ≃ₐ[K] L) Q)).trans key

/-- **The decomposition group of an unramified prime has order the inertia degree.** -/
theorem card_stabilizer_eq_inertiaDeg_of_isUnramifiedAt (Q : Ideal (𝓞 L))
    [Q.IsPrime] (hQ : Q ≠ ⊥) [Algebra.IsUnramifiedAt (𝓞 K) Q] :
    Nat.card (MulAction.stabilizer (L ≃ₐ[K] L) Q) = Q.inertiaDeg (𝓞 K) := by
  let _ : Q.IsMaximal := (inferInstance : Q.IsPrime).isMaximal hQ
  rw [Ideal.card_stabilizer_eq_card_inertia_mul_finrank (Q.under (𝓞 K)) Q,
    (isUnramifiedAt_iff_inertia_eq_bot Q).mp ‹_›]
  simp

/-- **A Frobenius element generates the decomposition group.** At an unramified prime `Q` the
cyclic subgroup generated by an arithmetic Frobenius at `Q` is the whole decomposition group,
both having `f(Q / 𝔭)` elements. -/
theorem zpowers_eq_stabilizer_of_isArithFrobAt (Q : Ideal (𝓞 L)) [Q.IsPrime]
    (hQ : Q ≠ ⊥) [Algebra.IsUnramifiedAt (𝓞 K) Q] {σ : L ≃ₐ[K] L}
    (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    Subgroup.zpowers σ = MulAction.stabilizer (L ≃ₐ[K] L) Q := by
  have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (L ≃ₐ[K] L) Q :=
    Subgroup.zpowers_le.mpr hσ.mem_stabilizer
  refine le_antisymm hle ?_
  rw [← Subgroup.subgroupOf_eq_top]
  apply Subgroup.eq_top_of_card_eq
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers,
    orderOf_eq_inertiaDeg_of_isArithFrobAt Q hQ hσ,
    card_stabilizer_eq_inertiaDeg_of_isUnramifiedAt Q hQ]



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
# How many primes carry a given Frobenius element

Let `L / K` be a finite Galois extension of number fields, `𝔭` an ideal of `𝓞 K` and `σ` an
element of `Gal(L/K)`. The primes of `𝓞 L` above `𝔭` at which `σ` is an arithmetic Frobenius form
the *fiber* of `σ`, and `Ideal.frobenius_fiber_card_eq_of_isConj` shows that conjugate elements
have fibers of the same size. This file computes that size, at a prime where `σ` is a Frobenius
and `L / K` is unramified:

```text
#(fiber of σ) * orderOf σ = #Centralizer_{Gal(L/K)}(σ)
```

The reason is that the fiber is a single orbit. `Gal(L/K)` acts transitively on the primes above
`𝔭`, and the Frobenius at `τ • Q` is `τ σ τ⁻¹`, so the elements carrying `Q` to another member of
the fiber are exactly those commuting with `σ`. The stabilizer of `Q` inside that centralizer is
the decomposition group `⟨σ⟩`, whose order is `orderOf σ`, and the orbit-stabilizer theorem gives
the count.

The identity is stated as a product rather than as `#Centralizer(σ) / orderOf σ` so that it says
something without a separate divisibility: `orderOf σ` divides the centralizer's order because
`⟨σ⟩` is a subgroup of it, and `ConjClasses.card_carrier_mul_orderOf_dvd` records the companion
divisibility for a whole conjugacy class.

## Main results

* `Ideal.frobenius_fiber_eq_orbit_centralizer`: the fiber of `σ` above `𝔭` is the orbit of any of
  its members under the centralizer of `σ`.
* `Ideal.frobenius_fiber_card_mul_orderOf_eq_card_centralizer`: its size, times `orderOf σ`, is
  the order of that centralizer.
* `HeightOneSpectrum.frobeniusFiberEquiv`: the height-one-prime and ideal representations of the
  fiber are equivalent.

## References

* Sharifi, *Algebraic Number Theory*, Theorem 7.2.2 (p. 143).
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9.
-/

 section

open scoped NumberField Pointwise
open IsDedekindDomain (HeightOneSpectrum)

namespace Ideal
end Ideal
section Ideal
open Ideal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]

-- Source. The count is specified by the Chebotarev roadmap:
-- `TauCetiRoadmap/Chebotarev/README.md` §8.2, which displays the fibre size as
-- `#G / (#C * f) = #Centralizer_G(σ) / f` with `f = orderOf σ`. The theorems below count the
-- primes of `𝓞 L`; the roadmap's own statement counts primes of the fixed field `L ^ ⟨σ⟩`, and
-- reaches this one through the residue degree of a fixed-field prime.



/-- **The size of a Frobenius fiber.** At an unramified prime `Q` above an ideal `𝔭` with
arithmetic Frobenius `σ`, the number of primes above `𝔭` admitting `σ` as a Frobenius, times the
order of `σ`, is the order of the centralizer of `σ` in `Gal(L/K)`.

This is the orbit-stabilizer theorem applied to `frobenius_fiber_eq_orbit_centralizer`: the
stabilizer of `Q` in the centralizer is the decomposition group `⟨σ⟩`, of order `orderOf σ`.

Compare `Ideal.frobenius_fiber_card_eq_of_isConj`, which says fibers of conjugate elements have
equal size without saying what that size is. -/
theorem solution (𝔭 : _root_.Ideal (𝓞 K))
    {σ : L ≃ₐ[K] L} (Q : _root_.Ideal (𝓞 L)) [_root_.IsGalois K L] [Q.IsPrime] [Q.LiesOver 𝔭]
    [_root_.Algebra.IsUnramifiedAt (𝓞 K) Q] (hσ : _root_.IsArithFrobAt (𝓞 K) σ Q) :
    _root_.Nat.card {P : _root_.Ideal (𝓞 L) // ∃ (_ : P.IsPrime) (_ : P.LiesOver 𝔭) (_ : P ≠ ⊥),
        _root_.IsArithFrobAt (𝓞 K) σ P} * _root_.orderOf σ
      = _root_.Nat.card (_root_.Subgroup.centralizer {σ}) := by
  have hle : _root_.Subgroup.zpowers σ ≤ _root_.Subgroup.centralizer {σ} :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr _root_.rfl)
  have hstab : _root_.MulAction.stabilizer (_root_.Subgroup.centralizer {σ}) Q
      = (_root_.Subgroup.zpowers σ).subgroupOf (_root_.Subgroup.centralizer {σ}) := by
    ext τ
    rw [_root_.Subgroup.mem_subgroupOf, Q.zpowers_eq_stabilizer_of_isArithFrobAt hσ.ne_bot hσ,
      _root_.MulAction.mem_stabilizer_iff, _root_.MulAction.mem_stabilizer_iff, _root_.Subgroup.smul_def]
  have key := _root_.Nat.card_congr
    (_root_.MulAction.orbitProdStabilizerEquivGroup (_root_.Subgroup.centralizer {σ}) Q)
  rw [_root_.Nat.card_prod, hstab, _root_.Nat.card_congr (_root_.Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    _root_.Nat.card_zpowers] at key
  have hcard : _root_.Nat.card {P : _root_.Ideal (𝓞 L) // ∃ (_ : P.IsPrime) (_ : P.LiesOver 𝔭) (_ : P ≠ ⊥),
      _root_.IsArithFrobAt (𝓞 K) σ P}
      = _root_.Nat.card (_root_.MulAction.orbit (_root_.Subgroup.centralizer {σ}) Q) :=
    _root_.Nat.card_congr (_root_.Equiv.setCongr (_root_.Ideal.frobenius_fiber_eq_orbit_centralizer 𝔭 Q hσ))
  rw [hcard]
  exact key

end Ideal

namespace IsDedekindDomain.HeightOneSpectrum
end IsDedekindDomain.HeightOneSpectrum
section IsDedekindDomain.HeightOneSpectrum
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]









end IsDedekindDomain.HeightOneSpectrum

end
end
