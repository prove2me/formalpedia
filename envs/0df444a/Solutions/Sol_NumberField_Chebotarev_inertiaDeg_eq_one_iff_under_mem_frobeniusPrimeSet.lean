-- Prove2me | solution 1 for NumberField.Chebotarev.inertiaDeg_eq_one_iff_under_mem_frobeniusPrimeSet
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:32:41.496997+00:00
-- url     : https://prove2.me/submissions/7d6906be-03e5-411e-a9cf-067b53daf037

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_FieldTheory_Galois_FixedField
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_FrobeniusPrimeSet
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_RamifiedPrimes
import Definitions.Def_TauCeti_NumberTheory_NumberField_ArtinSymbol
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Definitions.Def_TauCeti_NumberTheory_NumberField_Frobenius
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_RamificationLocus
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.Tactic.Group
import Theorems.Thm_NumberField_isArithFrobAt_restrictScalars_of_inertiaDeg_eq_one

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Fixed fields and fixing subgroups

Complements to Mathlib's Galois correspondence: its interaction with the complete-lattice
operations, when a fixed field and an intermediate field generate the whole extension, when the
correspondence survives dropping finiteness of `M / K` for a finite subgroup, and what the
correspondence gives for a cyclic subgroup.

Taking fixed fields always sends joins of automorphism subgroups to intersections of intermediate
fields. For a finite Galois extension it also sends subgroup intersections to composita of fixed
fields. Both the binary and indexed forms are recorded so that finite generating families and
arbitrary families can use these lattice laws without manually passing through the order dual in
the Galois correspondence.

For a finite Galois extension `M / K`, a subgroup `H ≤ Gal(M/K)` and an intermediate field `E`,
the fixed field of `H` and `E` generate `M` exactly when `H` meets the fixers of `E` trivially.
With no hypothesis on `M / K`, the fixers of an arbitrary join of intermediate fields are the
automorphisms fixing each of them.

The correspondence is equivariant for conjugation: the fixed field of a conjugate subgroup is the
image of the fixed field under the conjugating automorphism.

The correspondence between subgroups and their fixed fields also holds with no hypothesis on
`M / K` at all, provided the subgroup is finite: Artin's theorem makes `M` finite Galois over the
fixed field of a finite `H`, and the fixers of that field are then exactly `H`. This is how a
subgroup of the automorphism group of an infinite extension is recovered from the field it cuts
out; the fixing subgroup of a subfield of finite degree is finite for the same reason.

The last results specialise the correspondence to a *cyclic* subgroup: the field fixed by a finite
cyclic group of automorphisms has `M` cyclic over it, and for `⟨σ⟩` there is a named automorphism
over the fixed field — `AlgEquiv.toFixedFieldAlgEquiv σ` acts on `M` as `σ` does, and generates
once `⟨σ⟩` is finite.

Neither `M / K` Galois nor `M / K` finite is needed, and neither is faithfulness of the action:
`FixedPoints.toAlgAut_surjective` asks only that the group be finite, and cyclicity passes along
its surjection. The fixed-point subfield it produces is the one underlying
`IntermediateField.fixedField`.

A simple extension `K⟮x⟯` is fixed pointwise by exactly those automorphisms that fix `x`, so
its fixing subgroup is the stabilizer of `x`; this too needs no hypothesis on `M / K` at all.

Two facts hold for every intermediate field `E` algebraic over `K`, with no separability anywhere
and nothing asked of `M / K`: its fixing subgroup is closed in the Krull topology, being the
intersection over the finite simple subextensions of their open fixing subgroups; and it is
unchanged by cutting `E` down to its part inside `separableClosure K M`, because every element of
`E` has a `q`-th power iterate there. The second is why a Galois correspondence over an
inseparable extension can only be indexed by the intermediate fields of the separable closure.

## Main results

* `Subgroup.fixedField_inf` and `Subgroup.fixedField_sup`
* `Subgroup.fixedField_iInf` and `Subgroup.fixedField_iSup`
* `Subgroup.fixedField_sup_eq_top_iff`
* `Subgroup.fixedField_map_conj`
* `IntermediateField.fixingSubgroup_inf`
* `IntermediateField.fixingSubgroup_iSup`
* `IntermediateField.fixingSubgroup_isClosed_of_isAlgebraic`
* `IntermediateField.fixingSubgroup_inf_separableClosure`
* `IntermediateField.fixingSubgroup_fixedField_of_finite`
* `IntermediateField.finite_of_finiteDimensional_fixedField`
* `IntermediateField.card_fixingSubgroup_le`
* `IntermediateField.fixingSubgroup_adjoin_simple`, with
  `IntermediateField.mem_fixedField_stabilizer`,
  `IntermediateField.fixedField_stabilizer_eq_adjoin_simple`,
  `IntermediateField.fixedField_iInf_stabilizer_eq_adjoin_range` and
  `IntermediateField.adjoin_eq_top_of_fixedField_stabilizer`: the stabilizer of `x` fixes
  exactly `K⟮x⟯`, in which `x` is a primitive element
* `FixedPoints.isCyclic_algEquiv`
* `AlgEquiv.toFixedFieldAlgEquiv`, with `AlgEquiv.zpowers_toFixedFieldAlgEquiv_eq_top` and
  `AlgEquiv.card_algEquiv_fixedField_zpowers`
* `TauCeti.natCard_algEquiv_dvd_finrank`: the automorphism group of a finite extension has order
  dividing the degree, since that order is the degree over the field fixed by all automorphisms
-/

 section

open IntermediateField

namespace IntermediateField

variable {K M : Type*} [Field K] [Field M] [Algebra K M]







end IntermediateField

namespace Subgroup

variable {K M : Type*} [Field K] [Field M] [Algebra K M]











end Subgroup

namespace IntermediateField

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

















-- The subgroup extensionality argument below, reducing membership of `K⟮x⟯.fixingSubgroup` to
-- `IntermediateField.forall_mem_adjoin_smul_eq_self_iff` at the singleton `{x}`, is adapted from
-- the proof of `stabilizer_isOpen_of_isIntegral` in `Mathlib/FieldTheory/KrullTopology.lean`,
-- which uses it there to identify a point stabilizer with the fixing subgroup of a finite
-- intermediate field. Here it is recorded as a statement in its own right, with no integrality
-- hypothesis.










end IntermediateField

namespace Subgroup

variable {K M : Type*} [Field K] [Field M] [Algebra K M]



end Subgroup

namespace FixedPoints



end FixedPoints

namespace AlgEquiv

variable {K M : Type*} [Field K] [Field M] [Algebra K M]

-- Source. The fixed field of `⟨σ⟩` and its named generator are the constructions pinned at
-- `TauCetiRoadmap/Chebotarev/Suggested.lean` lines 283-291, as `cyclicFixedField` and
-- `fixedFieldGenerator`. Neither name is kept: the field is spelled
-- `IntermediateField.fixedField (Subgroup.zpowers σ)` throughout rather than abbreviated, and the
-- automorphism is `toFixedFieldAlgEquiv`, because it is defined without finiteness and only
-- generates once `⟨σ⟩` is finite.



/-- **The rebundled automorphism acts as `σ`.** This is what makes `toFixedFieldAlgEquiv σ`
usable: it is a different bundling of the same underlying map, over the fixed field rather than
over `K`. It says nothing about generation, which needs `⟨σ⟩` finite and is
`zpowers_toFixedFieldAlgEquiv_eq_top`. -/
@[simp]
theorem toFixedFieldAlgEquiv_apply (σ : M ≃ₐ[K] M) (x : M) :
    toFixedFieldAlgEquiv σ x = σ x :=
  (rfl)

/-- **Restricting scalars undoes the rebundling.** Read back over `K`, `σ.toFixedFieldAlgEquiv`
is `σ` itself — the elimination rule matching `toFixedFieldAlgEquiv_apply`, in bundled form, which
is what a tower argument needs when it must produce an equation between automorphisms rather than
between their values. -/
@[simp]
theorem restrictScalars_toFixedFieldAlgEquiv (σ : M ≃ₐ[K] M) :
    AlgEquiv.restrictScalars K σ.toFixedFieldAlgEquiv = σ :=
  AlgEquiv.ext fun x ↦ toFixedFieldAlgEquiv_apply σ x





end AlgEquiv

namespace TauCeti



end TauCeti

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
# The Artin symbol of an unramified prime

For a finite Galois extension of number fields, this file attaches to an unramified
prime ideal of the base the conjugacy class of its arithmetic Frobenius elements.
The definition uses Mathlib's `IsArithFrobAt` and `arithFrobAt`; no Frobenius
predicate or representative is introduced here.

The construction follows Jürgen Neukirch, *Algebraic Number Theory*, Chapter I, §9,
Exercise 2.

The same reference gives functoriality in a normal tower: restriction maps the Artin symbol of
`L/K` to the Artin symbol of `M/K`. Unramifiedness in the intermediate extension is derived from
unramifiedness in the top extension, rather than assumed separately.

Raising the base field is the companion law, and it takes a power: for `K ⊆ M ⊆ L`, the symbol
of a prime of `𝓞 M` above `𝔭`, read inside `Gal(L/K)`, is the `f(𝔓/𝔭)`-th power of the symbol of
`𝔭`. Stated on conjugacy classes it names no prime of `𝓞 L` and no Frobenius representative, both
of which the element-level form in `TauCeti.NumberTheory.NumberField.Frobenius.Tower` fixes.

Finally, the symbol detects complete splitting: it is the identity class exactly when the
residue degree is one, equivalently when `𝓞 L` has `[L : K]` primes above `𝔭`.
-/

 section

open _root_.Ideal
open scoped _root_.NumberField _root_.Pointwise

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]







/-- Every representative of `artinSymbol 𝔭 hur` is an arithmetic Frobenius at some prime above
`𝔭`. -/
theorem exists_isArithFrobAt_of_artinSymbol_eq_mk {L : Type*} [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal]
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭],
      Algebra.IsUnramifiedAt (𝓞 K) Q) {σ : L ≃ₐ[K] L}
    (h : artinSymbol 𝔭 hur = ConjClasses.mk σ) :
    ∃ Q : 𝔭.primesOver (𝓞 L), IsArithFrobAt (𝓞 K) σ Q.1 := by
  obtain ⟨Q₀, _, _⟩ := (inferInstance : Nonempty (𝔭.primesOver (𝓞 L)))
  obtain ⟨σ₀, hσ₀⟩ := exists_isArithFrobAt K Q₀
    (Ideal.ne_bot_of_liesOver_of_ne_bot (NeZero.ne 𝔭) Q₀)
  have hconj : IsConj σ₀ σ := ConjClasses.mk_eq_mk_iff_isConj.mp
    ((artinSymbol_eq_mk_of_isArithFrobAt 𝔭 hur Q₀ σ₀ hσ₀).symm.trans h)
  obtain ⟨τ, hτ⟩ := isConj_iff.mp hconj
  exact ⟨Ideal.primesOver.mk 𝔭 (τ • Q₀), hτ ▸ hσ₀.conj τ⟩

section IsoOfExtensions

/-!
### Transport along an isomorphism of extensions

An isomorphism `e : L ≃ₐ[K] L'` of extensions of `K` induces `𝓞 L ≃ₐ[𝓞 K] 𝓞 L'`, and everything
`artinSymbol` is built from travels along it: the primes above `𝔭`, their unramifiedness, and the
Frobenius condition. The symbol itself is therefore equivariant for the induced isomorphism
`AlgEquiv.autCongr e` of Galois groups.
-/

variable {L L' : Type*} [Field L] [Algebra K L] [Field L'] [Algebra K L']

variable [NumberField L] [IsGalois K L] [NumberField L'] [IsGalois K L']



end IsoOfExtensions

section SplitsCompletely

/-!
### The trivial Artin symbol

Two equivalent readings of the identity Artin class at an unramified prime: residue degree one,
and complete splitting.
-/

variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [IsGalois K L]





end SplitsCompletely

section BaseChange

/-!
### Raising the base field

The companion to `artinSymbol_map_restrictNormalHom`. That law shrinks the top field of a normal
tower and takes no power; this one raises the base field and takes the power `f(𝔓/𝔭)`.
-/

-- Source. Both transport laws are specified by `TauCetiRoadmap/Chebotarev/README.md` Layer 1,
-- which asks for closed transport lemmas derived from `artinSymbol_map_restrictNormalHom` and
-- `exists_isArithFrobAt_pow_inertiaDeg`. This is the second of the two.



end BaseChange

end NumberField

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
# The unramified primes carrying a prescribed Artin class

Let `L / K` be a finite Galois extension of number fields and let `C` be a conjugacy class in
`Gal(L/K)`. This file defines the set

`frobeniusPrimeSet K L C : Set (HeightOneSpectrum (𝓞 K))`

of height-one primes `𝔭` of `𝓞 K` that are unramified in `L` and whose Artin class is `C`. It is
the set whose density the Chebotarev density theorem computes.

## The dependent membership condition

`artinSymbol` is a *partial* construction: it takes an unramifiedness proof as an argument and has
no value at a ramified prime. So membership cannot be an equation between two total functions;
it is stated as

`∃ hur : (𝔭 is unramified in L), artinSymbol 𝔭.asIdeal hur = C`,

an existential over a proof. Membership is nonetheless unambiguous: it does not depend on which
unramifiedness proof witnesses it, and `mem_frobeniusPrimeSet_iff_artinSymbol_eq` turns the
existential into the plain equation `artinSymbol 𝔭.asIdeal hur = C` for whichever unramifiedness
proof `hur` the caller has in hand.

The alternative — a total `Gal(L/K)`-valued or `ConjClasses`-valued function taking a junk value
at the ramified primes — is worse for this set: the junk value carries no arithmetic content, yet
the ramified primes would sit inside the fibre of whichever class it names, so the fibres would
neither cover the unramified primes exactly nor be pinned down by a Frobenius element there. The
existential is what keeps the fibres free of them.

## Main definitions

* `NumberField.Chebotarev.frobeniusPrimeSet`: the primes of `𝓞 K` unramified in `L` whose Artin
  class is `C`.

## Main results

* `NumberField.Chebotarev.mem_frobeniusPrimeSet_iff_artinSymbol_eq`: proof-independence — with
  any unramifiedness proof in hand, membership is the equation `artinSymbol 𝔭.asIdeal hur = C`.
* `NumberField.Chebotarev.mem_frobeniusPrimeSet_mk_iff_exists_isArithFrobAt`: for an unramified
  `𝔭` and an element `σ`, membership in the fibre of `[σ]` says exactly that `σ` is an arithmetic
  Frobenius at *some* prime of `𝓞 L` above `𝔭`.
* `NumberField.Chebotarev.frobeniusPrimeSet_map_autCongr`: equivariance — an isomorphism
  `e : L ≃ₐ[K] L'` of extensions of `K` matches the fibre of `C` in `L` with the fibre in `L'` of
  the image of `C` under the induced isomorphism `AlgEquiv.autCongr e` of Galois groups.
* `NumberField.Chebotarev.frobeniusPrimeSet_subset_map_restrictNormalHom`: a fibre over `L` lies
  in the fibre over a Galois subextension `M` of the restricted class.
* `NumberField.Chebotarev.disjoint_frobeniusPrimeSet`: distinct classes have disjoint fibres.
* `NumberField.Chebotarev.iUnion_frobeniusPrimeSet`: the fibres cover exactly the complement of
  `ramifiedPrimes K L`, so `existsUnique_mem_frobeniusPrimeSet` partitions the unramified primes
  and `finite_compl_iUnion_frobeniusPrimeSet` records that the discarded remainder is finite.

The last two are what let the density arguments discard a finite exceptional set and then work
one class at a time: a lower density bound for each class can be squeezed against a partition of
a cofinite set, which is how the crossing argument produces exact densities.
-/

 section

open _root_.Ideal
open scoped _root_.NumberField

open _root_.IsDedekindDomain (HeightOneSpectrum)

namespace NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]



/-- Membership in `frobeniusPrimeSet`, unfolded. Downstream files should open the definition
through this lemma rather than through defeq. -/
@[simp]
theorem mem_frobeniusPrimeSet_iff {𝔭 : HeightOneSpectrum (𝓞 K)}
    {C : ConjClasses (L ≃ₐ[K] L)} :
    𝔭 ∈ frobeniusPrimeSet K L C ↔
      ∃ hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
        Algebra.IsUnramifiedAt (𝓞 K) Q, artinSymbol 𝔭.asIdeal hur = C :=
  Iff.rfl







/-- A member of `frobeniusPrimeSet K L C` is unramified in `L`. -/
theorem isUnramifiedAt_of_mem_frobeniusPrimeSet {𝔭 : HeightOneSpectrum (𝓞 K)}
    {C : ConjClasses (L ≃ₐ[K] L)} (h : 𝔭 ∈ frobeniusPrimeSet K L C)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal] :
    Algebra.IsUnramifiedAt (𝓞 K) Q :=
  (mem_frobeniusPrimeSet_iff.mp h).elim fun hur _ ↦ hur Q



/-- **A Frobenius witnesses membership.** If `σ` is an arithmetic Frobenius at a prime `Q` of
`𝓞 L` above an unramified `𝔭`, then `𝔭` lies in the fibre of the class of `σ`. -/
theorem mem_frobeniusPrimeSet_mk_of_isArithFrobAt {𝔭 : HeightOneSpectrum (𝓞 K)}
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal] {σ : L ≃ₐ[K] L}
    (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    𝔭 ∈ frobeniusPrimeSet K L (ConjClasses.mk σ) :=
  ⟨hur, artinSymbol_eq_mk_of_isArithFrobAt 𝔭.asIdeal hur Q σ hσ⟩

/-- **Every representative is realized.** If `𝔭` lies in the fibre of the class of `σ`, then `σ`
itself — not merely some conjugate of it — is an arithmetic Frobenius at some prime of `𝓞 L`
above `𝔭`. -/
theorem exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk {𝔭 : HeightOneSpectrum (𝓞 K)}
    {σ : L ≃ₐ[K] L} (h : 𝔭 ∈ frobeniusPrimeSet K L (ConjClasses.mk σ)) :
    ∃ Q : 𝔭.asIdeal.primesOver (𝓞 L), IsArithFrobAt (𝓞 K) σ Q.1 := by
  obtain ⟨hur, hC⟩ := mem_frobeniusPrimeSet_iff.mp h
  exact exists_isArithFrobAt_of_artinSymbol_eq_mk 𝔭.asIdeal hur hC



section IsoOfExtensions

variable {L' : Type*} [Field L'] [NumberField L'] [Algebra K L'] [IsGalois K L']



end IsoOfExtensions

section RestrictNormal

variable {M : Type*} [Field M] [NumberField M] [Algebra K M] [Algebra M L] [IsScalarTower K M L]
  [IsGalois K M]



end RestrictNormal











end NumberField.Chebotarev

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
# Ideals over a fixed field

Let `H` be a subgroup of `Gal(L/K)` and `E = L ^ H`.  The Galois correspondence identifies `H` with
`Gal(L/E)` without moving points, hence without moving ideals: an element of `H` and its image in
`Gal(L/E)` act alike on the ideals of `𝓞 L`.  The stabilizer of an ideal `Q` in `Gal(L/E)`
therefore corresponds to `H ⊓ D(Q)`, with `D(Q)` the stabilizer of `Q` in `Gal(L/K)`; in
particular the two have the same number of elements.  The same holds for the inertia group
`I(Q)`, because the two bundlings of an element of `H` act alike on `𝓞 L` itself.

Let `σ` be an automorphism of `L` over `K` of finite order fixing an ideal `Q` of `𝓞 L`.  Then
every automorphism of `L` over the fixed field `L ^ ⟨σ⟩` fixes `Q`, because `Gal(L / L ^ ⟨σ⟩)` is
generated by `σ` read over that field.

The stabilizer statement needs neither `Q` prime, nor `σ` an arithmetic Frobenius, nor `L / K`
Galois: its hypothesis is only that `σ` fixes `Q`.  A Frobenius at an unramified prime supplies
that through `IsArithFrobAt.mem_stabilizer`, which is how a fixed-field fibre count uses this.

Transitivity of the Galois action then turns a full stabilizer into uniqueness of the prime above,
which is the second result.  That one does ask for `Q` prime, but still not for `L / K` to be
Galois: `L / L ^ ⟨σ⟩` is Galois on its own, being the fixed field of a finite group acting on `L`.
Uniqueness is not inertness — it excludes splitting, not ramification.

## Main results

* `AlgEquiv.toFixedFieldAlgEquiv_smul_ideal`: the two bundlings of `σ` act alike on ideals.
* `Subgroup.subgroupEquivAlgEquiv_smul_ideal`: the Galois correspondence `H ≃* Gal(L / L ^ H)`
  does not change how an element acts on ideals.
* `Ideal.comap_stabilizer_fixedField_eq_subgroupOf`: under that correspondence the stabilizer of
  `Q` in `Gal(L / L ^ H)` corresponds to `H ⊓ D(Q)`.
* `Ideal.card_stabilizer_fixedField_eq_card_inf`: so the two have the same number of elements.
* `Ideal.comap_inertia_fixedField_eq_subgroupOf`, `Ideal.card_inertia_fixedField_eq_card_inf`: the
  same two statements for the inertia group of `Q` in place of its stabilizer.
* `NumberField.stabilizer_fixedField_zpowers_eq_top`: over `L ^ ⟨σ⟩`, every automorphism fixes `Q`.
* `Ideal.eq_of_smul_eq_of_liesOver_under_fixedField`: `Q` is the only prime of `𝓞 L` lying over
  its contraction to `𝓞 (L ^ ⟨σ⟩)`.

## References

The corresponding step of the Birkbeck--Brasca Chebotarev development,
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0) at
commit `55a89985d47a3befcf6069aca1da250ff088b5c7`, is the private declaration
`stabilizer_intermediate_eq_top_of_frobenius` in `CebotarevDensity/FixedFieldDensity.lean`.  There
it is stated for an arithmetic Frobenius at an unramified prime, with four instance arguments
threaded through the signature; neither the hypotheses nor the instances are needed.  The
uniqueness statement is the private declaration `eq_of_liesOver_under_E_of_frobenius` in the same
file, likewise stated there for a Frobenius at an unramified prime; here it needs only that `σ`
fixes `Q`.
-/

 section

open IntermediateField

open scoped NumberField Pointwise

namespace AlgEquiv

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **The rebundled automorphism acts as `σ` on ideals.**  `AlgEquiv.toFixedFieldAlgEquiv σ` is
`σ` with its base field changed, so it induces the same action on the ideals of `𝓞 L`. -/
@[simp]
theorem toFixedFieldAlgEquiv_smul_ideal (σ : L ≃ₐ[K] L) (Q : Ideal (𝓞 L)) :
    (toFixedFieldAlgEquiv σ) • Q = σ • Q := by
  rw [Ideal.pointwise_smul_def, Ideal.pointwise_smul_def]
  refine congrArg (Ideal.map · Q) (RingHom.ext fun x ↦ NumberField.RingOfIntegers.ext ?_)
  simp only [MulSemiringAction.toRingHom_apply, NumberField.algebraMap_smul_eq_apply,
    toFixedFieldAlgEquiv_apply]

end AlgEquiv

namespace Subgroup

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- **The Galois correspondence does not move points.**  For a subgroup `H` of `Gal(L/K)`, the
automorphism of `L` over `L ^ H` attached to `τ ∈ H` is `τ` itself on elements. -/
@[simp]
theorem coe_subgroupEquivAlgEquiv (H : Subgroup (L ≃ₐ[K] L)) (τ : ↥H) (x : L) :
    subgroupEquivAlgEquiv H τ x = (τ : L ≃ₐ[K] L) x :=
  rfl

/-- **The Galois correspondence does not move ideals.**  For a subgroup `H` of `Gal(L/K)`, the
automorphism of `L` over `L ^ H` attached to `τ ∈ H` acts on the ideals of `𝓞 L` exactly as `τ`
acts over `K`. -/
@[simp]
theorem subgroupEquivAlgEquiv_smul_ideal (H : Subgroup (L ≃ₐ[K] L)) (τ : ↥H) (Q : Ideal (𝓞 L)) :
    subgroupEquivAlgEquiv H τ • Q = (τ : L ≃ₐ[K] L) • Q := by
  rw [Ideal.pointwise_smul_def, Ideal.pointwise_smul_def]
  refine congrArg (Ideal.map · Q) (RingHom.ext fun y ↦ NumberField.RingOfIntegers.ext ?_)
  exact coe_subgroupEquivAlgEquiv H τ (y : L)

end Subgroup

namespace NumberField

variable {K L : Type*} [Field K] [Field L] [Algebra K L]



end NumberField

namespace Ideal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]



section FixedFieldSubgroups

omit [NumberField K] [NumberField L]
variable [FiniteDimensional K L]

/-- **The decomposition group over a fixed field corresponds to the intersection.**  For a subgroup
`H` of `Gal(L/K)` and `E = L ^ H`, the Galois correspondence `H ≃* Gal(L/E)` pulls the stabilizer
of `Q` in `Gal(L/E)` back to the intersection of `H` with the stabilizer of `Q` in `Gal(L/K)`,
read inside `H`. -/
@[simp]
theorem comap_stabilizer_fixedField_eq_subgroupOf (Q : Ideal (𝓞 L)) (H : Subgroup (L ≃ₐ[K] L)) :
    (MulAction.stabilizer (L ≃ₐ[↥(fixedField H)] L) Q).comap
        (subgroupEquivAlgEquiv H : ↥H →* (L ≃ₐ[↥(fixedField H)] L))
      = (MulAction.stabilizer (L ≃ₐ[K] L) Q).subgroupOf H := by
  ext τ
  simp only [Subgroup.mem_comap, MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
  exact Eq.congr_left (H.subgroupEquivAlgEquiv_smul_ideal τ Q)

/-- A subgroup of `Gal(L / L ^ H)` whose pullback to `H` is `B.subgroupOf H` has as many elements as
`B ⊓ H`. -/
private theorem card_eq_card_inf_of_comap_eq (H : Subgroup (L ≃ₐ[K] L))
    {A : Subgroup (L ≃ₐ[↥(fixedField H)] L)} {B : Subgroup (L ≃ₐ[K] L)}
    (h : A.comap (subgroupEquivAlgEquiv H : ↥H →* (L ≃ₐ[↥(fixedField H)] L)) = B.subgroupOf H) :
    Nat.card A = Nat.card (B ⊓ H : Subgroup (L ≃ₐ[K] L)) := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : B ⊓ H ≤ H)).toEquiv,
    Subgroup.inf_subgroupOf_right, ← h, Subgroup.comap_equiv_eq_map_symm]
  exact Nat.card_congr
    (Subgroup.equivMapOfInjective _ _ (subgroupEquivAlgEquiv H).symm.injective).toEquiv

/-- **The decomposition group over a fixed field has the size of the intersection.**  For a
subgroup `H` of `Gal(L/K)` and `E = L ^ H`, the stabilizer of `Q` in `Gal(L/E)` has as many
elements as the intersection of `H` with the stabilizer of `Q` in `Gal(L/K)`. -/
-- Deliberately not `@[simp]`: `MulAction.mem_stabilizer_iff` and `Nat.card_eq_fintype_card`
-- rewrite this left-hand side further, so it is not in `simp`-normal form and the rule would
-- never fire. The simp-NF linter rejects the attribute.
theorem card_stabilizer_fixedField_eq_card_inf (Q : Ideal (𝓞 L)) (H : Subgroup (L ≃ₐ[K] L)) :
    Nat.card (MulAction.stabilizer (L ≃ₐ[↥(fixedField H)] L) Q)
      = Nat.card ((MulAction.stabilizer (L ≃ₐ[K] L) Q ⊓ H : Subgroup (L ≃ₐ[K] L))) :=
  card_eq_card_inf_of_comap_eq H (comap_stabilizer_fixedField_eq_subgroupOf Q H)





end FixedFieldSubgroups

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
# Ramification and residue degrees below a fixed field

Let `H` be a subgroup of `Gal(L/K)`, let `E = L ^ H`, and let `Q` be a nonzero prime of `𝓞 L`
over `𝓞 K`. The product of the ramification index and residue degree of `Q ∩ 𝓞 E` over
`𝓞 K` is the relative index

`[D(Q) : D(Q) ∩ H]`.

Equivalently, multiplying that product by the order of `D(Q) ∩ H` gives the corresponding
product for `Q` over `𝓞 K`. The proof combines multiplicativity of ramification indices and
residue degrees in the tower `K ⊆ E ⊆ L` with the identification of the decomposition group over
`E` with `D(Q) ∩ H`. Applied to a translate `σ • Q`, this is the decomposition-group index formula
for the prime of `E` below that translate.

The ramification index alone is the relative index `[I(Q) : I(Q) ∩ H]` of inertia groups, by the
same argument with the inertia group of `Q` over `E` identified with `I(Q) ∩ H`. So the prime
below `Q` in `E` has `e = 1` exactly when `I(Q) ≤ H`, and `e = f = 1` exactly when `D(Q) ≤ H`.

If `Q` is unramified over `K`, all ramification indices in the tower are one. The general formula
then specializes to the residue-degree identity previously used in Frobenius arguments. Nothing
in either statement needs `H` cyclic: the Galois correspondence identifies
`Gal(L/E)` with `H` acting on ideals exactly as it does over `K`, so the decomposition group of `Q`
over `E` corresponds to `H ⊓ D(Q)` and in particular has as many elements, and multiplicativity of
the two local invariants does the rest.

A Frobenius `φ` at `Q` generates `D(Q)`, so the count is `Subgroup.relIndex` — the index of
`H ⊓ ⟨φ⟩` in `⟨φ⟩` — and the residue degree is one exactly when `φ ∈ H`.  At `H = ⟨φ⟩` membership
is automatic and the degree is one, which is the hypothesis of
`NumberField.restrictScalars_eq_of_inertiaDeg_eq_one` and so the step a fixed-field fibre count
runs through.

## Main results

* `Ideal.ramificationIdx_mul_inertiaDeg_under_fixedField_mul_card_inf`: the local degree below
  `L ^ H`, multiplied by the order of `D(Q) ∩ H`, is the local degree of `Q` over the base.
* `Ideal.ramificationIdx_mul_inertiaDeg_under_fixedField_eq_relIndex`: the local degree below
  `L ^ H` is `[D(Q) : D(Q) ∩ H]`.
* `Ideal.ramificationIdx_under_fixedField_mul_card_inf`: the ramification index below `L ^ H`,
  multiplied by the order of `I(Q) ∩ H`, is the ramification index of `Q` over the base.
* `Ideal.ramificationIdx_under_fixedField_eq_relIndex`: the ramification index below `L ^ H` is
  `[I(Q) : I(Q) ∩ H]`.
* `Ideal.isUnramifiedAt_fixedField_iff_inertia_inf_eq_bot`: unramifiedness over `L ^ H` is
  equivalent to trivial intersection of inertia with `H`.
* `Ideal.inertiaDeg_under_fixedField_mul_card_inf`: the number of elements of `D(Q) ⊓ H` times the
  residue degree below `L ^ H` is the residue degree of `Q`.
* `Ideal.inertiaDeg_under_fixedField_eq_relIndex`: that residue degree is `Subgroup.relIndex`,
  the index of `H ⊓ ⟨φ⟩` in `⟨φ⟩`.
* `Ideal.isLeast_pow_mem_inertiaDeg_under_fixedField`: equivalently, it is the least `n ≥ 1` with
  `φ ^ n ∈ H`.
* `Ideal.inertiaDeg_under_fixedField_eq_one_iff`: it is one exactly when a Frobenius lies in `H`.
* `Ideal.inertiaDeg_under_fixedField_eq_one_of_isArithFrobAt`: at `σ = φ`, it is one.

## References

The decomposition-group index formula is Neukirch, *Algebraic Number Theory*, Chapter I, §9,
and Janusz, *Algebraic Number Fields*, Chapter I. The unramified Frobenius specialization also
appears in Sharifi, *Algebraic Number Theory*, Theorem 7.2.2. The corresponding step of the
Birkbeck--Brasca Chebotarev development,
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0) at
commit `55a89985d47a3befcf6069aca1da250ff088b5c7`, is the private declaration
`inertiaDeg_under_E_eq_one_of_frobenius` in `CebotarevDensity/FixedFieldDensity.lean`.  There it is
one conjunct of a triple that also records the ramification index and the residue-field count, and
it carries `orderOf σ = Nat.card Gal(L/E)` as a hypothesis; that equality is a consequence of the
Galois correspondence and is derived here rather than assumed.  Upstream states only the `σ = φ`
case; the general residue degree above is not there.
-/

 section

open IntermediateField

open scoped NumberField Pointwise

namespace Ideal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]











omit [IsGalois K L] in
/-- **The residue degree below a fixed field.**  For any subgroup `H` and `E = L ^ H`, the residue
degree of `Q ∩ 𝓞 E` over `𝓞 K` times the size of the intersection of `H` with the decomposition
group is the residue degree of `Q` itself.  Stated as a product, so no natural-number division is
truncated. -/
theorem inertiaDeg_under_fixedField_mul_card_inf (Q : Ideal (𝓞 L)) [Q.IsPrime] (hQ : Q ≠ ⊥)
    [Algebra.IsUnramifiedAt (𝓞 K) Q] (H : Subgroup (L ≃ₐ[K] L)) :
    (Q.under (𝓞 ↥(fixedField H))).inertiaDeg (𝓞 K)
        * Nat.card ((MulAction.stabilizer (L ≃ₐ[K] L) Q ⊓ H : Subgroup (L ≃ₐ[K] L)))
      = Q.inertiaDeg (𝓞 K) := by
  set E := fixedField H with hE
  have : IsScalarTower K ↥E L := E.isScalarTower_mid'
  have : IsGalois ↥E L := IsGalois.of_fixed_field L H
  have : Algebra.IsUnramifiedAt (𝓞 ↥E) Q := Algebra.IsUnramifiedAt.of_restrictScalars (𝓞 K) Q
  have htower : Q.inertiaDeg (𝓞 K)
      = (Q.under (𝓞 ↥E)).inertiaDeg (𝓞 K) * Q.inertiaDeg (𝓞 ↥E) :=
    inertiaDeg_tower (Q.under (𝓞 ↥E)) Q
  rw [htower, ← card_stabilizer_eq_inertiaDeg_of_isUnramifiedAt Q hQ,
    card_stabilizer_fixedField_eq_card_inf Q H]

/-- **The residue degree is a relative index.**  For any subgroup `H` and `φ` a Frobenius at an
unramified `Q`, the residue degree below `L ^ H` is `Subgroup.relIndex`, Mathlib's name for the
index of `H ⊓ ⟨φ⟩` in `⟨φ⟩`. -/
theorem inertiaDeg_under_fixedField_eq_relIndex (Q : Ideal (𝓞 L)) [Q.IsPrime] (hQ : Q ≠ ⊥)
    [Algebra.IsUnramifiedAt (𝓞 K) Q] (H : Subgroup (L ≃ₐ[K] L)) {φ : L ≃ₐ[K] L}
    (hφ : IsArithFrobAt (𝓞 K) φ Q) :
    (Q.under (𝓞 ↥(fixedField H))).inertiaDeg (𝓞 K) = H.relIndex (Subgroup.zpowers φ) := by
  have hmul := inertiaDeg_under_fixedField_mul_card_inf Q hQ H
  rw [← zpowers_eq_stabilizer_of_isArithFrobAt Q hQ hφ,
    ← orderOf_eq_inertiaDeg_of_isArithFrobAt Q hQ hφ] at hmul
  have hidx := Subgroup.relIndex_inf_mul_relIndex ⊥ H (Subgroup.zpowers φ)
  simp only [Subgroup.relIndex_bot_left, bot_inf_eq] at hidx
  rw [inf_comm, Nat.card_zpowers φ, ← hmul, mul_comm] at hidx
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hidx.symm





/-- **Residue degree one is membership.**  The prime below `Q` in `L ^ H` has residue degree one
over `𝓞 K` exactly when a Frobenius at `Q` lies in `H`. -/
-- Deliberately not `@[simp]`: `φ` occurs only in the hypothesis `hφ`, never in the left-hand
-- side, so `simp` cannot infer it and the rule would never fire. The simp-NF linter rejects
-- the attribute.
theorem inertiaDeg_under_fixedField_eq_one_iff (Q : Ideal (𝓞 L)) [Q.IsPrime] (hQ : Q ≠ ⊥)
    [Algebra.IsUnramifiedAt (𝓞 K) Q] (H : Subgroup (L ≃ₐ[K] L)) {φ : L ≃ₐ[K] L}
    (hφ : IsArithFrobAt (𝓞 K) φ Q) :
    (Q.under (𝓞 ↥(fixedField H))).inertiaDeg (𝓞 K) = 1 ↔ φ ∈ H := by
  rw [inertiaDeg_under_fixedField_eq_relIndex Q hQ H hφ, Subgroup.relIndex_eq_one,
    Subgroup.zpowers_le]

/-- **The prime below `Q` in the fixed field of a Frobenius at `Q` has degree one.**  The case
`H = ⟨σ⟩` with `σ` itself the Frobenius, where membership is automatic. -/
theorem inertiaDeg_under_fixedField_eq_one_of_isArithFrobAt (Q : Ideal (𝓞 L)) [Q.IsPrime]
    (hQ : Q ≠ ⊥) [Algebra.IsUnramifiedAt (𝓞 K) Q] {σ : L ≃ₐ[K] L}
    (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    (Q.under (𝓞 ↥(fixedField (Subgroup.zpowers σ)))).inertiaDeg (𝓞 K) = 1 :=
  (inertiaDeg_under_fixedField_eq_one_iff Q hQ (Subgroup.zpowers σ) hσ).2 (Subgroup.mem_zpowers σ)

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
# Frobenius fibers over cyclic fixed fields

Let `L / K` be a finite Galois extension, let `C` be a conjugacy class in `Gal(L/K)`, and choose
`sigma` in `C`.  Put `E = L ^ <sigma>`.  This file counts the primes of `E` over a prime in the
Frobenius class `C` whose relative Frobenius in `L / E` is the automorphism induced by `sigma`:

```text
#G / (#C * orderOf sigma).
```

Contraction identifies these primes with the primes of `L` at which `sigma` itself is an
arithmetic Frobenius.  The latter form one orbit under the centralizer of `sigma`; its stabilizer
is `<sigma>`.  The resulting count is the fixed-field multiplicity used when transferring prime
sums and densities between `E` and `K`.

## Main result

* `NumberField.Chebotarev.fixedField_frobenius_fiber_eq_image`: contraction identifies the
  relative fiber with the image of the corresponding absolute Frobenius fiber.
* `NumberField.Chebotarev.inertiaDeg_eq_one_iff_under_mem_frobeniusPrimeSet`: away from the
  ramified primes, a prime of the relative fiber has residue degree one over `K` exactly when the
  prime below it lies in the Frobenius fiber of `sigma`.
* `NumberField.Chebotarev.fixedField_frobenius_fiber_card`: the exact cardinality of the relative
  Frobenius fiber over one prime of `K`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, Section 9.
* R. Sharifi, *Algebraic Number Theory*, Theorem 7.2.2.
* C. Birkbeck and R. Brasca,
  [*Chebotarev density*](https://github.com/CBirkbeck/chebotarev-density),
  `CebotarevDensity/FixedFieldDensity.lean` at commit
  `55a89985d47a3befcf6069aca1da250ff088b5c7` (Apache-2.0).
-/

 section

open IntermediateField
open scoped NumberField Pointwise
open IsDedekindDomain (HeightOneSpectrum)

namespace NumberField.Chebotarev
end NumberField.Chebotarev
section NumberField.Chebotarev
open NumberField NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

private theorem NumberField.Chebotarev.isArithFrobAt_of_fixedField_isArithFrobAt
    (sigma : L ≃ₐ[K] L) (p : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hp : p ∈ _root_.NumberField.Chebotarev.frobeniusPrimeSet K L (_root_.ConjClasses.mk sigma))
    (Q : _root_.Ideal (𝓞 L)) [Q.IsPrime]
    (hQp : Q.under (𝓞 K) = p.asIdeal)
    (hrel : _root_.IsArithFrobAt (𝓞 ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma)))
      sigma.toFixedFieldAlgEquiv Q) :
    _root_.IsArithFrobAt (𝓞 K) sigma Q := by
  have hur : ∀ (P : _root_.Ideal (𝓞 L)) [P.IsPrime] [P.LiesOver p.asIdeal],
      _root_.Algebra.IsUnramifiedAt (𝓞 K) P :=
    (mem_frobeniusPrimeSet_iff.mp hp).choose
  have : Q.LiesOver p.asIdeal := ⟨hQp.symm⟩
  let _ : _root_.Algebra.IsUnramifiedAt (𝓞 K) Q := hur Q
  obtain ⟨phi, hphi⟩ := _root_.NumberField.exists_isArithFrobAt K Q
    (_root_.Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot Q)
  have hclass : _root_.ConjClasses.mk phi = _root_.ConjClasses.mk sigma := by
    rw [← (mem_frobeniusPrimeSet_iff.mp hp).choose_spec]
    exact (_root_.NumberField.artinSymbol_eq_mk_of_isArithFrobAt p.asIdeal hur Q phi hphi).symm
  have hconj : _root_.IsConj sigma phi :=
    ConjClasses.mk_eq_mk_iff_isConj.mp hclass.symm
  have hsigma_mem : sigma ∈ _root_.Subgroup.zpowers phi := by
    rw [_root_.Ideal.zpowers_eq_stabilizer_of_isArithFrobAt Q hphi.ne_bot hphi]
    rw [_root_.MulAction.mem_stabilizer_iff, ← _root_.AlgEquiv.toFixedFieldAlgEquiv_smul_ideal]
    exact hrel.mem_stabilizer
  have horder : _root_.orderOf sigma = _root_.orderOf phi :=
    _root_.SemiconjBy.orderOf_eq (↑hconj.choose) hconj.choose_spec
  have hz : _root_.Subgroup.zpowers sigma = _root_.Subgroup.zpowers phi := by
    apply _root_.Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hsigma_mem)
    rw [_root_.Nat.card_zpowers, _root_.Nat.card_zpowers, horder]
  have hdeg : (Q.under (𝓞 ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma)))).inertiaDeg (𝓞 K) = 1 :=
    (_root_.Ideal.inertiaDeg_under_fixedField_eq_one_iff Q hphi.ne_bot
      (_root_.Subgroup.zpowers sigma) hphi).2 (hz.symm ▸ _root_.Subgroup.mem_zpowers phi)
  have habs := _root_.NumberField.isArithFrobAt_restrictScalars_of_inertiaDeg_eq_one hrel hdeg
  rw [_root_.AlgEquiv.restrictScalars_toFixedFieldAlgEquiv] at habs
  exact habs







/-- **Residue degree one detects the absolute Frobenius class below a relative fiber.** Let `P`
be a prime of `L ^ <sigma>` whose relative Artin class in `L / L ^ <sigma>` is represented by
`sigma.toFixedFieldAlgEquiv`, and suppose that the prime of `K` below `P` is unramified in `L`.
Then `P` has residue degree one over `K` exactly when the prime below it has Artin class `[sigma]`.

Membership of `P` in the relative fiber does not by itself fix the class below.  If `L / K` is
cyclic of degree four with generator `g` and `sigma = g ^ 2`, a prime of `K` with Frobenius `g` is
inert in `L ^ <g ^ 2>`, and the prime above it has relative Frobenius `g ^ 2`.

The unramifiedness hypothesis cannot be dropped.  For `K = ℚ`, `L = ℚ(∛2, ζ₃)` and `sigma` a
transposition, the prime `𝔓` of `ℚ(∛2)` above `2` has residue degree one and relative Frobenius
`sigma`, although `2` ramifies in `L` and so has no Artin class.

Conversely, a prime of `K` in the class of `sigma` can have primes of residue degree one above it
whose relative Frobenius is another generator of `<sigma>`; `fixedField_frobenius_fiber_card`
counts those whose relative Frobenius is `sigma`. -/
theorem solution (sigma : L ≃ₐ[K] L)
    {P : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma)))}
    (hP : P ∈ _root_.NumberField.Chebotarev.frobeniusPrimeSet ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma)) L
      (_root_.ConjClasses.mk sigma.toFixedFieldAlgEquiv))
    (hram : P.under (𝓞 K) ∉ _root_.NumberField.Chebotarev.ramifiedPrimes K L) :
    P.asIdeal.inertiaDeg (𝓞 K) = 1 ↔
      P.under (𝓞 K) ∈ _root_.NumberField.Chebotarev.frobeniusPrimeSet K L (_root_.ConjClasses.mk sigma) := by
  obtain ⟨Q, hQ⟩ := _root_.NumberField.Chebotarev.exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk hP
  have hQE : Q.1.under (𝓞 ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma))) = P.asIdeal :=
    Q.2.2.over.symm
  have hQK : Q.1.under (𝓞 K) = (P.under (𝓞 K)).asIdeal := by
    rw [_root_.IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
    exact (_root_.Ideal.under_under (B := 𝓞 ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma))) Q.1).symm.trans
      (_root_.congrArg (_root_.Ideal.under (𝓞 K)) hQE)
  have : Q.1.LiesOver (P.under (𝓞 K)).asIdeal := ⟨hQK.symm⟩
  constructor
  · intro hdeg
    rw [_root_.NumberField.Chebotarev.mem_ramifiedPrimes_iff, _root_.Classical.not_not] at hram
    have habs := _root_.NumberField.isArithFrobAt_restrictScalars_of_inertiaDeg_eq_one hQ
      (hQE ▸ hdeg)
    rw [_root_.AlgEquiv.restrictScalars_toFixedFieldAlgEquiv] at habs
    exact _root_.NumberField.Chebotarev.mem_frobeniusPrimeSet_mk_of_isArithFrobAt hram Q.1 habs
  · intro hp
    let _ : _root_.Algebra.IsUnramifiedAt (𝓞 K) Q.1 := _root_.NumberField.Chebotarev.isUnramifiedAt_of_mem_frobeniusPrimeSet hp Q.1
    have habs := _root_.NumberField.Chebotarev.isArithFrobAt_of_fixedField_isArithFrobAt sigma _ hp Q.1 hQK hQ
    rw [← hQE]
    exact _root_.Ideal.inertiaDeg_under_fixedField_eq_one_of_isArithFrobAt Q.1 habs.ne_bot habs



-- The counting argument follows Birkbeck--Brasca, `CebotarevDensity/FixedFieldDensity.lean`.


end NumberField.Chebotarev

end
end
