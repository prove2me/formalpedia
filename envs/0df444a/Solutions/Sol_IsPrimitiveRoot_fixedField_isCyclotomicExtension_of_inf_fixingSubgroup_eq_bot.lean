-- Prove2me | solution 1 for IsPrimitiveRoot.fixedField_isCyclotomicExtension_of_inf_fixingSubgroup_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:23:36.159457+00:00
-- url     : https://prove2.me/submissions/00b85ec5-3375-40c1-81f2-b6f51eb6973d

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Theorems.Thm_IsPrimitiveRoot_adjoin_singleton_eq_adjoin_nth_roots

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









/-- **A trivial meet of subgroups is a full join of fields.** `M ^ H` and `E` generate `M` exactly
when `H ⊓ Gal(M/E)` is trivial.

This is the Galois correspondence read in both directions: `fixingSubgroup` turns a join of fields
into a meet of subgroups, and `fixedField` turns the trivial subgroup back into `⊤`.

Stated in the `Subgroup` namespace rather than `IntermediateField`, so that `H` — the first
explicit argument, and the one `fixedField` is applied to — carries the dot notation: a consumer
writes `H.fixedField_sup_eq_top_iff E`. -/
theorem fixedField_sup_eq_top_iff [FiniteDimensional K M] [IsGalois K M]
    (H : Subgroup (M ≃ₐ[K] M)) (E : IntermediateField K M) :
    fixedField H ⊔ E = ⊤ ↔ H ⊓ E.fixingSubgroup = ⊥ := by
  constructor
  · intro h
    have := congrArg IntermediateField.fixingSubgroup h
    rwa [fixingSubgroup_sup, fixingSubgroup_fixedField, fixingSubgroup_top] at this
  · intro h
    have hbot : (fixedField H ⊔ E).fixingSubgroup = ⊥ := by
      rw [fixingSubgroup_sup, fixingSubgroup_fixedField, h]
    have := congrArg fixedField hbot
    rwa [IsGalois.fixedField_fixingSubgroup, fixedField_bot] at this

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
# The fixed field of a subgroup meeting the cyclotomic fixers trivially

If `M` contains a primitive `m`-th root of unity and a subgroup `H ≤ Gal(M/K)` meets
`Gal(M/K(μ_m))` trivially, then `M` is an `m`-th cyclotomic extension of the fixed field `M ^ H`.

Only `M / K` is assumed finite and Galois. The root of unity enters as a hypothesis rather than
through an ambient cyclotomic tower, so no separately quantified intermediate field or cyclotomic
tower appears among the arguments — the fixed field itself is of course an `IntermediateField K M`,
being the base of the conclusion.

Nothing here needs `H` to be cyclic. The Chebotarev application takes `H = Subgroup.zpowers (σ, τ)`,
but the argument is the Galois correspondence and uses neither a generator nor cyclicity.

## Main results

* `IsPrimitiveRoot.fixedField_isCyclotomicExtension_of_inf_fixingSubgroup_eq_bot`

## Provenance

The proof is adapted from the private `compositum_isCyclotomic_over_fixedField` in
`CebotarevDensity/Abelian.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `8575c9df1ae0a61120ab5c964c7911414254bec7`. That version is stated for
a cyclic subgroup over a tower `K ⊆ L ⊆ M` of number fields; the hypotheses here are weaker.
-/

 section

open IntermediateField

/-- **The fixed field of `H` carries the cyclotomic extension**, whenever `H` meets the fixers of
`K(μ_m)` trivially.

The trivial meet says exactly that `M ^ H` and `K(μ_m)` generate `M`, so adjoining a primitive
root to `M ^ H` recovers all of `M`. -/
theorem solution
    {K M : Type*} [_root_.Field K] [_root_.Field M] [_root_.Algebra K M] [_root_.FiniteDimensional K M] [_root_.IsGalois K M]
    {m : ℕ} [_root_.NeZero m] {ζ : M} (hζ : _root_.IsPrimitiveRoot ζ m) (H : _root_.Subgroup (M ≃ₐ[K] M))
    (hmeet : H ⊓ (_root_.IntermediateField.adjoin K {b : M | b ^ m = 1}).fixingSubgroup = ⊥) :
    _root_.IsCyclotomicExtension {m} (_root_.IntermediateField.fixedField H) M := by
  set F : _root_.IntermediateField K M := _root_.IntermediateField.fixedField H
  set Kμ : _root_.IntermediateField K M := _root_.IntermediateField.adjoin K {b : M | b ^ m = 1}
  have hadjζ : _root_.IntermediateField.adjoin K {ζ} = Kμ := hζ.adjoin_singleton_eq_adjoin_nth_roots
  -- a trivial meet of fixing subgroups is a sup equal to `⊤`
  have htop : F ⊔ Kμ = ⊤ := (H.fixedField_sup_eq_top_iff Kμ).mpr hmeet
  -- hence `ζ` generates `M` over `F`
  have htopF : _root_.IntermediateField.adjoin F {ζ} = ⊤ := by
    apply _root_.IntermediateField.restrictScalars_injective K
    rw [_root_.IntermediateField.restrictScalars_adjoin_eq_sup, hadjζ, htop, _root_.IntermediateField.restrictScalars_top]
  have : _root_.Algebra.IsIntegral F M := _root_.Algebra.IsIntegral.of_finite F M
  have hcyc : _root_.IsCyclotomicExtension {m} F (_root_.IntermediateField.adjoin F {ζ}) :=
    _root_.IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension (K := F) hζ
  rw [htopF] at hcyc
  exact _root_.IsCyclotomicExtension.equiv (S := {m}) (A := F) (f := _root_.IntermediateField.topEquiv)

end
end
