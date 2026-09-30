-- Prove2me | solution 1 for Ideal.eq_of_smul_eq_of_liesOver_under_fixedField
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:21:53.505184+00:00
-- url     : https://prove2.me/submissions/3498edea-cb4b-42fb-afcb-ee6998c0c714

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_FieldTheory_Galois_FixedField
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Theorems.Thm_AlgEquiv_zpowers_toFixedFieldAlgEquiv_eq_top

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
end AlgEquiv
section AlgEquiv
open AlgEquiv

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **The rebundled automorphism acts as `σ` on ideals.**  `AlgEquiv.toFixedFieldAlgEquiv σ` is
`σ` with its base field changed, so it induces the same action on the ideals of `𝓞 L`. -/
@[simp]
theorem AlgEquiv.toFixedFieldAlgEquiv_smul_ideal (σ : L ≃ₐ[K] L) (Q : _root_.Ideal (𝓞 L)) :
    (_root_.AlgEquiv.toFixedFieldAlgEquiv σ) • Q = σ • Q := by
  rw [_root_.Ideal.pointwise_smul_def, _root_.Ideal.pointwise_smul_def]
  refine _root_.congrArg (_root_.Ideal.map · Q) (_root_.RingHom.ext fun x ↦ _root_.NumberField.RingOfIntegers.ext ?_)
  simp only [_root_.MulSemiringAction.toRingHom_apply, _root_.NumberField.algebraMap_smul_eq_apply,
    _root_.AlgEquiv.toFixedFieldAlgEquiv_apply]

end AlgEquiv

namespace Subgroup
end Subgroup
section Subgroup
open Subgroup

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]





end Subgroup

namespace NumberField
end NumberField
section NumberField
open NumberField

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **Over the fixed field, every automorphism fixes `Q`.**  If `σ` has finite order and fixes the
ideal `Q`, the stabilizer of `Q` in `Gal(L / L ^ ⟨σ⟩)` is the whole group.

This says the stabilizer is everything, not that `L ^ ⟨σ⟩` is the largest such field. -/
@[simp]
theorem NumberField.stabilizer_fixedField_zpowers_eq_top {σ : L ≃ₐ[K] L} [_root_.Finite (_root_.Subgroup.zpowers σ)]
    {Q : _root_.Ideal (𝓞 L)} (hQ : σ • Q = Q) :
    _root_.MulAction.stabilizer (L ≃ₐ[↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers σ))] L) Q = ⊤ := by
  have hmem : _root_.AlgEquiv.toFixedFieldAlgEquiv σ ∈
      _root_.MulAction.stabilizer (L ≃ₐ[↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers σ))] L) Q := by
    rw [_root_.MulAction.mem_stabilizer_iff, _root_.AlgEquiv.toFixedFieldAlgEquiv_smul_ideal]
    exact hQ
  refine _root_.top_le_iff.1 ?_
  rw [← _root_.AlgEquiv.zpowers_toFixedFieldAlgEquiv_eq_top σ]
  exact _root_.Subgroup.zpowers_le.2 hmem

end NumberField

namespace Ideal
end Ideal
section Ideal
open Ideal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **A prime is the only one above its contraction to the fixed field.**  If `σ` fixes the prime
`Q` of `𝓞 L`, then `Q` is the only prime of `𝓞 L` lying over `Q ∩ 𝓞 (L ^ ⟨σ⟩)`.

This excludes splitting, not ramification: it says the fibre is a single point, and asserts nothing
about the ramification index.  A fixed-field fibre count is what needs it, and `σ` need not be a
Frobenius there either. -/
theorem solution {σ : L ≃ₐ[K] L} {Q : _root_.Ideal (𝓞 L)} [Q.IsPrime]
    (hQ : σ • Q = Q) (Q' : _root_.Ideal (𝓞 L)) [Q'.IsPrime]
    [Q'.LiesOver (Q.under (𝓞 ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers σ))))] :
    Q' = Q := by
  have : _root_.IsScalarTower K ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers σ)) L :=
    (_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers σ)).isScalarTower_mid'
  have : _root_.IsGalois ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers σ)) L :=
    _root_.IsGalois.of_fixed_field L (_root_.Subgroup.zpowers σ)
  have : _root_.IsGaloisGroup (L ≃ₐ[↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers σ))] L)
      ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers σ)) L := _root_.IsGaloisGroup.of_isGalois _ L
  have : Q.LiesOver (Q.under (𝓞 ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers σ)))) :=
    _root_.Ideal.over_under (A := 𝓞 ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers σ))) (P := Q)
  obtain ⟨τ, hτ⟩ := _root_.Ideal.exists_smul_eq_of_isGaloisGroup
    (Q.under (𝓞 ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers σ)))) Q Q'
    (L ≃ₐ[↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers σ))] L)
  rw [← hτ]
  exact MulAction.mem_stabilizer_iff.mp
    (_root_.NumberField.stabilizer_fixedField_zpowers_eq_top hQ ▸ _root_.Subgroup.mem_top τ)

section FixedFieldSubgroups

omit [NumberField K] [NumberField L]
variable [FiniteDimensional K L]











end FixedFieldSubgroups

end Ideal

end
end
