-- Prove2me | solution 1 for GroundTheory.LocalField.exists_finite_abelian_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:04.556+00:00
-- url     : https://prove2.me/submissions/69d753bd-4c08-45ff-9a75-9c4672df1d4a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalAbelianExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open IntermediateField
open scoped commutatorElement
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]
namespace GroundTheory.LocalField
theorem _root_.solution {y : Ω} (hy : y ∈ maximalAbelianExtension F Ω) :
    ∃ L : IntermediateField F Ω, FiniteDimensional F L ∧ IsAbelianGalois F L ∧ y ∈ L := by
  have : FiniteDimensional F F⟮y⟯ :=
    adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral y)
  set M : IntermediateField F Ω := normalClosure F F⟮y⟯ Ω
  have : FiniteDimensional F M := normalClosure.is_finiteDimensional F F⟮y⟯ Ω
  have : IsGalois F M := IsGalois.normalClosure F F⟮y⟯ Ω
  have hyM : y ∈ M := IntermediateField.le_normalClosure F⟮y⟯ (mem_adjoin_simple_self F y)
  have hMn : M.fixingSubgroup.Normal := by
    rw [← M.restrictNormalHom_ker]; exact MonoidHom.normal_ker _
  set H : Subgroup (Ω ≃ₐ[F] Ω) := M.fixingSubgroup ⊔ commutator (Ω ≃ₐ[F] Ω)
  have : H.Normal := Subgroup.sup_normal _ _
  set A : IntermediateField F Ω := fixedField H
  have hAM : A ≤ M := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup M]
    exact fixedField_le le_sup_left
  have : FiniteDimensional F A :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hAM).toLinearMap
      (IntermediateField.inclusion hAM).injective
  have hfix : ∀ g ∈ H, AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) A g = 1 := by
    intro g hg
    ext x
    rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.one_apply]
    exact (mem_fixedField_iff H (x : Ω)).1 x.2 g hg
  refine ⟨A, inferInstance, { toIsMulCommutative := ⟨⟨fun σ τ => ?_⟩⟩ }, ?_⟩
  · obtain ⟨σ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := A) (E := Ω) σ
    obtain ⟨τ', rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := A) (E := Ω) τ
    have hc := hfix ⁅σ', τ'⁆ (Subgroup.mem_sup_right
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top σ') (Subgroup.mem_top τ')))
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc
  · rw [mem_fixedField_iff]
    intro g hg
    have hle : H ≤ MulAction.stabilizer (Ω ≃ₐ[F] Ω) y := by
      refine sup_le (fun g hg => ?_) (fun g hg => ?_)
      · exact (IntermediateField.mem_fixingSubgroup_iff M g).1 hg y hyM
      · exact (mem_fixedField_iff _ y).1 hy g (Subgroup.le_topologicalClosure _ hg)
    exact hle hg
end GroundTheory.LocalField
