-- Prove2me | solution 1 for GlobalTheory.SmGL.UnitInd.exists_piForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:50:23.737358+00:00
-- url     : https://prove2.me/submissions/4e8e2828-6f3d-47f5-8d6f-087ee5ede70c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BlockTriangularOneAddMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsLocallyConstantModulus
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_IsSubquotient_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory Matrix
open scoped TensorProduct ENNReal
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.UnitInd
variable {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable {α : Type} [Fintype α] {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
namespace GlobalTheory.SmGL.UnitInd
theorem _root_.solution (B : ∀ a, X a →ₗ[ℂ] X a →ₗ⋆[ℂ] ℂ) (hs : ∀ a v w, B a w v = starRingEnd ℂ (B a v w)) :
    ∃ C : (⨂[ℂ] a, X a) →ₗ[ℂ] (⨂[ℂ] a, X a) →ₗ⋆[ℂ] ℂ, ∀ x y,
      C (PiTensorProduct.tprod ℂ x) (PiTensorProduct.tprod ℂ y) = ∏ a, B a (x a) (y a) := by
  let F : (∀ a, X a) → (⨂[ℂ] a, X a) →ₗ⋆[ℂ] ℂ := fun x =>
    (starLinearEquiv ℂ (A := ℂ)).toLinearMap.comp (PiTensorProduct.lift
      ((MultilinearMap.mkPiAlgebra ℂ α ℂ).compLinearMap fun a => (B a).flip (x a)))
  have hF : ∀ x y, F x (PiTensorProduct.tprod ℂ y) =
      (MultilinearMap.mkPiAlgebra ℂ α ℂ).compLinearMap (fun a => (B a).flip (y a)) x := fun x y => by
    simp [F, ← hs]
  refine ⟨PiTensorProduct.lift ⟨F, fun x i u v => ?_, fun x i c u => ?_⟩, fun x y => ?_⟩
  · refine LinearMap.ext_on_range PiTensorProduct.span_tprod_eq_top fun y => ?_
    rw [LinearMap.add_apply, hF, hF, hF, MultilinearMap.map_update_add]
  · refine LinearMap.ext_on_range PiTensorProduct.span_tprod_eq_top fun y => ?_
    rw [LinearMap.smul_apply, hF, hF, MultilinearMap.map_update_smul]
  · rw [PiTensorProduct.lift.tprod]
    exact (hF x y).trans (by simp)
end GlobalTheory.SmGL.UnitInd
