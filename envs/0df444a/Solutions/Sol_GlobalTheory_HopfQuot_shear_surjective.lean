-- Prove2me | solution 1 for GlobalTheory.HopfQuot.shear_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:21:39.130368+00:00
-- url     : https://prove2.me/submissions/1dff93dd-eba2-4242-82de-eaef67d3ef50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer
import Theorems.Thm_GlobalTheory_HopfQuot_ev_tmul
import Theorems.Thm_GlobalTheory_HopfQuot_shear_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HopfQuot.ev_tmul

set_option autoImplicit false
open GlobalTheory GlobalTheory.HopfQuot
open TensorProduct
variable {R Λ ι : Type*} [CommRing R] [CommRing Λ] [HopfAlgebra R Λ] [Fintype ι]
namespace GlobalTheory.HopfQuot
theorem _root_.solution : Function.Surjective (shear R Λ) := by
  have key : ∀ y : Λ, shear R Λ ((HopfAlgebra.antipode R).rTensor Λ (Coalgebra.comul y))
      = 1 ⊗ₜ y := by
    intro y
    have h1 : ∀ z : Λ ⊗[R] Λ, shear R Λ ((HopfAlgebra.antipode R).rTensor Λ z) =
        (LinearMap.mul' R Λ ∘ₗ (HopfAlgebra.antipode R).rTensor Λ).rTensor Λ
          ((TensorProduct.assoc R Λ Λ Λ).symm ((Coalgebra.comul (R := R)).lTensor Λ z)) := by
      intro z
      induction z with
      | zero => simp
      | add a b ha hb => simp only [map_add, ha, hb]
      | tmul a b =>
        rw [LinearMap.rTensor_tmul, shear_tmul, LinearMap.lTensor_tmul]
        generalize Coalgebra.comul (R := R) b = w
        induction w with
        | zero => simp
        | add u v hu hv => simp only [map_add, smul_add, tmul_add, hu, hv]
        | tmul u v => simp [TensorProduct.smul_tmul']
    rw [h1, Coalgebra.coassoc_symm_apply, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
      LinearMap.comp_assoc, HopfAlgebra.mul_antipode_rTensor_comul, LinearMap.rTensor_comp,
      LinearMap.comp_apply, Coalgebra.rTensor_counit_comul]
    simp
  intro z
  induction z with
  | zero => exact ⟨0, map_zero _⟩
  | add a b ha hb =>
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨a + b, map_add _ _ _⟩
  | tmul a b =>
    refine ⟨a • (HopfAlgebra.antipode R).rTensor Λ (Coalgebra.comul b), ?_⟩
    rw [map_smul, key, TensorProduct.smul_tmul']
    simp
end GlobalTheory.HopfQuot
