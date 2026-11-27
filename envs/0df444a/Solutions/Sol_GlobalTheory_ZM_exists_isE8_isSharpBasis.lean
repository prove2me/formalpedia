-- Prove2me | solution 1 for GlobalTheory.ZM.exists_isE8_isSharpBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:37:03.682739+00:00
-- url     : https://prove2.me/submissions/893089e4-01af-42d9-ae66-fd75f71e93d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_W8AddTransposeEqE8
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsE8IsSharpBasis
import Theorems.Thm_GlobalTheory_ZM_twistSnd_twistSnd
import Theorems.Thm_GlobalTheory_ZM_sum_omegaStd_twistSnd
import Theorems.Thm_GlobalTheory_ZM_sum_omegaStd_single
import Theorems.Thm_GlobalTheory_e8_det_eq_one
import Theorems.Thm_GlobalTheory_e8_mul_e8inv
import Theorems.Thm_GlobalTheory_e8_posDef
import Theorems.Thm_GlobalTheory_e8_transpose
import Theorems.Thm_GlobalTheory_e8inv_mul_e8
import Theorems.Thm_GlobalTheory_w8_add_transpose_eq_e8


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.ZM
namespace GlobalTheory.ZM
theorem _root_.solution : ∃ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W ∧ ∀ h : ℕ, ∃ bas : (Fin (2 * (8 * h)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)), IsSharpBasis W bas := by
  refine ⟨GlobalTheory.W8, ?_, fun h => ?_⟩
  · unfold IsE8
    rw [GlobalTheory.w8_add_transpose_eq_e8]
    exact ⟨GlobalTheory.e8_posDef, GlobalTheory.e8_det_eq_one⟩
  · let e : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) :=
      { twistSnd GlobalTheory.E8inv with
        invFun := twistSnd GlobalTheory.E8
        left_inv := twistSnd_twistSnd _ _ GlobalTheory.e8_mul_e8inv
        right_inv := twistSnd_twistSnd _ _ GlobalTheory.e8inv_mul_e8 }
    refine ⟨(sharpReindex h).trans e, fun i j => ?_⟩
    rw [GlobalTheory.w8_add_transpose_eq_e8, ← sum_omegaStd_single h i j]
    exact sum_omegaStd_twistSnd _ _ GlobalTheory.e8_transpose GlobalTheory.e8_mul_e8inv _ _
end GlobalTheory.ZM
