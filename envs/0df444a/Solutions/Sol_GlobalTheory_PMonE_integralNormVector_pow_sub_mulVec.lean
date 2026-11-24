-- Prove2me | solution 1 for GlobalTheory.PMonE.integralNormVector_pow_sub_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:37:41.696234+00:00
-- url     : https://prove2.me/submissions/7b48a6e6-e4b6-47b4-aa57-a21699419707

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralSolutionFrobeniusSubMulVecEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LangCountFrobeniusEqMulVecSolutionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemPreparationNormalFormOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUniqueIntegralAdditiveSystemFrobeniusPowerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemGeneralLemmaOrderOne
import Theorems.Thm_GlobalTheory_PMonE_norm_mulVec_le_one_of_integral_matrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset
namespace GlobalTheory.PMonE
theorem _root_.solution {F : Type} [NormedField F] [IsUltrametricDist F] {m : Type} [Fintype m]
    (A : Matrix m m F) (hA : ∀ i j, ‖A i j‖ ≤ 1) (q : ℕ) (x : m → F) (hx : Integral x) :
    Integral (fun i => x i ^ q - A.mulVec x i) := by
  intro i
  have h1 : ‖x i ^ q‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hx i)
  have h2 := norm_mulVec_le_one_of_integral_matrix A hA x hx i
  calc ‖x i ^ q - A.mulVec x i‖ = ‖x i ^ q + -A.mulVec x i‖ := by rw [sub_eq_add_neg]
    _ ≤ max ‖x i ^ q‖ ‖-A.mulVec x i‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := by rw [norm_neg]; exact max_le h1 h2
end GlobalTheory.PMonE
