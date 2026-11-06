-- Prove2me | solution 1 for OAI.SevenEighths.LatticeSummability.summable_weighted_normForm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:46:41.166527+00:00
-- url     : https://prove2.me/submissions/8f062e85-b1a6-4c94-9d43-275c51f07deb

import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Definitions.Def_OAI_NumberTheory_DirichletL_LatticeSummability
import Theorems.Thm_OAI_SevenEighths_LatticeSummability_normForm_nonneg
import Theorems.Thm_OAI_SevenEighths_LatticeSummability_summable_one_div_normForm_rpow
import Theorems.Thm_OAI_SevenEighths_EisensteinTheta_parityPair_k
import Theorems.Thm_OAI_SevenEighths_ThetaProduct_rectangularPair_k
attribute [local simp] OAI.SevenEighths.EisensteinTheta.parityPair_k
attribute [local simp] OAI.SevenEighths.ThetaProduct.rectangularPair_k



set_option autoImplicit false
open OAI
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.LatticeSummability
open EisensteinTheta
namespace OAI.SevenEighths.LatticeSummability
theorem _root_.solution {w : ℤ × ℤ → ℂ} {C σ : ℝ}
    (hw : ∀ n, ‖w n‖ ≤ C) (hσ : 1 < σ) :
    Summable (fun n : ℤ × ℤ => ‖w n‖ / normForm n.1 n.2 ^ σ) := by
  apply Summable.of_nonneg_of_le (fun n => div_nonneg (norm_nonneg _)
    (Real.rpow_nonneg (normForm_nonneg _ _) _)) _
    ((summable_one_div_normForm_rpow hσ).mul_left C)
  intro n
  simpa only [mul_one_div] using
    div_le_div_of_nonneg_right (hw n) (Real.rpow_nonneg (normForm_nonneg _ _) _)
end OAI.SevenEighths.LatticeSummability
