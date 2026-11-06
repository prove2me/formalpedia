-- Prove2me | solution 1 for OAI.SevenEighths.LatticeSummability.summable_normForm_neg_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:44:59.425876+00:00
-- url     : https://prove2.me/submissions/239248d6-a355-469a-98fb-d1fcdfddb4cd

import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Definitions.Def_OAI_NumberTheory_DirichletL_LatticeSummability
import Theorems.Thm_OAI_SevenEighths_LatticeSummability_normForm_nonneg
import Theorems.Thm_OAI_SevenEighths_LatticeSummability_normForm_ge_half_norm_sq
import Theorems.Thm_OAI_SevenEighths_LatticeSummability_summable_pair_norm_rpow
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
theorem _root_.solution {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℤ × ℤ => normForm n.1 n.2 ^ (-σ)) := by
  have hmajor := (summable_pair_norm_rpow (k := 2 * σ) (by linarith)).mul_left
    ((1 / 2 : ℝ) ^ (-σ))
  apply Summable.of_nonneg_of_le
    (fun n => Real.rpow_nonneg (normForm_nonneg _ _) _) _ hmajor
  intro n
  by_cases hn : n = 0
  · subst n
    simp [normForm, Real.zero_rpow (by linarith : -σ ≠ 0),
      Real.zero_rpow (by linarith : -(2 * σ) ≠ 0)]
  · have hnpos : 0 < ‖n‖ := norm_pos_iff.mpr hn
    calc
      normForm n.1 n.2 ^ (-σ) ≤ ((1 / 2 : ℝ) * ‖n‖ ^ 2) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (normForm_ge_half_norm_sq n)
          (by linarith)
      _ = (1 / 2 : ℝ) ^ (-σ) * ‖n‖ ^ (-(2 * σ)) := by
        rw [Real.mul_rpow (by norm_num) (sq_nonneg _)]
        congr 1
        rw [← Real.rpow_two, ← Real.rpow_mul (norm_nonneg _)]
        congr 1
        ring
end OAI.SevenEighths.LatticeSummability
