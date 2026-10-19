-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_prefactor_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T17:40:21.733811+00:00
-- url     : https://prove2.me/submissions/4bca03b8-57ea-4cda-9a74-eca7cdce6d44

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_translation_binomial_factor_bound
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_translation_log_tail_coeff_bound

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r) :
    ‖(((∏ i : Fin d.m,
          (t.1.1 i).choose (r.2.1 i.succ) *
            (t.1.1 i - r.2.1 i.succ).choose (t.2.1 i) : ℕ) : ℂ) *
      PowerSeries.coeff (t.2.2 : ℕ)
        (∏ i : Fin d.m,
          ((PowerSeries.trunc
            (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
            (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ) ^
              (t.2.1 i : ℕ)))‖ ≤
      Real.exp (H * (Real.log 4 / d.wstar + Real.log 2 / (d.v0 : ℝ))) := by
  have hb := OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_binomial_factor_bound
    d hnu hH r t
  have hc := OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_log_tail_coeff_bound
    d hnu hH r t
  rw [norm_mul]
  calc
    ‖((∏ i : Fin d.m,
          (t.1.1 i).choose (r.2.1 i.succ) *
            (t.1.1 i - r.2.1 i.succ).choose (t.2.1 i) : ℕ) : ℂ)‖ *
        ‖PowerSeries.coeff (t.2.2 : ℕ)
          (∏ i : Fin d.m,
            ((PowerSeries.trunc
              (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
              (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ) ^
                (t.2.1 i : ℕ))‖
        ≤ Real.exp (H * (Real.log 4 / d.wstar)) *
            Real.exp (H * (Real.log 2 / (d.v0 : ℝ))) :=
      mul_le_mul hb hc (norm_nonneg _) (Real.exp_nonneg _)
    _ = Real.exp (H * (Real.log 4 / d.wstar + Real.log 2 / (d.v0 : ℝ))) := by
      rw [← Real.exp_add]
      congr 1
      ring