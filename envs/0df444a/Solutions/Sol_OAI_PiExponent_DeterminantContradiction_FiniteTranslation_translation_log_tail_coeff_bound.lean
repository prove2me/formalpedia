-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_log_tail_coeff_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T17:50:24.313265+00:00
-- url     : https://prove2.me/submissions/92b65ff6-b2f5-4da2-90f4-fc1ecd0bd0a3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_translation_log_tail_coeff_le_majorant
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_powerSeries_coeff_product_pow_majorant
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_log_majorant_coeff_nonnegative
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_log_majorant_power_coeff_le_one
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_translation_log_tail_allowance_ge_one

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu) {H : ℝ}
    (hH : 0 < H) (r : Row d H) (t : Choice d H r) :
    ‖PowerSeries.coeff (t.2.2 : ℕ)
        (∏ i : Fin d.m,
          ((PowerSeries.trunc
            (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
            (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ) ^
              (t.2.1 i : ℕ))‖ ≤
      Real.exp (H * (Real.log 2 / (d.v0 : ℝ))) := by
  let L : PowerSeries ℂ := PowerSeries.mk
    (fun n : ℕ => if n = 0 then 0 else (n : ℂ)⁻¹)
  let B : Fin d.m → PowerSeries ℂ := fun i =>
    ((PowerSeries.trunc
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
      (PowerSeries.log ℂ) : PowerSeries ℂ) - PowerSeries.log ℂ)
  have hL : ∀ n, ∃ x : ℝ, 0 ≤ x ∧ PowerSeries.coeff n L = (x : ℂ) := by
    exact log_majorant_coeff_nonnegative
  have hB : ∀ i n, ‖PowerSeries.coeff n (B i)‖ ≤
      ‖PowerSeries.coeff n L‖ := by
    intro i n
    exact translation_log_tail_coeff_le_majorant
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i) n
  have hprod := powerSeries_coeff_product_pow_majorant L B
    (fun i => (t.2.1 i : ℕ)) (t.2.2 : ℕ) hL hB
  have hlog := log_majorant_power_coeff_le_one
    (∑ i : Fin d.m, (t.2.1 i : ℕ)) (t.2.2 : ℕ)
  have hallow := translation_log_tail_allowance_ge_one d hH
  simpa [L, B] using le_trans (le_trans hprod hlog) hallow