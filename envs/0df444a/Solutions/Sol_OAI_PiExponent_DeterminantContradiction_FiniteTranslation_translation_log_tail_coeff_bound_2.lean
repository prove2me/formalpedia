-- Prove2me | solution 2 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.translation_log_tail_coeff_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T18:07:03.80335+00:00
-- url     : https://prove2.me/submissions/ec276fa6-969d-4c6a-b96c-227b28b34ddb

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_translation_log_tail_coeff_le_majorant
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_powerSeries_coeff_product_pow_majorant
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_log_majorant_coeff_nonnegative
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_log_majorant_power_coeff_le_two_pow
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

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
  classical
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
  have hlog := log_majorant_power_coeff_le_two_pow
    (∑ i : Fin d.m, (t.2.1 i : ℕ)) (t.2.2 : ℕ)
  have hrow :
      (d.v0 : ℝ) * (r.2.1 0 : ℝ) +
        (∑ i : Fin d.m,
          (MatrixArithmetic.logWeights (finiteDenominators d) i / (d.base.theta : ℝ)) *
            (r.2.1 i.succ : ℝ)) < H := by
    have hsum :
        (∑ j : Fin (d.m + 1),
          InterpolationMatrix.rowWeights (d.v0 : ℝ) (d.base.theta : ℝ)
            (MatrixArithmetic.logWeights (finiteDenominators d)) j *
              (r.2.1 j : ℝ)) < H :=
      (Finset.mem_filter.mp r.2.property).2
    simpa only [Fin.sum_univ_succ, InterpolationMatrix.rowWeights,
      Fin.cases_zero, Fin.cases_succ] using hsum
  have hrest : 0 ≤
      ∑ i : Fin d.m,
        (MatrixArithmetic.logWeights (finiteDenominators d) i / (d.base.theta : ℝ)) *
          (r.2.1 i.succ : ℝ) := by
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg
    · apply div_nonneg
      · unfold MatrixArithmetic.logWeights
        exact Nat.cast_nonneg _
      · exact le_of_lt d.base.theta_pos
    · exact Nat.cast_nonneg _
  have hr0 : (r.2.1 0 : ℝ) ≤ H / (d.v0 : ℝ) := by
    apply (le_div_iff₀ d.v0_pos).mpr
    nlinarith [hrow, hrest]
  have hk0 : (t.2.2 : ℕ) ≤ r.2.1 0 :=
    Nat.le_of_lt_succ t.2.2.isLt
  have hk : ((t.2.2 : ℕ) : ℝ) ≤ H / (d.v0 : ℝ) :=
    le_trans (by exact_mod_cast hk0) hr0
  have hallow : (2 : ℝ) ^ (t.2.2 : ℕ) ≤
      Real.exp (H * (Real.log 2 / (d.v0 : ℝ))) := by
    calc
      (2 : ℝ) ^ (t.2.2 : ℕ) =
          Real.exp (((t.2.2 : ℕ) : ℝ) * Real.log 2) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ ≤ Real.exp ((H / (d.v0 : ℝ)) * Real.log 2) :=
        Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right hk (Real.log_nonneg (by norm_num)))
      _ = Real.exp (H * (Real.log 2 / (d.v0 : ℝ))) := by
        congr 1
        ring
  simpa only [L, B] using le_trans (le_trans hprod hlog) hallow
