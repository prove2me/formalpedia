-- Prove2me | solution 1 for OAI.PiExponent.MatrixTranslationBounds.rounded_log_weight_majorant
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T13:06:51.464092+00:00
-- url     : https://prove2.me/submissions/58726d93-4df1-4a26-9712-56e40ac5392a

import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_OAI_NumberTheory_PiExponent_Approximation_MatrixArithmetic_CoreData

theorem solution
    (K j : ℕ) (ν : ℝ) (q : ℕ)
    (hK : 1 ≤ K) (hj : j ≤ K) (hν : 0 ≤ ν) (hq : 1 ≤ q) :
    (2 * (j : ℝ)) * (q : ℝ) ^ (-ν) ≤
      Real.exp ((Real.log (2 * (K : ℝ)) + ν) -
        ν * (⌈Real.log (q : ℝ)⌉₊ : ℝ)) := by
  have hKpos : 0 < (K : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK)
  have hqpos : 0 < (q : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hApos : 0 < 2 * (K : ℝ) := by positivity
  have hlogq : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hq)
  have hceil : (⌈Real.log (q : ℝ)⌉₊ : ℝ) < Real.log (q : ℝ) + 1 :=
    Nat.ceil_lt_add_one hlogq
  have hmul : ν * (⌈Real.log (q : ℝ)⌉₊ : ℝ) ≤
      ν * (Real.log (q : ℝ) + 1) :=
    mul_le_mul_of_nonneg_left hceil.le hν
  have hexp : Real.log (2 * (K : ℝ)) - ν * Real.log (q : ℝ) ≤
      (Real.log (2 * (K : ℝ)) + ν) -
        ν * (⌈Real.log (q : ℝ)⌉₊ : ℝ) := by
    nlinarith
  have hbase : (2 * (j : ℝ)) * (q : ℝ) ^ (-ν) ≤
      Real.exp (Real.log (2 * (K : ℝ)) - ν * Real.log (q : ℝ)) := by
    rw [Real.rpow_def_of_pos hqpos]
    have hjR : (j : ℝ) ≤ (K : ℝ) := by exact_mod_cast hj
    have hpow : 0 ≤ Real.exp (Real.log (q : ℝ) * -ν) :=
      (Real.exp_pos _).le
    calc
      (2 * (j : ℝ)) * Real.exp (Real.log (q : ℝ) * -ν) ≤
          (2 * (K : ℝ)) * Real.exp (Real.log (q : ℝ) * -ν) :=
        mul_le_mul_of_nonneg_right (by nlinarith) hpow
      _ = Real.exp (Real.log (2 * (K : ℝ)) - ν * Real.log (q : ℝ)) := by
        calc
          (2 * (K : ℝ)) * Real.exp (Real.log (q : ℝ) * -ν) =
              Real.exp (Real.log (2 * (K : ℝ))) *
                Real.exp (Real.log (q : ℝ) * -ν) := by
            rw [Real.exp_log hApos]
          _ = Real.exp (Real.log (2 * (K : ℝ)) +
                (Real.log (q : ℝ) * -ν)) := by rw [Real.exp_add]
          _ = Real.exp (Real.log (2 * (K : ℝ)) -
                ν * Real.log (q : ℝ)) := by congr 1 <;> ring
  exact hbase.trans (Real.exp_le_exp.mpr hexp)