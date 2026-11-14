-- Prove2me | solution 1 for NarrowDNF.WidthBound.ceil_width_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @chenghua.liu
-- created : 2026-11-13T08:16:03.525439+00:00
-- url     : https://prove2.me/submissions/17f48e37-eb35-4b25-9237-c539b0045d70

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace NarrowDNF.WidthBound
end NarrowDNF.WidthBound

section


/-!
# Explicit width and error-budget arithmetic

These are the final arithmetic estimates in the proof of Theorem 1.2 of
the 2026-11-06 STOC revision. The source's numerical constants are retained. This
module does not assume or assert the structural theorem supplying the
approximator and activation family.
-/

noncomputable section

namespace NarrowDNF.WidthBound













private theorem two_pow_le_exp (d : ℕ) : (2 : ℝ)^d ≤ Real.exp (d : ℝ) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp 1]
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo d
  simpa only [← Real.exp_nat_mul, mul_one] using h













end NarrowDNF.WidthBound

end

end

noncomputable section
open NarrowDNF
open NarrowDNF.WidthBound
/-- Absorb the ceiling and the prefactor without taking logarithms. -/
theorem solution {ε a : ℝ} (hε : 0 < ε) (ha : 0 ≤ a) (d : ℕ) :
    (Nat.ceil (4 * (2 : ℝ)^d * Real.exp a / ε) : ℝ) ≤
      Real.exp (4 / ε + (d : ℝ) + a) := by
  have hpow : 1 ≤ (2 : ℝ)^d := one_le_pow₀ (by norm_num)
  have hexp : 1 ≤ Real.exp a := Real.one_le_exp_iff.mpr ha
  have hproduct : 1 ≤ (2 : ℝ)^d * Real.exp a := one_le_mul_of_one_le_of_one_le hpow hexp
  have hceil := (Nat.ceil_lt_add_one (by positivity :
    0 ≤ 4 * (2 : ℝ)^d * Real.exp a / ε)).le
  calc
    (Nat.ceil (4 * (2 : ℝ)^d * Real.exp a / ε) : ℝ)
        ≤ 4 * (2 : ℝ)^d * Real.exp a / ε + 1 := hceil
    _ ≤ (4 / ε + 1) * ((2 : ℝ)^d * Real.exp a) := by
      calc
        _ ≤ 4 * (2 : ℝ)^d * Real.exp a / ε + (2 : ℝ)^d * Real.exp a :=
          by simpa only [add_comm] using
            add_le_add_left hproduct (4 * (2 : ℝ)^d * Real.exp a / ε)
        _ = _ := by ring
    _ ≤ Real.exp (4 / ε) * ((2 : ℝ)^d * Real.exp a) :=
      mul_le_mul_of_nonneg_right (Real.add_one_le_exp (4 / ε)) (by positivity)
    _ ≤ Real.exp (4 / ε) * (Real.exp (d : ℝ) * Real.exp a) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_right (two_pow_le_exp d) (Real.exp_pos _).le
    _ = Real.exp (4 / ε + (d : ℝ) + a) := by rw [Real.exp_add, Real.exp_add]; ring
