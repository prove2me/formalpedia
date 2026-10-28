-- Prove2me | solution 1 for LargeCongestion.Poisson.proposition_5_a
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:05:04.211729+00:00
-- url     : https://prove2.me/submissions/afc669fb-bfa2-448a-85e7-8c1f7f08ab2d

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_LargeCongestion_Poisson_PoissonCalculus

open MeasureTheory ProbabilityTheory
open scoped ENNReal

open LargeCongestion.Poisson in
theorem solution (h : ℕ → ℝ) (x y : ℝ) (hy : 0 ≤ y) (hyx : y ≤ x) :
    ∑' k : ℕ, ENNReal.ofReal (|h k| * poissonPmf y k) ≤
      ENNReal.ofReal (Real.exp (x - y)) * ∑' k : ℕ, ENNReal.ofReal (|h k| * poissonPmf x k) := by
  have hx : 0 ≤ x := hy.trans hyx
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun k => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  rw [poissonPmf_eq hy, poissonPmf_eq hx]
  have hexp : Real.exp (x - y) * Real.exp (-x) = Real.exp (-y) := by
    rw [← Real.exp_add]; ring_nf
  have hpow : y ^ k ≤ x ^ k := pow_le_pow_left₀ hy hyx k
  have hf : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have key : Real.exp (-y) * y ^ k / (k.factorial : ℝ) ≤ Real.exp (-y) * x ^ k / (k.factorial : ℝ) := by
    apply div_le_div_of_nonneg_right _ hf.le
    exact mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
  calc |h k| * (Real.exp (-y) * y ^ k / (k.factorial : ℝ))
      ≤ |h k| * (Real.exp (-y) * x ^ k / (k.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left key (abs_nonneg _)
    _ = Real.exp (x - y) * (|h k| * (Real.exp (-x) * x ^ k / (k.factorial : ℝ))) := by
        rw [← hexp]; ring
