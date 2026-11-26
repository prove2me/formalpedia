-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41BoundedJumpEnvelopeV10
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:44:44.263787+00:00
-- url     : https://prove2.me/submissions/85652d01-826d-4d8e-835a-54bd048146bc

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    {ι : Type} (x l : ι → ℝ) (R K : ℝ)
    (hx : ∀ i, |x i| ≤ R) (hl : ∀ i, |l i| ≤ R)
    (g : ℕ → ℝ → ℝ) (G : ℝ → ℝ)
    (hg : ∀ n, ContDiff ℝ 1 (g n))
    (hlim : ∀ y, Tendsto (fun n => g n y) atTop (𝓝 (G y)))
    (hBound : ∀ n y, |y| ≤ R → ‖deriv (g n) y‖ ≤ K)
    (hSum : Summable (fun i => |x i - l i|)) :
    ∃ B : ι → ℝ, Summable B ∧
      (∀ᶠ n in atTop, ∀ i, ‖g n (x i) - g n (l i)‖ ≤ B i) ∧
      Summable (fun i => ‖G (x i) - G (l i)‖) := by
  let B : ι → ℝ := fun i => K * |x i - l i|
  have hB : Summable B := hSum.mul_left K
  have hJ (n : ℕ) (i : ι) : ‖g n (x i) - g n (l i)‖ ≤ B i := by
    have h := (convex_Icc (-R) R).norm_image_sub_le_of_norm_deriv_le
      (fun y _ => (hg n).differentiable (by norm_num) y)
      (fun y hy => hBound n y (abs_le.mpr hy))
      (abs_le.mp (hl i)) (abs_le.mp (hx i))
    simpa only [B, Real.norm_eq_abs] using h
  have hlimB (i : ι) : ‖G (x i) - G (l i)‖ ≤ B i :=
    le_of_tendsto' (tendsto_norm.comp ((hlim (x i)).sub (hlim (l i)))) (fun n => hJ n i)
  exact ⟨B,hB,Eventually.of_forall hJ,
    hB.of_nonneg_of_le (fun i => norm_nonneg _) hlimB⟩
