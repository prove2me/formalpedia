-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_scale_discount_series_compact_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:25:56.706139+00:00
-- url     : https://prove2.me/submissions/6bd28283-15d7-41ea-b30b-0a0aa63df68e

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Definitions.Def_Kyprianou_Ch08_ScaleConvolutionPower
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_power_continuous_positive
import Theorems.Thm_Kyprianou_Ch08_StageB_source_scale_compact_factorial_majorant
set_option autoImplicit false

open MeasureTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB

theorem solution (ψ : ℝ → ℝ) (W : ℝ → ℝ → ℝ)
    (hW : HasSourceScaleFamily ψ W)
    (q a R : ℝ) (hq : 0 ≤ q) (ha : 0 < a) (hR : a ≤ R) :
    ContinuousOn (fun x : ℝ => ∑' n : ℕ,
      q ^ n * scaleConvolutionPower (W 0) n x)
      (Set.Icc a R) := by
  have hR0 : 0 ≤ R := ha.le.trans hR
  have hsub : Set.Icc a R ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    exact lt_of_lt_of_le ha hx.1
  have hcont : ∀ n : ℕ, ContinuousOn
      (fun x : ℝ => q ^ n * scaleConvolutionPower (W 0) n x)
      (Set.Icc a R) := by
    intro n
    exact continuousOn_const.mul
      ((source_scale_power_continuous_positive ψ W hW n).mono hsub)
  have hfactorial : Summable (fun n : ℕ =>
      W 0 R * (q * R * W 0 R) ^ n / (Nat.factorial n : ℝ)) := by
    simpa only [mul_div_assoc] using
      (Real.summable_pow_div_factorial (q * R * W 0 R)).mul_left (W 0 R)
  have hbound : ∀ n : ℕ, ∀ x : ℝ, x ∈ Set.Icc a R →
      ‖q ^ n * scaleConvolutionPower (W 0) n x‖ ≤
      W 0 R * (q * R * W 0 R) ^ n / (Nat.factorial n : ℝ) := by
    intro n x hx
    apply source_scale_compact_factorial_majorant ψ W hW q R hq hR0 n x
    exact ⟨ha.le.trans hx.1, hx.2⟩
  exact continuousOn_tsum hcont hfactorial hbound
