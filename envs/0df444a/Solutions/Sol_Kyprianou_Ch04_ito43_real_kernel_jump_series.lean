-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_real_kernel_jump_series
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:01:55.456351+00:00
-- url     : https://prove2.me/submissions/ec23c0cc-f46b-4bd4-9704-cc4483a38212

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Processes_Cadlag
import Theorems.Thm_Kyprianou_Ch04_ito43_general_kernel_jump_series
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
open Kyprianou.Ch04
set_option autoImplicit false
/-- Pathwise auxiliary for the weighted spatial correction. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (X L : NNReal → Ω → ℝ) (w : Ω)
    (hc : IsCadlag (fun s => X s w))
    (hl : ∀ s : NNReal, 0 < s →
      Tendsto (fun r => X r w) (nhdsWithin s (Iio s)) (nhds (L s w)))
    (K : ℝ → ℝ → ℝ → ℝ) (h0 : ∀ s x, K s x 0 = 0) (t : NNReal) :
    (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ),
      K z.1 (L z.1.toNNReal w) z.2 ∂(pathJumpMeasure X L w)) =
    ∑' s : Ioc (0 : NNReal) t, K ((s : NNReal) : ℝ) (L s w) (X s w-L s w) := by
  let K' : NNReal → ℝ → ℝ → ℝ := fun s x r => K (s : ℝ) x r
  calc
    _ = (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ),
        K' z.1.toNNReal (L z.1.toNNReal w) z.2 ∂(pathJumpMeasure X L w)) := by
      apply setIntegral_congr_fun (measurableSet_Icc.prod MeasurableSet.univ)
      intro z hz
      dsimp [K']
      rw [max_eq_left hz.1.1]
    _ = _ := ito43_general_kernel_jump_series X L w hc hl K'
      (fun s x => h0 (s : ℝ) x) t
