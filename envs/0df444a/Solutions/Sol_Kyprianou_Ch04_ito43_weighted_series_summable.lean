-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_weighted_series_summable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:15:00.36717+00:00
-- url     : https://prove2.me/submissions/e075097e-93ec-44e3-8ebf-dd34eb574a67

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Processes_Cadlag
import Theorems.Thm_Kyprianou_Ch04_ito43_path_weight_compact_bound
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
    (g : ℝ × ℝ → ℝ) (hg : ContinuousOn g (Ici (0 : ℝ) ×ˢ (univ : Set ℝ)))
    (t : NNReal) (hs : Summable (fun s : Ioc (0 : NNReal) t => (X s w-L s w)^2)) :
    Summable (fun s : Ioc (0 : NNReal) t =>
      |g (((s : NNReal) : ℝ), L s w) * (X s w-L s w)^2/2|) := by
  obtain ⟨M, hM, _, hL⟩ := ito43_path_weight_compact_bound X L w hc hl g hg t
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) ?_ (hs.mul_left (M/2))
  intro s
  let z : ℝ := X s w-L s w
  let a : ℝ := g (((s : NNReal) : ℝ), L s w)
  change |a*z^2/2| ≤ M/2*z^2
  have ha : |a| ≤ M := hL s s.2.1 s.2.2
  calc
    |a*z^2/2| = abs a * z^2 / 2 := by
      rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg z), abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    _ ≤ M*z^2/2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right ha (sq_nonneg z)) (by norm_num)
    _ = M/2*z^2 := by ring
