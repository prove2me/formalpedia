-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_weighted_path_cutoff_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:21:00.565933+00:00
-- url     : https://prove2.me/submissions/007a3f88-922f-4a8b-b424-f528fdcddd06

import Mathlib
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
import Definitions.Def_LeanLevy_Processes_Cadlag
import Theorems.Thm_Kyprianou_Ch04_ito43_weighted_series_summable
import Theorems.Thm_Kyprianou_Ch04_ito43_cutoff_summable_series_limit
import Theorems.Thm_Kyprianou_Ch04_ito43_real_kernel_jump_series
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
open Kyprianou.Ch04
set_option autoImplicit false
/-- Use the proved weighted jump series summability, cutoff summable series limit, and conversion of real-time kernels to actual jump series. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (X L : NNReal → Ω → ℝ) (w : Ω)
    (hc : IsCadlag (fun s => X s w))
    (hl : ∀ s : NNReal, 0 < s →
      Tendsto (fun r => X r w) (nhdsWithin s (Iio s)) (nhds (L s w)))
    (g : ℝ × ℝ → ℝ) (hg : ContinuousOn g (Ici (0:ℝ) ×ˢ (univ : Set ℝ)))
    (t : NNReal) (hs : Summable (fun s : Ioc (0:NNReal) t => (X s w-L s w)^2)) :
    Tendsto (fun m : ℕ =>
      ∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ),
        g (z.1,L z.1.toNNReal w)*z.2^2/2 *
          min 1 (max 0 (|z.2| * ((m:ℝ)+1)-1))
          ∂(pathJumpMeasure X L w)) atTop
      (nhds (∫ z in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ),
        g (z.1,L z.1.toNNReal w)*z.2^2/2 ∂(pathJumpMeasure X L w))) := by
  let z : Ioc (0:NNReal) t → ℝ := fun s => X s w-L s w
  let a : Ioc (0:NNReal) t → ℝ := fun s => g (((s:NNReal):ℝ), L s w)*z s^2/2
  have ha : Summable (fun s => |a s|) := ito43_weighted_series_summable X L w hc hl g hg t hs
  have h0 (s : Ioc (0:NNReal) t) (hz : z s = 0) : a s = 0 := by simp [a,hz]
  have hlim := ito43_cutoff_summable_series_limit a z ha h0
  have heq : (∫ y in Icc (0:ℝ) (t:ℝ) ×ˢ (univ : Set ℝ),
      g (y.1,L y.1.toNNReal w)*y.2^2/2 ∂(pathJumpMeasure X L w)) =
      ∑' s, a s := ito43_real_kernel_jump_series X L w hc hl
        (fun s x r => g (s,x)*r^2/2) (by intro s x; simp) t
  rw [heq]
  apply hlim.congr
  intro m
  exact (ito43_real_kernel_jump_series X L w hc hl
    (fun s x r => g (s,x)*r^2/2*min 1 (max 0 (abs r * ((m:ℝ)+1)-1)))
    (by intro s x; simp) t).symm
