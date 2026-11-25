-- Prove2me | solution 1 for Kyprianou.Ch04.l2SquareIntegralLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:42:43.738683+00:00
-- url     : https://prove2.me/submissions/5012f2f2-98ab-4451-9769-d21a34a5c69e

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_l2NormSquareIntegralV1
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Convergence in L² implies convergence of the integrated squares. -/
theorem solution {α : Type} [MeasurableSpace α] (μ : Measure α)
    (f : ℕ → α → ℝ) (g : α → ℝ)
    (hf : ∀ n, MemLp (f n) 2 μ) (hg : MemLp g 2 μ)
    (h : Tendsto (fun n => eLpNorm (fun x => f n x - g x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, (f n x)^2 ∂μ) atTop (𝓝 (∫ x, (g x)^2 ∂μ)) := by
  haveI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let F : ℕ → Lp ℝ 2 μ := fun n => (hf n).toLp (f n)
  have hF : Tendsto F atTop (𝓝 (hg.toLp g)) := by
    apply Lp.tendsto_Lp_of_tendsto_eLpNorm g hg
    convert h using 1
    funext n
    apply eLpNorm_congr_ae
    filter_upwards [(hf n).coeFn_toLp] with x hx
    exact congrArg (fun v : ℝ => v - g x) hx
  have hnorm := hF.norm.pow 2
  have heq (n : ℕ) : ‖F n‖^2 = ∫ x, (f n x)^2 ∂μ := by
    rw [show F n = (hf n).toLp (f n) from rfl, Lp.norm_toLp,
      Kyprianou.Ch04.l2NormSquareIntegralV1 μ (f n) (hf n)]
  have hg' : ‖hg.toLp g‖^2 = ∫ x, (g x)^2 ∂μ := by
    rw [Lp.norm_toLp, Kyprianou.Ch04.l2NormSquareIntegralV1 μ g hg]
  simpa only [heq,hg'] using hnorm
