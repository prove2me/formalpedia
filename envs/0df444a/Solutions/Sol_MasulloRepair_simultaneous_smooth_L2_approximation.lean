-- Prove2me | solution 1 for MasulloRepair.simultaneous_smooth_L2_approximation
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T14:58:30.187776+00:00
-- url     : https://prove2.me/submissions/67491d9f-9aca-47e7-a10a-0db3b02597a8

import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

theorem solution (μ : ℕ → Measure ℝ)
    [∀ n, IsFiniteMeasureOnCompacts (μ n)] (hμ : Monotone μ)
    (f : ℝ → ℂ) (hf : ∀ n, MemLp f 2 (μ n)) :
    ∃ g : ℕ → ℝ → ℂ,
      (∀ k, HasCompactSupport (g k) ∧ ContDiff ℝ ∞ (g k)) ∧
      (∀ n k, MemLp (g k) 2 (μ n)) ∧
      ∀ n, Tendsto (fun k => eLpNorm (f - g k) 2 (μ n)) atTop (𝓝 0) := by
  have ha (k : ℕ) : ∃ g : ℝ → ℂ,
      HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
        eLpNorm (f - g) 2 (μ k) ≤ ENNReal.ofReal (1 / ((k : ℝ) + 1)) :=
    (hf k).exist_eLpNorm_sub_le (by norm_num) (by norm_num) (by positivity)
  choose g hg using ha
  refine ⟨g, fun k => ⟨(hg k).1, (hg k).2.1⟩,
    fun n k => (hg k).2.1.continuous.memLp_of_hasCompactSupport (hg k).1, ?_⟩
  intro n
  have ht : Tendsto (fun k : ℕ => ENNReal.ofReal (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [one_div, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · exact Eventually.of_forall fun _ => bot_le
  · filter_upwards [eventually_ge_atTop n] with k hk
    exact (eLpNorm_mono_measure (f - g k) (hμ hk)).trans (hg k).2.2

#print axioms solution
