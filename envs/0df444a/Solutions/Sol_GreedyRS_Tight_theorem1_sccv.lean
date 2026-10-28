-- Prove2me | solution 1 for GreedyRS.Tight.theorem1_sccv
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T10:40:44.659225+00:00
-- url     : https://prove2.me/submissions/f53987e9-7df1-4b8c-b034-52e926275487

import Mathlib
import Definitions.Def_GreedyRS_Tight_Setting
import Theorems.Thm_GreedyRS_Greedy_theorem1_sample_optimality
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : ℕ → ℝ) (v : ℕ → ℝ≥0) (X : ℕ → ℕ → Ω → ℝ) (hX : GreedyRS.Greedy.NormalArray P μ v X)
    (γ : ℝ) (hγ : 0 < γ) (hslip : ∀ i, 1 ≤ i → μ i = μ 0 - γ)
    (w : ℝ≥0) (hw : 0 < w) (hcv : ∀ i, v i = w)
    (c : ℝ) (hc : GreedyRS.Greedy.Cfun (γ / Real.sqrt w) < c) :
    (∃ γ0 ∈ Set.Ioo 0 γ, GreedyRS.Greedy.Cfun ((γ - γ0) / Real.sqrt w) = c) ∧
    ∀ γ0 ∈ Set.Ioo 0 γ, GreedyRS.Greedy.Cfun ((γ - γ0) / Real.sqrt w) = c →
      P {ω | GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) 1 (μ 0 - γ0)}
          ≤ Filter.liminf (fun k : ℕ => GreedyRS.Greedy.pcs P X k 1 ⌊c * k⌋₊) atTop ∧
      P {ω | GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) 1 (μ 0 - γ0)}
          = ENNReal.ofReal (1 / GreedyRS.Greedy.Cfun (γ0 / Real.sqrt w)) ∧
      0 < P {ω | GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) 1 (μ 0 - γ0)} := by
  have hv : ∀ i, 0 < v i := fun i => by rw [hcv i]; exact hw
  have hσ : 0 < Real.sqrt w := Real.sqrt_pos.2 (by exact_mod_cast hw)
  have hgap : ∀ i, 1 ≤ i → μ i ≤ μ 0 - γ := fun i hi => (hslip i hi).le
  have hvar : ∀ i, (v i : ℝ) ≤ Real.sqrt w ^ 2 := fun i => by
    rw [hcv i, Real.sq_sqrt (NNReal.coe_nonneg w)]
  obtain ⟨hex, h⟩ := GreedyRS.Greedy.theorem1_sample_optimality P μ v X hX hv γ (Real.sqrt w)
    hγ hσ hgap hvar c hc
  refine ⟨hex, fun γ0 hγ0 hC0 => ?_⟩
  have := h γ0 hγ0 hC0
  rw [hcv 0] at this
  exact this
