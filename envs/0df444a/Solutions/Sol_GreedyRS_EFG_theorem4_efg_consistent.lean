-- Prove2me | solution 1 for GreedyRS.EFG.theorem4_efg_consistent
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T10:19:42.171803+00:00
-- url     : https://prove2.me/submissions/29c6c35c-134b-488c-b49d-9dda4242d82e

import Mathlib
import Definitions.Def_GreedyRS_EFG_Setting
import Theorems.Thm_GreedyRS_EFG_theorem3_efg_sample_optimality
import Theorems.Thm_GreedyRS_EFG_lemma7_C_continuous_antitone

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (μ : ℕ → ℝ) (v : ℕ → ℝ≥0) (X : ℕ → ℕ → Ω → ℝ)
    (hX : GreedyRS.Greedy.NormalArray P μ v X) (hv : ∀ i, 0 < v i)
    (γ σbar : ℝ) (hγ : 0 < γ) (hσbar : 0 < σbar)
    (hgap : ∀ i, 1 ≤ i → μ i ≤ μ 0 - γ) (hvar : ∀ i, (v i : ℝ) ≤ σbar ^ 2)
    (α : ℝ) (hα : α ∈ Set.Ioo 0 1)
    (γ0 : ℝ) (hγ0 : γ0 ∈ Set.Ioo 0 γ) (n0 : ℕ) (hn0 : 1 ≤ n0)
    (h53 : ENNReal.ofReal α ≤
      P {ω | GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) n0 (μ 0 - γ0)})
    (ng : ℝ) (hng : GreedyRS.Greedy.Cn0 ((γ - γ0) / σbar) n0 ≤ ENNReal.ofReal (n0 + ng)) :
    ENNReal.ofReal α ≤
      Filter.liminf (fun k : ℕ => GreedyRS.Greedy.pcs P X k n0 ⌊((n0 : ℝ) + ng) * k⌋₊) Filter.atTop := by
  obtain ⟨hanti, -⟩ := GreedyRS.EFG.lemma7_C_continuous_antitone n0 hn0
  have hx0 : (0:ℝ) < (γ - γ0) / σbar := div_pos (by linarith [hγ0.2]) hσbar
  have hx1 : (γ - γ0) / σbar < γ / σbar := by
    apply div_lt_div_of_pos_right _ hσbar; linarith [hγ0.1]
  have hlt : GreedyRS.Greedy.Cn0 (γ / σbar) n0 < ENNReal.ofReal (n0 + ng) :=
    lt_of_lt_of_le (hanti (Set.mem_Ioi.2 hx0) (Set.mem_Ioi.2 (hx0.trans hx1)) hx1) hng
  obtain ⟨⟨γ0', hγ0', heq⟩, hall⟩ :=
    GreedyRS.EFG.theorem3_efg_sample_optimality P μ v X hX hv γ σbar hγ hσbar hgap hvar n0 hn0 ng hlt
  have hle : γ0 ≤ γ0' := by
    by_contra hcon
    push_neg at hcon
    have hx' : (γ - γ0) / σbar < (γ - γ0') / σbar := by
      apply div_lt_div_of_pos_right _ hσbar; linarith
    have := hanti (Set.mem_Ioi.2 hx0) (Set.mem_Ioi.2 (hx0.trans hx')) hx'
    have h2 : GreedyRS.Greedy.Cn0 ((γ - γ0') / σbar) n0 < GreedyRS.Greedy.Cn0 ((γ - γ0) / σbar) n0 := this
    rw [heq] at h2
    exact absurd (lt_of_lt_of_le h2 hng) (lt_irrefl _)
  have hsub : {ω | GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) n0 (μ 0 - γ0)}
      ⊆ {ω | GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) n0 (μ 0 - γ0')} := by
    intro ω hω
    exact ⟨hω.1, lt_of_le_of_lt (by linarith) hω.2⟩
  exact h53.trans ((measure_mono hsub).trans (hall γ0' hγ0' heq))
