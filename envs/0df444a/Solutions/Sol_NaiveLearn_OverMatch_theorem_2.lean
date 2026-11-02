-- Prove2me | solution 1 for NaiveLearn.OverMatch.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T12:39:46.950122+00:00
-- url     : https://prove2.me/submissions/7e281699-4450-4df6-9da8-c60e4e6ad44c

import Mathlib
import Definitions.Def_NaiveLearn_OverMatch_Model
import Theorems.Thm_NaiveLearn_OverMatch_corollary_1
import Theorems.Thm_NaiveLearn_OverMatch_weighted_lln

open MeasureTheory ProbabilityTheory Filter Topology
open NaiveLearn.OverMatch

theorem solution (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    {S : Type*} [MeasurableSpace S] (F0 F1 : Measure S)
    [IsProbabilityMeasure F0] [IsProbabilityMeasure F1] (hF : F0 ≠ F1)
    (σ : ℝ → ℝ → ℝ) (hσ : IsExtremizationFamily p σ)
    (n : ℕ → ℕ) (W : ∀ k, Matrix (Fin (n k)) (Fin (n k)) ℝ) (μ : ∀ k, Fin (n k) → ℝ)
    (hW : ∀ k, IsWeightMatrix (W k)) (hμ : ∀ k, IsCentrality (W k) (μ k))
    (hvan : Tendsto (fun k => ⨆ i, μ k i) atTop (𝓝 0)) :
    ∃ ε δ : ℕ → ℝ, (∀ k, ε k ∈ Set.Ioc (0 : ℝ) 1 ∧ δ k ∈ Set.Ioc (0 : ℝ) 1) ∧
      ∃ η : ℕ → ℝ, Tendsto η atTop (𝓝 0) ∧
        ∀ k, NaiveLearning (η k) (σ (δ k)) (ε k) p (W k) F0 F1 := by
  have hc : ∀ k, ∃ δ ∈ Set.Ioc (0 : ℝ) 1, ∃ ε ∈ Set.Ioc (0 : ℝ) 1,
      NaiveLearning (1 - lGF p F0 F1 (μ k) + 1 / ((k : ℝ) + 1)) (σ δ) ε p (W k) F0 F1 := by
    intro k
    exact corollary_1 p hp0 hp1 F0 F1 σ hσ (W k) (μ k) (hW k) (hμ k) _
      (by positivity)
  choose δ hδ ε hε hL using hc
  refine ⟨ε, δ, fun k => ⟨hε k, hδ k⟩,
    fun k => 1 - lGF p F0 F1 (μ k) + 1 / ((k : ℝ) + 1), ?_, hL⟩
  obtain ⟨h1, h0⟩ := weighted_lln p hp0 hp1 F0 F1 hF n μ (fun k => (hμ k).1)
    (fun k => (hμ k).2.1) hvan
  have h1' := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h1
  have h0' := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h0
  have hl : Tendsto (fun k => lGF p F0 F1 (μ k)) atTop (𝓝 1) := by
    have := (h1'.const_mul p).add (h0'.const_mul (1 - p))
    simp only [ENNReal.toReal_one, mul_one, add_sub_cancel] at this
    exact this
  have hr : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have := (tendsto_const_nhds (x := (1 : ℝ))).sub hl |>.add hr
  simpa using this
