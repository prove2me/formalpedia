-- Prove2me | solution 1 for MartOT.Card.lemma_1_11
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:22:11.828799+00:00
-- url     : https://prove2.me/submissions/51c6bf7a-16a9-4f64-8fc2-d95ace498646

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Theorems.Thm_MartOT_HN_lemma_1_11

open MeasureTheory

theorem solution (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) (c : ℝ → ℝ → ℝ) (hc : Measurable (Function.uncurry c))
    (hint : MartOT.Var.SuffIntegrable μ ν c) (π : Measure (ℝ × ℝ)) (hπ : MartOT.Var.IsOptimal c μ ν π)
    (hfin : MartOT.Var.cost c π < ⊤) :
    ∃ Γ : Set (ℝ × ℝ), MeasurableSet Γ ∧ π Γᶜ = 0 ∧
      ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), (↑S : Set (ℝ × ℝ)) ⊆ Γ →
        ∀ α' : Measure (ℝ × ℝ),
          MartOT.Var.IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
          MartOT.Var.cost c (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤ MartOT.Var.cost c α' :=
  MartOT.HN.lemma_1_11 μ ν hμν c hc hint π hπ hfin
