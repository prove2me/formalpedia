-- Prove2me | solution 1 for MartOT.Var.lemma_1_11
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T06:39:29.1335+00:00
-- url     : https://prove2.me/submissions/cdfd8058-079e-4c4d-9ac0-e17daf3f57d2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Theorems.Thm_MartOT_Var_theorem_3_1
import Theorems.Thm_MartOT_Var_badTuples_measurableSet
import Theorems.Thm_MartOT_Var_case_one_gives_Gamma_n
import Theorems.Thm_MartOT_Var_case_two_cannot_occur
import Theorems.Thm_MartOT_Var_gamma_iInter

open MeasureTheory MartOT.Var

theorem solution (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : ConvexLE μ ν) (c : ℝ → ℝ → ℝ) (hc : Measurable (Function.uncurry c))
    (hint : SuffIntegrable μ ν c) (π : Measure (ℝ × ℝ)) (hπ : IsOptimal c μ ν π)
    (hfin : cost c π < ⊤) :
    ∃ Γ : Set (ℝ × ℝ), MeasurableSet Γ ∧ π Γᶜ = 0 ∧
      ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), (↑S : Set (ℝ × ℝ)) ⊆ Γ →
        ∀ α' : Measure (ℝ × ℝ),
          IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
          cost c (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤ cost c α' := by
  haveI : IsProbabilityMeasure π := by
    constructor
    have h1 := hπ.1.1.1
    have : (π.map Prod.fst) Set.univ = π Set.univ := by
      rw [Measure.map_apply measurable_fst MeasurableSet.univ]; rfl
    rw [← this, h1, measure_univ]
  have key : ∀ n : ℕ, ∃ Γn : Set (ℝ × ℝ), MeasurableSet Γn ∧ π Γnᶜ = 0 ∧
      ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), S.card ≤ n →
        (↑S : Set (ℝ × ℝ)) ⊆ Γn → ∀ α' : Measure (ℝ × ℝ),
          IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
          cost c (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤ cost c α' := by
    intro n
    rcases theorem_3_1 π n (BadTuples c n) (badTuples_measurableSet c hc n) with
      ⟨Ms, hnull, hcover⟩ | hγ
    · obtain ⟨Γn, h1, h2, -, h4⟩ := case_one_gives_Gamma_n c π n Ms hnull hcover
      exact ⟨Γn, h1, h2, h4⟩
    · exact absurd hγ (case_two_cannot_occur μ ν hμν c hc hint π hπ hfin n)
  choose Γn hmeas hfull hopt using key
  obtain ⟨h1, h2, h3⟩ := gamma_iInter c π Γn hmeas hfull hopt
  exact ⟨⋂ n, Γn n, h1, h2, h3⟩
