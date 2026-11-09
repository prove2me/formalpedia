-- Prove2me | solution 1 for KallMayerSLP.Bonferroni.binomial_moment_one_marginals
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T09:43:14.78557+00:00
-- url     : https://prove2.me/submissions/9c46f9e0-1c5c-48ef-9ef0-7979914ed459

import Mathlib
import Definitions.Def_KallMayerSLP_Bonferroni_binomialMoment
import Definitions.Def_KallMayerSLP_Bonferroni_lowerEvent
import Definitions.Def_KallMayerSLP_Bonferroni_exceedanceEvent
import Definitions.Def_KallMayerSLP_Bonferroni_marginalCDF

open MeasureTheory

open KallMayerSLP.Bonferroni in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {r : ℕ} (hr : 1 ≤ r) (ξ : Ω → Fin r → ℝ) (hξ : Measurable ξ) (x : Fin r → ℝ) :
    binomialMoment μ (exceedanceEvent ξ x) 1 = ∑ i, μ.real (exceedanceEvent ξ x i) ∧
    ∑ i, μ.real (exceedanceEvent ξ x i) = (r : ℝ) - ∑ i, μ.real (lowerEvent ξ x i) ∧
    (r : ℝ) - ∑ i, μ.real (lowerEvent ξ x i) = (r : ℝ) - ∑ i, marginalCDF μ ξ i (x i) := by
  refine ⟨?_, ?_, rfl⟩
  · unfold binomialMoment
    rw [Finset.powersetCard_one, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Function.Embedding.coeFn_mk, Finset.set_biInter_singleton]
  · have hmeas : ∀ i, MeasurableSet (lowerEvent ξ x i) := by
      intro i
      exact measurableSet_le ((measurable_pi_apply i).comp hξ) measurable_const
    have hcompl : ∀ i, exceedanceEvent ξ x i = (lowerEvent ξ x i)ᶜ := by
      intro i; ext ω; simp [exceedanceEvent, lowerEvent]
    simp only [hcompl, probReal_compl_eq_one_sub (hmeas _)]
    rw [Finset.sum_sub_distrib]
    simp
