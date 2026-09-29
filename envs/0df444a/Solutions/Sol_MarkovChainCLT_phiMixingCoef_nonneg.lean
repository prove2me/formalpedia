-- Prove2me | solution 1 for MarkovChainCLT.phiMixingCoef_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-04T23:17:26.375546+00:00
-- url     : https://prove2.me/submissions/c4006d46-3ca9-4ccb-91e4-d0a85c94fdb8

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n : ℕ) :
    0 ≤ phiMixingCoef P Y n := by
  have h0mem : (0 : ℝ) ∈ {r | ∃ k' : ℕ, ∃ A' B' : Set Ω,
      MeasurableSet[processSigma Y (Set.Iic k')] A' ∧ P A' ≠ 0 ∧
      MeasurableSet[processSigma Y (Set.Ici (k' + n))] B' ∧
      r = |(P (A' ∩ B')).toReal / (P A').toReal - (P B').toReal|} := by
    refine ⟨0, Set.univ, Set.univ, MeasurableSet.univ, ?_, MeasurableSet.univ, ?_⟩
    · simp
    · simp [measure_univ]
  have hbdd : BddAbove {r | ∃ k' : ℕ, ∃ A' B' : Set Ω,
      MeasurableSet[processSigma Y (Set.Iic k')] A' ∧ P A' ≠ 0 ∧
      MeasurableSet[processSigma Y (Set.Ici (k' + n))] B' ∧
      r = |(P (A' ∩ B')).toReal / (P A').toReal - (P B').toReal|} := by
    use 1
    intro r hr
    obtain ⟨k', A', B', _, hA'0, _, rfl⟩ := hr
    have h1 : (P B').toReal ≤ 1 := by
      have h : P B' ≤ 1 := by
        calc P B' ≤ P Set.univ := measure_mono (Set.subset_univ B')
          _ = 1 := measure_univ
      exact ENNReal.toReal_mono (by simp) h
    have h2 : (P (A' ∩ B')).toReal / (P A').toReal ≤ 1 := by
      have hsub2 : P (A' ∩ B') ≤ P A' := measure_mono Set.inter_subset_left
      have hle : (P (A' ∩ B')).toReal ≤ (P A').toReal :=
        ENNReal.toReal_mono (measure_ne_top P _) hsub2
      have hpos : 0 < (P A').toReal := ENNReal.toReal_pos hA'0 (measure_ne_top P _)
      rw [div_le_one hpos]
      exact hle
    have hnn1 : 0 ≤ (P B').toReal := ENNReal.toReal_nonneg
    have hnn2 : 0 ≤ (P (A' ∩ B')).toReal / (P A').toReal := by positivity
    rw [abs_le]
    constructor <;> linarith
  unfold phiMixingCoef
  exact le_csSup hbdd h0mem
