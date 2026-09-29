-- Prove2me | solution 1 for MarkovChainCLT.alphaMixingCoef_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-04T23:37:09.377881+00:00
-- url     : https://prove2.me/submissions/f1007c3a-3d62-40cc-8734-65af18a5beae

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n : ℕ) :
    0 ≤ alphaMixingCoef P Y n := by
  have h0mem : (0 : ℝ) ∈ {r | ∃ k' : ℕ, ∃ A' B' : Set Ω,
      MeasurableSet[processSigma Y (Set.Iic k')] A' ∧
      MeasurableSet[processSigma Y (Set.Ici (k' + n))] B' ∧
      r = |(P (A' ∩ B')).toReal - (P A').toReal * (P B').toReal|} := by
    refine ⟨0, Set.univ, Set.univ, MeasurableSet.univ, MeasurableSet.univ, ?_⟩
    simp [measure_univ]
  have hbdd : BddAbove {r | ∃ k' : ℕ, ∃ A' B' : Set Ω,
      MeasurableSet[processSigma Y (Set.Iic k')] A' ∧
      MeasurableSet[processSigma Y (Set.Ici (k' + n))] B' ∧
      r = |(P (A' ∩ B')).toReal - (P A').toReal * (P B').toReal|} := by
    use 1
    intro r hr
    obtain ⟨k', A', B', _, _, rfl⟩ := hr
    have h1 : (P (A' ∩ B')).toReal ≤ 1 := by
      have h : P (A' ∩ B') ≤ 1 := by
        calc P (A' ∩ B') ≤ P Set.univ := measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
      exact ENNReal.toReal_mono (by simp) h
    have h2 : (P A').toReal * (P B').toReal ≤ 1 := by
      have hA1 : (P A').toReal ≤ 1 := by
        have h : P A' ≤ 1 := by
          calc P A' ≤ P Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
        exact ENNReal.toReal_mono (by simp) h
      have hB1 : (P B').toReal ≤ 1 := by
        have h : P B' ≤ 1 := by
          calc P B' ≤ P Set.univ := measure_mono (Set.subset_univ _)
            _ = 1 := measure_univ
        exact ENNReal.toReal_mono (by simp) h
      have nnB : 0 ≤ (P B').toReal := ENNReal.toReal_nonneg
      calc (P A').toReal * (P B').toReal ≤ 1 * 1 :=
            mul_le_mul hA1 hB1 nnB (by linarith)
        _ = 1 := one_mul 1
    have nn1 : 0 ≤ (P (A' ∩ B')).toReal := ENNReal.toReal_nonneg
    have nn2 : 0 ≤ (P A').toReal * (P B').toReal :=
      mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    rw [abs_le]
    constructor <;> linarith
  unfold alphaMixingCoef
  exact le_csSup hbdd h0mem
