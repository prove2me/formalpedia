-- Prove2me | solution 1 for MarkovChainCLT.phiMixingCoef_le_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-04T23:17:26.867699+00:00
-- url     : https://prove2.me/submissions/4654dd0f-5648-48b1-8118-7fc60e226179

import Definitions.Def_MixingCoefficients

open MeasureTheory ProbabilityTheory MarkovChainCLT
open scoped ProbabilityTheory ENNReal

theorem solution
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → E) (n : ℕ) :
    phiMixingCoef P Y n ≤ 1 := by
  unfold phiMixingCoef
  apply csSup_le
  · -- nonempty: univ/univ gives element
    exact ⟨0, 0, Set.univ, Set.univ, MeasurableSet.univ, by simp, MeasurableSet.univ, by simp [measure_univ]⟩
  · intro r hr
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
