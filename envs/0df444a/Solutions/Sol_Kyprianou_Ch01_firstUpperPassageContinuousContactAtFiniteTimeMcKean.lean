-- Prove2me | solution 1 for Kyprianou.Ch01.firstUpperPassageContinuousContactAtFiniteTimeMcKean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T15:20:13.242449+00:00
-- url     : https://prove2.me/submissions/82d069b2-af56-4dc1-8a29-bbd4c8224448

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_continuousFirstUpperContactFromBelowPublic

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Y : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (s : ℝ) (hs : 0 < s)
    (hContinuous : Continuous (fun t : ℝ≥0 => Y t ω))
    (hStart : Y 0 ω = 0)
    (t : ℝ≥0)
    (hPass : firstUpperPassage Y s ω = (t : WithTop ℝ≥0)) :
    Y t ω = s := by
  classical
  have hstart : Y 0 ω < s := by
    rw [hStart]
    exact hs
  by_cases hex : ∃ u : ℝ≥0, 0 < u ∧ s < Y u ω
  · have hdef :
        firstUpperPassage Y s ω =
          ((sInf {u : ℝ≥0 | 0 < u ∧ s < Y u ω} : ℝ≥0) :
            WithTop ℝ≥0) := by
      unfold firstUpperPassage
      simp only [if_pos hex]
    rw [hdef] at hPass
    have ht :
        sInf {u : ℝ≥0 | 0 < u ∧ s < Y u ω} = t :=
      WithTop.coe_inj.mp hPass
    rw [← ht]
    exact Kyprianou.Ch01.continuousFirstUpperContactFromBelowPublic
      (fun u : ℝ≥0 => Y u ω) hContinuous s hstart hex
  · have hdef : firstUpperPassage Y s ω = ⊤ := by
      unfold firstUpperPassage
      simp only [if_neg hex]
    rw [hdef] at hPass
    cases hPass
