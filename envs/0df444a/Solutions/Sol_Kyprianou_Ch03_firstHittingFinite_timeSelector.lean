-- Prove2me | solution 1 for Kyprianou.Ch03.firstHittingFinite_timeSelector
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T17:32:18.578993+00:00
-- url     : https://prove2.me/submissions/4c4b9a86-c92c-4709-9dee-a5b3b88bd68d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch03

theorem solution
    {Omega : Type} (X : NNReal → Omega → ℝ)
    (B : Set ℝ) :
    ∃ f : Omega → NNReal,
      ∀ omega : Omega,
        (firstHittingTime X B omega != ⊤) →
          firstHittingTime X B omega = (f omega : WithTop NNReal) := by
  classical
  have hTime (omega : Omega) :
      ∃ t : NNReal,
        firstHittingTime X B omega ≠ ⊤ →
          firstHittingTime X B omega =
            (t : WithTop NNReal) := by
    by_cases h : firstHittingTime X B omega = ⊤
    · exact ⟨0, by simp [h]⟩
    · obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp h
      refine ⟨t, fun _ => ?_⟩
      first | exact ht | exact ht.symm
  refine ⟨fun omega => Classical.choose (hTime omega), ?_⟩
  refine fun omega h => ?_
  by_cases ht : firstHittingTime X B omega = ⊤
  · simp [ht] at h
  · exact Classical.choose_spec (hTime omega) ht
