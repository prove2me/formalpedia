-- Prove2me | solution 1 for Kyprianou.Ch03.positiveHitInfDelayedClosedV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:02:56.042809+00:00
-- url     : https://prove2.me/submissions/1dda63a2-f01e-426e-b2bc-3b1d712734a0

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false


theorem solution
    {Omega : Type} (X : NNReal → Omega → ℝ) (B : Set ℝ) (w : Omega) :
    Kyprianou.Ch03.firstHittingTime X B w =
      ⨅ j : ℕ, sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 1 / ((j : NNReal) + 1) ≤ t ∧ X t w ∈ B}) := by
  unfold Kyprianou.Ch03.firstHittingTime
  apply le_antisymm
  · apply le_iInf
    intro j
    apply le_sInf
    rintro _ ⟨t, ⟨ht, hB⟩, rfl⟩
    exact sInf_le ⟨t, ⟨(show 0 < 1 / ((j : NNReal) + 1) by positivity).trans_le ht, hB⟩, rfl⟩
  · apply le_sInf
    rintro _ ⟨t, ⟨ht, hB⟩, rfl⟩
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt ht
    exact (iInf_le _ j).trans (sInf_le ⟨t, ⟨hj.le, hB⟩, rfl⟩)
