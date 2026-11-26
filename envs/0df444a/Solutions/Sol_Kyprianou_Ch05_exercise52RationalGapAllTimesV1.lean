-- Prove2me | solution 1 for Kyprianou.Ch05.exercise52RationalGapAllTimesV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:23:52.177923+00:00
-- url     : https://prove2.me/submissions/97b2af35-5fdf-4757-b497-5cf9d1ce34e9

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_openHitLtRationalWitness
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Definitions.Def_Kyprianou_Ch05_RenewalEpochProcess
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch05_RiskConditionalPassage
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Set
open Kyprianou.Ch05
/-- A right-continuous path avoids a real open interval iff its rational samples avoid it. -/
theorem solution
    (Y : NNReal → ℝ) (hr : ∀ t, ContinuousWithinAt Y (Ici t) t)
    (a b : ℝ) :
    (∀ t : NNReal, Y t ≤ a ∨ b ≤ Y t) ↔
      (∀ q : ℚ, Y (Real.toNNReal q) ≤ a ∨ b ≤ Y (Real.toNNReal q)) := by
  constructor
  · intro h q
    exact h _
  · intro h t
    by_contra! hn
    have hh : Y t ∈ Ioo a b := ⟨hn.1, hn.2⟩
    have hlt : (sInf {v : WithTop NNReal | ∃ r : NNReal,
      v = ↑r ∧ Y r ∈ Ioo a b}) < ((t + 1 : NNReal) : WithTop NNReal) := by
      have hm : (t : WithTop NNReal) ∈ {v : WithTop NNReal |
        ∃ r : NNReal, v = ↑r ∧ Y r ∈ Ioo a b} := ⟨t, rfl, hh⟩
      exact (sInf_le hm).trans_lt (WithTop.coe_lt_coe.mpr (lt_add_of_pos_right t zero_lt_one))
    obtain ⟨q, _, _, hq⟩ := (Kyprianou.Ch04.openHitLtRationalWitness Y
      (Ioo a b) isOpen_Ioo hr (t+1)).mp hlt
    rcases h q with hq' | hq'
    · exact (not_lt_of_ge hq') hq.1
    · exact (not_lt_of_ge hq') hq.2
