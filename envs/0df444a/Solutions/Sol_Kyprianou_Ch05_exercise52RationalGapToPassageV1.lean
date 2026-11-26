-- Prove2me | solution 1 for Kyprianou.Ch05.exercise52RationalGapToPassageV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:29:25.631256+00:00
-- url     : https://prove2.me/submissions/ffbd01e4-91e0-44d2-9b9a-c4652afb7561

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_exercise52RationalGapAllTimesV1
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

open Topology
/-- A rational gap gives both strict passage margins at the first passage. -/
theorem solution
    (Y L : NNReal → ℝ) (hm : Monotone Y)
    (s : NNReal) (hs0 : 0 < s)
    (hl : Tendsto Y (nhdsWithin s (Iio s)) (nhds (L s)))
    (x u y : ℝ) (hx : 0 < x) (hu : 0 < u) (hy : 0 < y)
    (hr : ∀ t, ContinuousWithinAt Y (Ici t) t)
    (hpre : ∀ t, t < s → Y t ≤ x) (hat : x ≤ Y s)
    (hgap : (∃ a b : ℚ, (a : ℝ) < x-y ∧ x+u < (b : ℝ) ∧
      (∀ q : ℚ, Y (Real.toNNReal q) ≤ (a : ℝ) ∨ (b : ℝ) ≤ Y (Real.toNNReal q)) ∧
      ∃ q : ℚ, (b : ℝ) ≤ Y (Real.toNNReal q))) :
    u < Y s - x ∧ y < x - L s := by
  obtain ⟨a,b,ha,hb,hg,q,hq⟩ := hgap
  have hg' := exercise52RationalGapAllTimesV1 Y hr a b |>.2 hg
  have hhigh : (b : ℝ) ≤ Y s := by
    rcases hg' s with h | h
    · exfalso; linarith
    · exact h
  letI : (nhdsWithin s (Iio s)).NeBot :=
    nhdsWithin_Iio_neBot' ⟨0, hs0⟩ le_rfl
  have hlow : L s ≤ (a : ℝ) := by
    apply le_of_tendsto hl
    filter_upwards [self_mem_nhdsWithin] with v hv
    rcases hg' v with h | h
    · exact h
    · exfalso; linarith [hpre v hv]
  constructor <;> linarith
