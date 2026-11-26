-- Prove2me | solution 1 for Kyprianou.Ch05.exercise52CountMarkIndepV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:51:41.042551+00:00
-- url     : https://prove2.me/submissions/7b537233-d1de-4d10-9811-409f84faa3e6

import Mathlib
import Theorems.Thm_Kyprianou_Ch05_exercise52ArrivalMarkSequenceIndepV1
import Definitions.Def_levy_foundations_jumpCount
import Definitions.Def_levy_foundations_arrival
import Theorems.Thm_AvramDividend_Classical_avram_a06_compound_jumpCount_measurable_public
import Theorems.Thm_levy_foundations_iIndepFun_setRestrict_pairwiseDisjoint
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
/-- The arrival count is measurable and independent of the entire mark sequence. -/
theorem solution
    {Lambda : Type} [MeasurableSpace Lambda] (Q : Measure Lambda)
    [IsProbabilityMeasure Q] (arrival marks : ℕ → Lambda → ℝ)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : LevyFoundations.IsCompoundPoissonDriver arrival marks 1 F Q) (t : NNReal) :
    let N := fun w => LevyFoundations.jumpCount
      (fun n => LevyFoundations.arrival arrival n w) (t : ℝ)
    Measurable N ∧ IndepFun N (fun w n => marks n w) Q := by
  dsimp only
  have hN := AvramDividend.Classical.avram_a06_compound_jumpCount_measurable_public
    arrival hd.measurable_interarrival (t : ℝ)
  refine ⟨hN,?_⟩
  have hTY := exercise52ArrivalMarkSequenceIndepV1 Q arrival marks F hd
  have hj := AvramDividend.Classical.avram_a06_compound_jumpCount_measurable_public
    (fun j (z : ℕ → ℝ) => z j) (fun j => measurable_pi_apply j) (t : ℝ)
  exact hTY.comp hj measurable_id
