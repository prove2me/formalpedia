-- Prove2me | solution 1 for Kyprianou.Ch05.exercise52CPDriverStationaryV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:54:58.657226+00:00
-- url     : https://prove2.me/submissions/fa06a5af-80be-4b14-b339-2620b5cc6632

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoissonStartsZeroAE_public
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonOfMeasurableSequences
import Theorems.Thm_Kyprianou_Ch06_stationaryIncrementsFromMarginalLaw
import Theorems.Thm_Kyprianou_Ch01_riskSurplus_increment_stationary
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
/-- The driftless compound Poisson driver has stationary increments. -/
theorem solution
    {Lambda : Type} [MeasurableSpace Lambda] (Q : Measure Lambda)
    [IsProbabilityMeasure Q] (arrival marks : ℕ → Lambda → ℝ)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : LevyFoundations.IsCompoundPoissonDriver arrival marks 1 F Q) :
    HasStationaryIncrements (fun (t : NNReal) w =>
      ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) w) Q := by
  let R : NNReal → Lambda → ℝ := fun t w =>
    ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) w
  have hd' : ProbabilityTheory.IsCompoundPoissonDriver arrival marks 1 F Q :=
    ⟨hd.measurable_interarrival,hd.measurable_mark,hd.indep,hd.law_interarrival,hd.law_mark⟩
  have h0 : ∀ᵐ w ∂Q, R 0 w = 0 :=
    AvramDividend.Classical.avram_a06_compoundPoissonStartsZeroAE_public hd one_pos 0
  have hm (t : NNReal) : Measurable (R t) :=
    (Kyprianou.Ch01.compoundPoissonOfMeasurableSequences arrival marks
      hd.measurable_interarrival hd.measurable_mark).comp (measurable_id.prodMk measurable_const)
  apply Kyprianou.Ch06.stationaryIncrementsFromMarginalLaw Q R hm h0
  intro s t
  have h := Kyprianou.Ch01.riskSurplus_increment_stationary Q arrival marks 1 one_pos
    F hd' 0 s (s+t) (le_add_of_nonneg_right bot_le)
  have hsur (u : NNReal) : Measurable (Kyprianou.Ch01.riskSurplus arrival marks 0 0 u) := by
    have he : Kyprianou.Ch01.riskSurplus arrival marks 0 0 u = fun w => -R u w := by
      funext w
      simp [Kyprianou.Ch01.riskSurplus,Kyprianou.Ch01.aggregateClaims,R]
    rw [he]
    exact (hm u).neg
  have h' := congrArg (Measure.map (fun x : ℝ => -x)) h
  have hmneg : Measurable (fun x : ℝ => -x) := measurable_neg
  have hmI : Measurable (fun w =>
      Kyprianou.Ch01.riskSurplus arrival marks 0 0 (s+t) w -
      Kyprianou.Ch01.riskSurplus arrival marks 0 0 s w) := (hsur (s+t)).sub (hsur s)
  rw [Measure.map_map hmneg hmI, Measure.map_map hmneg (hsur (s+t-s))] at h'
  simpa [Function.comp_def,Kyprianou.Ch01.riskSurplus,Kyprianou.Ch01.aggregateClaims,
    R,neg_sub_neg,add_tsub_cancel_left,sub_eq_add_neg,add_comm] using h'
