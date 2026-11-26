-- Prove2me | solution 1 for Kyprianou.Ch05.exercise52CPDriverLevyVersionV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:48:45.999955+00:00
-- url     : https://prove2.me/submissions/d242756a-c68e-451d-9dc0-9b5dc125f3ea

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a06_compoundPoissonStartsZeroAE_public
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonOfMeasurableSequences
import Theorems.Thm_Kyprianou_Ch05_exercise52CPDriverStationaryV1
import Theorems.Thm_Kyprianou_Ch01_aggregateClaims_hasIndependentIncrements
import Theorems.Thm_Kyprianou_Ch01_riskSurplus_isCadlag_ae
import Theorems.Thm_Kyprianou_Ch01_cadlag_nnreal_neg
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
/-- A compound Poisson driver admits a measurable Levy version with the same whole-path law. -/
theorem solution
    {Lambda : Type} [MeasurableSpace Lambda] (Q : Measure Lambda)
    [IsProbabilityMeasure Q] (arrival marks : ℕ → Lambda → ℝ)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : LevyFoundations.IsCompoundPoissonDriver arrival marks 1 F Q) :
    ∃ Z : NNReal → Lambda → ℝ, IsLevyProcess Z Q ∧
      (∀ t, Measurable (Z t)) ∧
      (∀ᵐ w ∂Q, ∀ t : NNReal, Z t w =
        ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) w) := by
  let R : NNReal → Lambda → ℝ := fun t w =>
    ProbabilityTheory.compoundPoisson 0 arrival marks (t : ℝ) w
  let Z : NNReal → Lambda → ℝ := fun t w => R t w - R 0 w
  have hd' : ProbabilityTheory.IsCompoundPoissonDriver arrival marks 1 F Q :=
    ⟨hd.measurable_interarrival,hd.measurable_mark,hd.indep,hd.law_interarrival,hd.law_mark⟩
  have h0 : ∀ᵐ w ∂Q, R 0 w = 0 :=
    AvramDividend.Classical.avram_a06_compoundPoissonStartsZeroAE_public hd one_pos 0
  have heq : ∀ᵐ w ∂Q, ∀ t, Z t w = R t w := by
    filter_upwards [h0] with w hw t
    simp [Z,hw]
  have hm (t : NNReal) : Measurable (R t) :=
    (Kyprianou.Ch01.compoundPoissonOfMeasurableSequences arrival marks
      hd.measurable_interarrival hd.measurable_mark).comp (measurable_id.prodMk measurable_const)
  have hinc (s t : NNReal) : increment Z s t = increment R s t := by
    funext w
    simp only [increment,Z]
    ring
  refine ⟨Z,⟨by funext w; simp [Z],?_,?_,?_⟩,fun t => (hm t).sub (hm 0),heq⟩
  · intro n g hg
    simp only [hinc]
    exact Kyprianou.Ch01.aggregateClaims_hasIndependentIncrements Q arrival marks 1 one_pos F hd' n g hg
  · intro s t
    rw [hinc,hinc]
    exact exercise52CPDriverStationaryV1 Q arrival marks F hd s t
  · filter_upwards [heq,Kyprianou.Ch01.riskSurplus_isCadlag_ae Q arrival marks 1 F hd'
      one_pos 0 0] with w hw hc
    have hh := Kyprianou.Ch01.cadlag_nnreal_neg _ hc
    have hfun : (fun t => Z t w) = (fun t => -Kyprianou.Ch01.riskSurplus arrival marks 0 0 t w) := by
      funext t
      simp [hw,R,Kyprianou.Ch01.riskSurplus,Kyprianou.Ch01.aggregateClaims]
    rw [hfun]
    exact hh
