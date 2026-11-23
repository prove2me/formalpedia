-- Prove2me | solution 1 for Kyprianou.Ch01.compoundPoissonDriverJointInfinitePiLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:10:20.805189+00:00
-- url     : https://prove2.me/submissions/d4f21384-e301-4cc8-b646-edeb0d62d342

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q) :
    HasLaw (fun w (i : ℕ ⊕ ℕ) => (Sum.elim arrival marks i) w)
      (Measure.infinitePi
        (Sum.elim (fun _ : ℕ => expMeasure rate)
                  (fun _ : ℕ => jumpLaw))) Q := by
  classical
  apply ProbabilityTheory.iIndepFun.hasLaw_infinitePi
  · intro i
    cases i with
    | inl n => exact hdriver.law_interarrival n
    | inr n => exact hdriver.law_mark n
  · exact hdriver.indep
  · apply Measurable.aemeasurable
    apply measurable_pi_lambda
    intro i
    cases i with
    | inl n => exact hdriver.measurable_interarrival n
    | inr n => exact hdriver.measurable_mark n
