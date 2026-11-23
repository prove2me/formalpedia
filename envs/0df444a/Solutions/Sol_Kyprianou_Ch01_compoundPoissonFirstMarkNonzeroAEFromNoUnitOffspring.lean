-- Prove2me | solution 1 for Kyprianou.Ch01.compoundPoissonFirstMarkNonzeroAEFromNoUnitOffspring
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:13:05.795344+00:00
-- url     : https://prove2.me/submissions/529cbf6f-972e-4a2a-a1dd-876a7fd05aaf

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (offspring : PMF ℕ) (hNoZeroJumps : offspring 1 = 0)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hJumpMass : ∀ k : ℕ,
      jumpLaw ({((k : ℝ) - 1)} : Set ℝ) = offspring k) :
    ∀ᵐ ω ∂Q, marks 0 ω ≠ 0 := by
  have hAtom : jumpLaw ({(0 : ℝ)} : Set ℝ) = 0 := by
    simpa [hNoZeroJumps] using hJumpMass 1
  have hMeas : MeasurableSet {ω : Ω | marks 0 ω = 0} :=
    (measurableSet_singleton (0 : ℝ)).preimage (hdriver.measurable_mark 0)
  have hLaw : Q {ω : Ω | marks 0 ω = 0} = 0 := by
    have heq := (hdriver.law_mark 0).measure_eq
      (p := fun z : ℝ => z = 0) (measurableSet_singleton (0 : ℝ))
    have hSet : ({z : ℝ | z = 0} : Set ℝ) = {(0 : ℝ)} := by
      ext z
      simp
    rw [hSet, hAtom] at heq
    exact heq
  apply (ae_iff).2
  simpa only [not_not] using hLaw
