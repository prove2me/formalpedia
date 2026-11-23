-- Prove2me | solution 1 for Kyprianou.Ch01.compoundPoissonFirstMarkOffspringSupportAE
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:16:06.285137+00:00
-- url     : https://prove2.me/submissions/98010a7a-1f0b-47e2-b14c-1933c14a5c9f

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (rate : ℝ≥0) (hrate : 0 < rate)
    (arrival marks : ℕ → Ω → ℝ)
    (jumpLaw : Measure ℝ) [IsProbabilityMeasure jumpLaw]
    (hdriver : IsCompoundPoissonDriver arrival marks rate jumpLaw Q)
    (hSupport : jumpLaw
      {x : ℝ | ∃ j : ℕ, x = (j : ℝ) - 1} = 1) :
    ∀ᵐ ω ∂Q, ∃ j : ℕ, marks 0 ω = (j : ℝ) - 1 := by
  have hs : MeasurableSet
      {x : ℝ | ∃ j : ℕ, x = (j : ℝ) - 1} := by
    apply Set.Countable.measurableSet
    have hc : Set.Countable
        (Set.range (fun j : ℕ => (j : ℝ) - 1)) :=
      Set.countable_range _
    apply hc.mono
    rintro x ⟨j, hj⟩
    exact ⟨j, hj.symm⟩
  have hLaw :
      Q {ω | ∃ j : ℕ, marks 0 ω = (j : ℝ) - 1} = 1 := by
    have heq := (hdriver.law_mark 0).measure_eq
      (p := fun z : ℝ => ∃ j : ℕ, z = (j : ℝ) - 1) hs
    simpa only [hSupport] using heq
  have hMeas : MeasurableSet
      {ω : Ω | ∃ j : ℕ, marks 0 ω = (j : ℝ) - 1} := by
    simpa only [Set.preimage, Set.mem_setOf_eq] using
      hs.preimage (hdriver.measurable_mark 0)
  apply (ae_iff).2
  have hComp := measure_compl hMeas (measure_ne_top Q _)
  simpa [Set.compl_setOf, hLaw] using hComp
