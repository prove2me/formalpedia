-- Prove2me | solution 1 for Kyprianou.Ch03.temperedStableZeroGaussianProcessExistsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T18:03:20.667846+00:00
-- url     : https://prove2.me/submissions/449d95a8-fd89-45a3-aa46-5698dd78f424

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Theorems.Thm_levy_foundations_existsPureJumpProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (T : LevyKhintchineTriple) (hzero : T.gaussianVariance = 0) :
    ∃ (Omega : Type) (m : MeasurableSpace Omega),
      letI : MeasurableSpace Omega := m
      ∃ (P : Measure Omega) (X : NNReal → Omega → ℝ),
        IsProbabilityMeasure P ∧ IsLevyProcess X P ∧
        (∀ t, Measurable (X t)) ∧
        ∀ (t : NNReal) (xi : ℝ),
          charFun (P.map (X t)) xi =
            Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent T xi) := by
  have hn : LevyFoundations.isLevyMeasure T.levyMeasure := T.levyMeasure_isLevyMeasure
  obtain ⟨Omega, m, P, X, hp, hx, hm, hchar⟩ :=
    levy_foundations_existsPureJumpProcess T.drift hn
  letI := m
  have hx' : IsLevyProcess X P :=
    ⟨hx.start_zero, hx.indep_increments, hx.stationary_increments, hx.cadlag_ae⟩
  refine ⟨Omega, m, P, X, hp, hx', hm, ?_⟩
  intro t xi
  have he : LevyFoundations.exponent ⟨T.drift, 0, T.levyMeasure, hn⟩ xi =
      Kyprianou.Ch01.levyTripleExponent T xi := by
    simp [LevyFoundations.exponent, Kyprianou.Ch01.levyTripleExponent, hzero,
      LevyFoundations.compensatedIntegrand, ProbabilityTheory.levyCompensatedIntegrand]
    <;> ring
  simpa only [he] using hchar t xi
