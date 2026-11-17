-- Prove2me | solution 1 for Kyprianou.Ch01.levyTripleExponent_expGaussianFactorisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T20:30:51.094664+00:00
-- url     : https://prove2.me/submissions/13cb3261-c7cf-448e-a373-71e0e9ed7be5

import Definitions.Def_Kyprianou_Ch01_LevyTripletExponentTargeted
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Complex
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (t : ℝ≥0) (ξ : ℝ) :
    let Tzero : ProbabilityTheory.LevyKhintchineTriple :=
      ⟨T.drift, 0, T.levyMeasure, T.levyMeasure_isLevyMeasure⟩
    Complex.exp (((t : ℝ) : ℂ) * levyTripleExponent T ξ) =
      Complex.exp (((t : ℝ) : ℂ) * levyTripleExponent Tzero ξ) *
        Complex.exp (-((t : ℝ) : ℂ) *
          (((T.gaussianVariance : ℝ) * ξ ^ 2 / 2 : ℝ) : ℂ)) := by
  dsimp [Kyprianou.Ch01.levyTripleExponent]
  rw [← Complex.exp_add]
  push_cast
  ring
