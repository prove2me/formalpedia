-- Prove2me | solution 1 for Kyprianou.Ch01.levyTripleExponent_gaussianSplit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T20:25:53.848054+00:00
-- url     : https://prove2.me/submissions/30ee5976-ddcb-443a-9af3-639165941ac1

import Definitions.Def_Kyprianou_Ch01_LevyTripletExponentTargeted
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (T : ProbabilityTheory.LevyKhintchineTriple) (ξ : ℝ) :
    let Tzero : ProbabilityTheory.LevyKhintchineTriple :=
      ⟨T.drift, 0, T.levyMeasure, T.levyMeasure_isLevyMeasure⟩
    Kyprianou.Ch01.levyTripleExponent T ξ =
      Kyprianou.Ch01.levyTripleExponent Tzero ξ -
        (((T.gaussianVariance : ℝ) * ξ ^ 2 / 2 : ℝ) : ℂ) := by
  dsimp [Kyprianou.Ch01.levyTripleExponent]
  push_cast
  ring
