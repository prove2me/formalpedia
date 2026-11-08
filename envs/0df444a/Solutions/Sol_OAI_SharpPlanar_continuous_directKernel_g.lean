-- Prove2me | solution 1 for OAI.SharpPlanar.continuous_directKernel_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:07:38.749302+00:00
-- url     : https://prove2.me/submissions/e51ca018-bddf-4326-9f13-b5b35e34e2a5

import Mathlib
import Definitions.Def_OAIQ098G1643

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Entire
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [local instance] OAI.circleMeasurableSpace OAI.circleBorelSpace

namespace OAI

/-!
# Gaussian cardinal interpolation

The folded spectral representation gives the cardinal values and derivatives.
Gaussian damping then extends the radial cardinal functions to Schwartz functions.
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory



open MeasureTheory
open scoped ComplexConjugate



open Set Filter MeasureTheory
open scoped Topology FourierTransform ContDiff

namespace SharpPlanar
open MeasureTheory Set

lemma continuous_directKernel_g_oai (ell : ℕ) (s : ℝ) : Continuous (directKernel ell s) := by
  unfold directKernel
  fun_prop

end SharpPlanar


open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap


open scoped SchwartzMap

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.continuous_directKernel_g_oai := @OAI.SharpPlanar.continuous_directKernel_g_oai
