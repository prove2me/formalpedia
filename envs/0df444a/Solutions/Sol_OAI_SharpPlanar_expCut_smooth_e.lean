-- Prove2me | solution 1 for OAI.SharpPlanar.expCut_smooth_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T08:04:29.34489+00:00
-- url     : https://prove2.me/submissions/60d03da7-c2c6-4112-8ec5-f687d517102c

import Mathlib
import Definitions.Def_OAIQ098E012

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Entire
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

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


open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap

namespace SharpPlanar

lemma expCut_smooth_e_oai (c : ℝ) : ContDiff ℝ ∞ (expCut c) := by
  unfold expCut
  fun_prop

end SharpPlanar


open scoped SchwartzMap

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.expCut_smooth_e_oai := @OAI.SharpPlanar.expCut_smooth_e_oai
