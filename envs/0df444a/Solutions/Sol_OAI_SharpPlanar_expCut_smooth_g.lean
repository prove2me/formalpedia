-- Prove2me | solution 1 for OAI.SharpPlanar.expCut_smooth_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T18:07:43.583035+00:00
-- url     : https://prove2.me/submissions/f83731cd-0183-4aef-86d5-9e6365a436ac

import Mathlib
import Definitions.Def_OAIQ098G012

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

lemma expCut_smooth_g_oai (c : ℝ) : ContDiff ℝ ∞ (expCut c) := by
  unfold expCut
  fun_prop

end SharpPlanar


open scoped SchwartzMap

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.expCut_smooth_g_oai := @OAI.SharpPlanar.expCut_smooth_g_oai
