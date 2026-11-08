-- Prove2me | solution 1 for OAI.SharpPlanar.direct_piece_integrable_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T19:28:20.047939+00:00
-- url     : https://prove2.me/submissions/0ce46ca0-c568-40d2-b53f-cdebe4dafe27

import Mathlib
import Definitions.Def_OAIQ098G001
import Definitions.Def_OAIQ098G1643
import Theorems.Thm_OAI_SharpPlanar_continuousOn_density_g
import Theorems.Thm_OAI_SharpPlanar_continuous_directKernel_g
import Theorems.Thm_OAI_SharpPlanar_piece_interval_g

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

lemma direct_piece_integrable_g_oai (p : CardinalData) (ell j : ℕ) (hj : j < 6) (s : ℝ) :
    IntervalIntegrable (fun t => density p j t * directKernel ell s t) volume
      ((j:ℝ)/6) (((j:ℝ)+1)/6) := by
  exact ((continuousOn_density_g p j).mul (continuous_directKernel_g ell s).continuousOn).mono
    (fun _ ht => piece_interval_g hj ht) |>.intervalIntegrable

end SharpPlanar


open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap


open scoped SchwartzMap

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.direct_piece_integrable_g_oai := @OAI.SharpPlanar.direct_piece_integrable_g_oai
