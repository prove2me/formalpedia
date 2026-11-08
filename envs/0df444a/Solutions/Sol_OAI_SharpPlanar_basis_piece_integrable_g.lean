-- Prove2me | solution 1 for OAI.SharpPlanar.basis_piece_integrable_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T19:19:39.025883+00:00
-- url     : https://prove2.me/submissions/9615d640-afcb-4b2a-873e-9f62868663c0

import Mathlib
import Definitions.Def_OAIQ098G001
import Definitions.Def_OAIQ098G1643
import Theorems.Thm_OAI_SharpPlanar_continuous_directKernel_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Cardinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Gaussian cardinal functions for planar packing

The cardinal family and Fourier kernel follow the construction in
*A sharp Fourier certificate for planar circle packing* (OpenAI, 2026).
-/

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar


lemma continuous_u (n j : ℕ) : Continuous (u n j) := by
  unfold u
  fun_prop

lemma continuous_v (n j : ℕ) : Continuous (v n j) := by
  unfold v
  fun_prop

end SharpPlanar

end OAI
end

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

lemma basis_piece_integrable_g_oai (sec : Bool) (n ell j : ℕ) (s : ℝ) :
    IntervalIntegrable (fun t => (if sec then v n j t else u n j t) * directKernel ell s t) volume
      ((j:ℝ)/6) (((j:ℝ)+1)/6) := by
  apply Continuous.intervalIntegrable
  cases sec
  · exact (continuous_u n j).mul (continuous_directKernel_g ell s)
  · exact (continuous_v n j).mul (continuous_directKernel_g ell s)

end SharpPlanar


open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap


open scoped SchwartzMap

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.basis_piece_integrable_g_oai := @OAI.SharpPlanar.basis_piece_integrable_g_oai
