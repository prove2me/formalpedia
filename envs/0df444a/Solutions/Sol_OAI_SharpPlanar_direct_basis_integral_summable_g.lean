-- Prove2me | solution 1 for OAI.SharpPlanar.direct_basis_integral_summable_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:15:44.963314+00:00
-- url     : https://prove2.me/submissions/27d978d4-8ea1-4810-a2d7-ecfbf60e8dba

import Mathlib
import Definitions.Def_OAIQ098G002
import Definitions.Def_OAIQ098G1643
import Theorems.Thm_OAI_SharpPlanar_X_summable_pairs_g
import Theorems.Thm_OAI_SharpPlanar_direct_basis_integral_bound_g

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

lemma direct_basis_integral_summable_g_oai (x : X) (ell j : ℕ) (hj : j < 6) (s : ℝ) :
    Summable (fun n : Node => ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
      ((x (n,false):ℂ)*u n.val j t+(x (n,true):ℂ)*v n.val j t)*directKernel ell s t) :=
  ((X_summable_pairs_g x).mul_left ((densityBound*Real.pi^ell)/6)).of_norm_bounded
    (fun n => direct_basis_integral_bound_g x n ell j hj s)

end SharpPlanar


open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap


open scoped SchwartzMap

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.direct_basis_integral_summable_g_oai := @OAI.SharpPlanar.direct_basis_integral_summable_g_oai
