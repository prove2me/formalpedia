-- Prove2me | solution 1 for OAI.SharpPlanar.direct_basis_pair_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T19:27:10.115169+00:00
-- url     : https://prove2.me/submissions/6463a8aa-acfa-406a-9cd3-9668c91d38d2

import Mathlib
import Definitions.Def_OAIQ098G001
import Definitions.Def_OAIQ098G1643
import Theorems.Thm_OAI_SharpPlanar_basis_piece_integrable_g

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

lemma direct_basis_pair_g_oai (c d : ℝ) (n ell j : ℕ) (s : ℝ) :
    (∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
      ((c:ℂ)*u n j t+(d:ℂ)*v n j t)*directKernel ell s t) =
    (c:ℂ)*(∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,u n j t*directKernel ell s t) +
    (d:ℂ)*(∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,v n j t*directKernel ell s t) := by
  simp_rw [add_mul,mul_assoc]
  have hU : IntervalIntegrable (fun t => u n j t * directKernel ell s t) volume
      ((j:ℝ)/6) (((j:ℝ)+1)/6) := by simpa using basis_piece_integrable_g false n ell j s
  have hV : IntervalIntegrable (fun t => v n j t * directKernel ell s t) volume
      ((j:ℝ)/6) (((j:ℝ)+1)/6) := by simpa using basis_piece_integrable_g true n ell j s
  rw [intervalIntegral.integral_add (hU.const_mul (c:ℂ)) (hV.const_mul (d:ℂ)),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]

end SharpPlanar


open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap


open scoped SchwartzMap

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.direct_basis_pair_g_oai := @OAI.SharpPlanar.direct_basis_pair_g_oai
