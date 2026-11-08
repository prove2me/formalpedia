-- Prove2me | solution 1 for OAI.SharpPlanar.directDensity_split_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T19:28:17.39947+00:00
-- url     : https://prove2.me/submissions/cf7c0763-dcc6-4b15-96bb-a070a904c579

import Mathlib
import Definitions.Def_OAIQ098G001
import Definitions.Def_OAIQ098G1643
import Theorems.Thm_OAI_SharpPlanar_continuous_directKernel_g
import Theorems.Thm_OAI_SharpPlanar_direct_basis_pair_g
import Theorems.Thm_OAI_SharpPlanar_direct_piece_integrable_g

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


open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap


open scoped SchwartzMap

namespace SharpPlanar
open MeasureTheory Set

lemma directDensity_split_g_oai (p : CardinalData) (ell j : ℕ) (hj : j < 6) (s : ℝ) :
    (∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, density p j t * directKernel ell s t) =
      (p.c₀:ℂ)*(∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, u 0 j t * directKernel ell s t) +
      (p.d₀:ℂ)*(∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, v 0 j t * directKernel ell s t) +
      (∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, density (positiveData p.x) j t * directKernel ell s t) := by
  have he (t : ℝ) : density p j t * directKernel ell s t =
      ((p.c₀:ℂ)*u 0 j t+(p.d₀:ℂ)*v 0 j t)*directKernel ell s t +
      density (positiveData p.x) j t * directKernel ell s t := by
    simp [density,positiveData,add_mul]
  simp_rw [he]
  have ha : IntervalIntegrable (fun t => ((p.c₀:ℂ)*u 0 j t+(p.d₀:ℂ)*v 0 j t)*directKernel ell s t)
      volume ((j:ℝ)/6) (((j:ℝ)+1)/6) := by
    apply Continuous.intervalIntegrable
    exact ((continuous_const.mul (continuous_u 0 j)).add
      (continuous_const.mul (continuous_v 0 j))).mul (continuous_directKernel_g ell s)
  rw [intervalIntegral.integral_add ha (direct_piece_integrable_g _ ell j hj s),direct_basis_pair_g]

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.directDensity_split_g_oai := @OAI.SharpPlanar.directDensity_split_g_oai
