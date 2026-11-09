-- Prove2me | solution 1 for OAI.SharpPlanar.direct_positive_series_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T08:26:22.477096+00:00
-- url     : https://prove2.me/submissions/96b8b09d-fc15-4fec-b0c8-e9e12527acb2

import Mathlib
import Definitions.Def_OAIQ098G1642
import Definitions.Def_OAIQ098G1643
import Theorems.Thm_OAI_SharpPlanar_directDensity_tsum_g
import Theorems.Thm_OAI_SharpPlanar_direct_basis_integral_summable_g
import Theorems.Thm_OAI_SharpPlanar_direct_basis_pair_g

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

lemma direct_positive_series_g_oai (x : X) (ell : ℕ) (s : ℝ) :
    (∑ j ∈ Finset.range 6, ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
      density (positiveData x) j t * directKernel ell s t).re =
    ∑' n : Node, (x (n,false)*basisMoment false n.val ell s +
      x (n,true)*basisMoment true n.val ell s) := by
  have he (j : ℕ) (hj : j ∈ Finset.range 6) := directDensity_tsum_g x ell j (Finset.mem_range.mp hj) s
  conv_lhs => arg 1; rw [Finset.sum_congr rfl he]
  rw [← Summable.tsum_finsetSum (fun j hj => direct_basis_integral_summable_g x ell j (Finset.mem_range.mp hj) s)]
  change Complex.reCLM (∑' n : Node, ∑ j ∈ Finset.range 6, ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
    ((x (n,false):ℂ)*u n.val j t+(x (n,true):ℂ)*v n.val j t)*directKernel ell s t) = _
  rw [ContinuousLinearMap.map_tsum _ (summable_sum
    (fun j hj => direct_basis_integral_summable_g x ell j (Finset.mem_range.mp hj) s))]
  apply tsum_congr
  intro n
  simp_rw [direct_basis_pair_g]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,
    Complex.reCLM_apply,Complex.add_re,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  simp [basisMoment,directKernel,mul_assoc]

end SharpPlanar


open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap


open scoped SchwartzMap

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.direct_positive_series_g_oai := @OAI.SharpPlanar.direct_positive_series_g_oai
