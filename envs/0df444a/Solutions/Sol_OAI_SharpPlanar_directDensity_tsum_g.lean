-- Prove2me | solution 1 for OAI.SharpPlanar.directDensity_tsum_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:25:22.054979+00:00
-- url     : https://prove2.me/submissions/05936930-3266-4916-8918-15bbb5ae5f2b

import Mathlib
import Definitions.Def_OAIQ098G002
import Definitions.Def_OAIQ098G1643
import Theorems.Thm_OAI_SharpPlanar_X_summable_pairs_g
import Theorems.Thm_OAI_SharpPlanar_continuous_directKernel_g
import Theorems.Thm_OAI_SharpPlanar_interval_integral_tsum_uniform_g
import Theorems.Thm_OAI_SharpPlanar_piece_interval_g
import Theorems.Thm_OAI_SharpPlanar_realSpectral_norm_g
import Theorems.Thm_OAI_SharpPlanar_summand_bound_g

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

lemma densityBound_nonneg : 0 ≤ densityBound := by unfold densityBound; positivity


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

lemma directDensity_tsum_g_oai (x : X) (ell j : ℕ) (hj : j < 6) (s : ℝ) :
    (∫ t in (j:ℝ)/6..((j:ℝ)+1)/6, density (positiveData x) j t * directKernel ell s t) =
      ∑' n : Node, ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
        ((x (n,false):ℂ)*u n.val j t + (x (n,true):ℂ)*v n.val j t) * directKernel ell s t := by
  have he (t : ℝ) : density (positiveData x) j t * directKernel ell s t =
      ∑' n : Node, ((x (n,false):ℂ)*u n.val j t + (x (n,true):ℂ)*v n.val j t) * directKernel ell s t := by
    simp only [density,positiveData,Complex.ofReal_zero,zero_mul,zero_add,tsum_mul_right]
  simp_rw [he]
  apply interval_integral_tsum_uniform_g (by linarith : (j:ℝ)/6 ≤ ((j:ℝ)+1)/6)
    (fun n => by apply Continuous.continuousOn; apply Continuous.mul
                 · exact (continuous_const.mul (continuous_u n.val j)).add
                     (continuous_const.mul (continuous_v n.val j))
                 · exact continuous_directKernel_g ell s)
    (fun n : Node => (densityBound*Real.pi^ell)*(|x (n,false)|+|x (n,true)|))
    ((X_summable_pairs_g x).mul_left (densityBound*Real.pi^ell))
  intro n t ht
  rw [norm_mul]
  have ht' := piece_interval_g hj (show t ∈ uIcc ((j:ℝ)/6) (((j:ℝ)+1)/6) by
    rwa [uIcc_of_le (by linarith : (j:ℝ)/6 ≤ ((j:ℝ)+1)/6)])
  calc
    _ ≤ (densityBound*(|x (n,false)|+|x (n,true)|))*Real.pi^ell :=
      mul_le_mul (summand_bound_g x n j ht') (realSpectral_norm_g ell ht' s)
        (norm_nonneg _) (mul_nonneg densityBound_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)))
    _ = _ := by ring

end SharpPlanar


open Set Filter MeasureTheory Asymptotics
open scoped Topology ContDiff SchwartzMap


open scoped SchwartzMap

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.directDensity_tsum_g_oai := @OAI.SharpPlanar.directDensity_tsum_g_oai
