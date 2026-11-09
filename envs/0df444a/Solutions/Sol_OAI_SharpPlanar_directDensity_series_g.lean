-- Prove2me | solution 1 for OAI.SharpPlanar.directDensity_series_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T08:25:53.271204+00:00
-- url     : https://prove2.me/submissions/a8375528-9bc3-4c8d-a867-1afc16f81b26

import Mathlib
import Definitions.Def_OAIQ098G1642
import Definitions.Def_OAIQ098G1643
import Theorems.Thm_OAI_SharpPlanar_directDensity_split_g
import Theorems.Thm_OAI_SharpPlanar_direct_positive_series_g

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

lemma directDensity_series_g_oai (p : CardinalData) (ell : ℕ) (s : ℝ) :
    (∑ j ∈ Finset.range 6, ∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
      density p j t * directKernel ell s t).re =
    p.c₀*basisMoment false 0 ell s + p.d₀*basisMoment true 0 ell s +
      ∑' n : Node, (p.x (n,false)*basisMoment false n.val ell s +
        p.x (n,true)*basisMoment true n.val ell s) := by
  have he (j : ℕ) (hj : j ∈ Finset.range 6) := directDensity_split_g p ell j (Finset.mem_range.mp hj) s
  conv_lhs => arg 1; rw [Finset.sum_congr rfl he]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Complex.add_re,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [direct_positive_series_g]
  simp only [basisMoment,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,directKernel,mul_assoc]

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.directDensity_series_g_oai := @OAI.SharpPlanar.directDensity_series_g_oai
