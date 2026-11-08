-- Prove2me | solution 1 for OAI.SharpPlanar.direct_basis_integral_bound_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:25:36.320401+00:00
-- url     : https://prove2.me/submissions/5568e218-7389-41fb-af95-9172afa0acca

import Mathlib
import Definitions.Def_OAIQ098G002
import Definitions.Def_OAIQ098G1643
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

lemma direct_basis_integral_bound_g_oai (x : X) (n : Node) (ell j : ℕ) (hj : j < 6) (s : ℝ) :
    ‖∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
      ((x (n,false):ℂ)*u n.val j t+(x (n,true):ℂ)*v n.val j t)*directKernel ell s t‖ ≤
        ((densityBound*Real.pi^ell)/6)*(|x (n,false)|+|x (n,true)|) := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (f:=fun t => ((x (n,false):ℂ)*u n.val j t+(x (n,true):ℂ)*v n.val j t)*directKernel ell s t)
    (a:=(j:ℝ)/6) (b:=((j:ℝ)+1)/6)
    (C:=(densityBound*Real.pi^ell)*(|x (n,false)|+|x (n,true)|)) (fun t ht => ?_)
  · convert hh using 1
    all_goals try with_reducible_and_instances rfl
    rw [show ((j:ℝ)+1)/6-(j:ℝ)/6=1/6 by ring,abs_of_pos (by norm_num : (0:ℝ)<1/6)]
    ring
  · rw [norm_mul]
    have ht' := piece_interval_g hj (uIoc_subset_uIcc ht)
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

theorem solution : type_of% @OAI.SharpPlanar.direct_basis_integral_bound_g_oai := @OAI.SharpPlanar.direct_basis_integral_bound_g_oai
