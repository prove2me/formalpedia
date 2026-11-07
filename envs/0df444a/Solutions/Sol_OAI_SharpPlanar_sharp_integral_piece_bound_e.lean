-- Prove2me | solution 1 for OAI.SharpPlanar.sharp_integral_piece_bound_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T03:59:55.363451+00:00
-- url     : https://prove2.me/submissions/1de29969-225f-4fe8-9925-84c4bb973d3d

import Mathlib
import Definitions.Def_OAIQ098E126
import Theorems.Thm_OAI_SharpPlanar_b_pos_e
import Theorems.Thm_OAI_SharpPlanar_continuousOn_density_e
import Theorems.Thm_OAI_SharpPlanar_densityCap_nonneg_e
import Theorems.Thm_OAI_SharpPlanar_h_pos_e
import Theorems.Thm_OAI_SharpPlanar_kernelMoment_segment_bound_e
import Theorems.Thm_OAI_SharpPlanar_piece_density_bound_e
import Theorems.Thm_OAI_SharpPlanar_piece_interval_e
import Theorems.Thm_OAI_SharpPlanar_segmentEnvelope_integral_bound_e

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

lemma denominator_ne (t : ℝ) : (t : ℂ) + Complex.I * h ≠ 0 := by
  intro he
  have hh := congrArg Complex.im he
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.ofReal_re, Complex.I_im, zero_mul, one_mul, zero_add, Complex.zero_im] at hh
  exact (ne_of_gt h_pos_e) hh

lemma continuous_lambda : Continuous lambda := by
  unfold lambda
  fun_prop (disch := intro t; exact mul_ne_zero (by exact_mod_cast b_pos_e.ne') (denominator_ne t))

lemma continuous_z : Continuous z := by
  unfold z
  fun_prop (disch := intro t; exact denominator_ne t)

lemma continuous_kernelMoment (ell : ℕ) (s : ℝ) : Continuous (kernelMoment ell s) := by
  unfold kernelMoment
  exact (continuous_lambda.mul ((continuous_const.mul continuous_z).pow ell)).mul
    (Complex.continuous_exp.comp ((continuous_const.mul continuous_z).mul continuous_const))

lemma piece_integrable (p : CardinalData) (ell j : ℕ) (hj : j < 6) (s : ℝ) :
    IntervalIntegrable (fun t => density p j t * kernelMoment ell s t) volume
      ((j : ℝ)/6) (((j : ℝ)+1)/6) := by
  exact ((continuousOn_density_e p j).mul (continuous_kernelMoment ell s).continuousOn).mono
    (fun _ ht => piece_interval_e hj ht) |>.intervalIntegrable

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CanonicalRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace SharpPlanar
open IntegerBasis

lemma sharp_integral_piece_bound_e_oai (p : CardinalData) (j : Fin 6) (ell : ℕ) {s : ℝ}
    (hs : 0 ≤ s) :
    ‖∫ t in (j.val:ℝ)/6..((j.val:ℝ)+1)/6, density p j.val t*kernelMoment ell s t‖ ≤
      (|p.c₀|+|p.d₀|+‖p.x‖)*densityCap j*pieceL j s*(Real.pi*zCap ⟨j.val,by omega⟩)^ell := by
  let w : ℝ := |p.c₀|+|p.d₀|+‖p.x‖
  have hw : 0 ≤ w := by dsimp [w] <;> positivity
  have hlu : (j.val:ℝ)/6 ≤ ((j.val:ℝ)+1)/6 := by linarith
  calc
    _ ≤ ∫ t in (j.val:ℝ)/6..((j.val:ℝ)+1)/6, ‖density p j.val t*kernelMoment ell s t‖ :=
      intervalIntegral.norm_integral_le_integral_norm hlu
    _ ≤ ∫ t in (j.val:ℝ)/6..((j.val:ℝ)+1)/6, (w*densityCap j)*segmentEnvelope j ell s t := by
      apply intervalIntegral.integral_mono_on hlu (piece_integrable p ell j.val j.isLt s).norm
        ((by unfold segmentEnvelope; fun_prop : Continuous (fun t : ℝ => (w*densityCap j)*segmentEnvelope j ell s t)).intervalIntegrable _ _)
      intro t ht
      rw [norm_mul]
      have hd := piece_density_bound_e p j ht
      have hk := kernelMoment_segment_bound_e j ell hs ht
      rw [mul_comm w]
      exact mul_le_mul hd hk (norm_nonneg _) (mul_nonneg (densityCap_nonneg_e _) hw)
    _ = (w*densityCap j)*(∫ t in (j.val:ℝ)/6..((j.val:ℝ)+1)/6, segmentEnvelope j ell s t) :=
      intervalIntegral.integral_const_mul _ _
    _ ≤ (w*densityCap j)*(pieceL j s*(Real.pi*zCap ⟨j.val,by omega⟩)^ell) :=
      mul_le_mul_of_nonneg_left (segmentEnvelope_integral_bound_e j ell hs) (mul_nonneg hw (densityCap_nonneg_e _))
    _ = _ := by dsimp [w] <;> ring

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.sharp_integral_piece_bound_e_oai := @OAI.SharpPlanar.sharp_integral_piece_bound_e_oai
