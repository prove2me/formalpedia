-- Prove2me | solution 1 for OAI.SharpPlanar.Scoords_add_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T08:09:14.774263+00:00
-- url     : https://prove2.me/submissions/45ab7d72-c363-4d45-b09d-44363781589f

import Mathlib
import Definitions.Def_OAIQ098E002
import Theorems.Thm_OAI_SharpPlanar_X_summable_pairs_e
import Theorems.Thm_OAI_SharpPlanar_b_pos_e
import Theorems.Thm_OAI_SharpPlanar_continuousOn_density_e
import Theorems.Thm_OAI_SharpPlanar_h_pos_e
import Theorems.Thm_OAI_SharpPlanar_piece_interval_e
import Theorems.Thm_OAI_SharpPlanar_summand_bound_e

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

lemma density_summable (x : X) (j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Summable (fun n : Node => (x (n, false) : ℂ) * u n.val j t +
      (x (n, true) : ℂ) * v n.val j t) := by
  exact ((X_summable_pairs_e x).mul_left densityBound).of_norm_bounded
    (fun n => summand_bound_e x n j ht)

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

lemma density_positive_add (x y : X) (j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    density (positiveData (x+y)) j t = density (positiveData x) j t +
      density (positiveData y) j t := by
  simp only [density, positiveData, Complex.ofReal_zero, zero_mul, zero_add,
    lp.coeFn_add, Pi.add_apply, Complex.ofReal_add]
  simp_rw [add_mul]
  simp_rw [show ∀ n : Node,
    (x (n, false) : ℂ) * u n.val j t + (y (n, false) : ℂ) * u n.val j t +
    ((x (n, true) : ℂ) * v n.val j t + (y (n, true) : ℂ) * v n.val j t) =
    ((x (n, false) : ℂ) * u n.val j t + (x (n, true) : ℂ) * v n.val j t) +
    ((y (n, false) : ℂ) * u n.val j t + (y (n, true) : ℂ) * v n.val j t) from fun n => by ring]
  exact (density_summable x j ht).tsum_add (density_summable y j ht)

lemma K_positive_add (x y : X) (ell : ℕ) (s : ℝ) :
    K (positiveData (x+y)) ell s = K (positiveData x) ell s + K (positiveData y) ell s := by
  have hp (j : ℕ) (hj : j < 6) :
      (∫ t in (j : ℝ)/6..((j : ℝ)+1)/6,
        density (positiveData (x+y)) j t * kernelMoment ell s t) =
      (∫ t in (j : ℝ)/6..((j : ℝ)+1)/6,
        density (positiveData x) j t * kernelMoment ell s t) +
      (∫ t in (j : ℝ)/6..((j : ℝ)+1)/6,
        density (positiveData y) j t * kernelMoment ell s t) := by
    rw [← intervalIntegral.integral_add (piece_integrable _ ell j hj s) (piece_integrable _ ell j hj s)]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [density_positive_add x y j (piece_interval_e hj ht), add_mul]
  unfold K
  simp only [positiveData, Complex.ofReal_zero, zero_mul, zero_add]
  rw [← Complex.add_re, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact hp j (Finset.mem_range.mp hj)

lemma Scoords_add_e_oai (x y : X) (ni : Node × Bool) :
    Scoords (x+y) ni = Scoords x ni + Scoords y ni := by
  unfold Scoords
  split <;> simp only [K_positive_add] <;> ring

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Scoords_add_e_oai := @OAI.SharpPlanar.Scoords_add_e_oai
