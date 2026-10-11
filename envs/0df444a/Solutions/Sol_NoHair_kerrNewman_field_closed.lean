-- Prove2me | solution 1 for NoHair.kerrNewman_field_closed
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-11T05:57:47.293588+00:00
-- url     : https://prove2.me/submissions/312d2f33-3e34-4743-b92d-77eb2b579b9a

import Mathlib
import Definitions.Def_NoHair_kerrNewman

set_option autoImplicit false

open scoped ContDiff Manifold BigOperators
open Set Matrix

namespace NoHair.Sol_field_closed

open NoHair

private lemma fderiv_fderiv_apply_eq (f : E4 → ℝ) (y : E4) (hf : ContDiffAt ℝ 2 f y)
    (v w : E4) :
    fderiv ℝ (fun z => fderiv ℝ f z v) y w = fderiv ℝ (fderiv ℝ f) y w v := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) y :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [fderiv_clm_apply hD (differentiableAt_const v)]
  simp

private lemma symm2 (f : E4 → ℝ) (y : E4) (hf : ContDiffAt ℝ 2 f y) (v w : E4) :
    fderiv ℝ (fderiv ℝ f) y v w = fderiv ℝ (fderiv ℝ f) y w v :=
  hf.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]) v w

private lemma partial_field_eq (A : Fin 4 → E4 → ℝ) (y : E4)
    (hA : ∀ ν, ContDiffAt ℝ 2 (A ν) y) (l μ ν : Fin 4) :
    coordPartial (fun z => coordPartial (A ν) μ z - coordPartial (A μ) ν z) l y
      = fderiv ℝ (fderiv ℝ (A ν)) y (coordBasis l) (coordBasis μ)
        - fderiv ℝ (fderiv ℝ (A μ)) y (coordBasis l) (coordBasis ν) := by
  have hD : ∀ κ, DifferentiableAt ℝ (fderiv ℝ (A κ)) y := fun κ =>
    ((hA κ).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hd : ∀ κ (v : E4), DifferentiableAt ℝ (fun z => fderiv ℝ (A κ) z v) y := fun κ v =>
    (hD κ).clm_apply (differentiableAt_const v)
  unfold coordPartial
  rw [fderiv_fun_sub (hd ν _) (hd μ _)]
  rw [_root_.sub_apply, fderiv_fderiv_apply_eq _ _ (hA ν),
    fderiv_fderiv_apply_eq _ _ (hA μ)]

private lemma bianchi_generic (A : Fin 4 → E4 → ℝ) (y : E4)
    (hA : ∀ ν, ContDiffAt ℝ 2 (A ν) y) (l μ ν : Fin 4) :
    coordPartial (fun z => coordPartial (A ν) μ z - coordPartial (A μ) ν z) l y
      + coordPartial (fun z => coordPartial (A l) ν z - coordPartial (A ν) l z) μ y
      + coordPartial (fun z => coordPartial (A μ) l z - coordPartial (A l) μ z) ν y = 0 := by
  rw [partial_field_eq A y hA, partial_field_eq A y hA, partial_field_eq A y hA]
  rw [symm2 _ _ (hA ν) (coordBasis l) (coordBasis μ), symm2 _ _ (hA μ) (coordBasis l) (coordBasis ν),
    symm2 _ _ (hA l) (coordBasis μ) (coordBasis ν)]
  ring

private lemma ksRadius_contDiffAt (a : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    ContDiffAt ℝ 2 (ksRadius a) y := by
  have hout := Real.sqrt_pos.mp hy
  have hD : (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 2 * y 3 ^ 2 ≠ 0 := by
    intro h0
    have h1 : (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 - a ^ 2) ^ 2 = 0 := by
      have := sq_nonneg (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 - a ^ 2)
      have : 0 ≤ 4 * a ^ 2 * y 3 ^ 2 := by positivity
      linarith
    have h2 : y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 - a ^ 2 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
    simp only at hout
    rw [h0, Real.sqrt_zero, h2] at hout
    norm_num at hout
  unfold ksRadius
  simp only
  have hout' := ne_of_gt hout
  fun_prop (disch := assumption)

private lemma potential_contDiffAt (a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) (ν : Fin 4) :
    ContDiffAt ℝ 2 (fun z => kerrNewmanPotential a e z ν) y := by
  have hR := ksRadius_contDiffAt a y hy
  have h1 : ksRadius a y ≠ 0 := ne_of_gt hy
  have h2 : ksRadius a y ^ 4 + a ^ 2 * y 3 ^ 2 ≠ 0 := by positivity
  have h3 : ksRadius a y ^ 2 + a ^ 2 ≠ 0 := by positivity
  fin_cases ν <;>
    simp only [kerrNewmanPotential, ksNull, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;>
    fun_prop (disch := assumption)

end NoHair.Sol_field_closed

open NoHair NoHair.Sol_field_closed

theorem solution (a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    ∀ l μ ν, coordPartial (fun z => kerrNewmanField a e z μ ν) l y
      + coordPartial (fun z => kerrNewmanField a e z ν l) μ y
      + coordPartial (fun z => kerrNewmanField a e z l μ) ν y = 0 := by
  intro l μ ν
  exact bianchi_generic (fun κ z => kerrNewmanPotential a e z κ) y
    (fun κ => potential_contDiffAt a e y hy κ) l μ ν
