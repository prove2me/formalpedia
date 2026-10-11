-- Prove2me | solution 1 for NoHair.kerrNewman_flat_maxwell
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-11T06:16:41.212049+00:00
-- url     : https://prove2.me/submissions/efe303cf-e099-4ee7-aac8-72739ed361ab

import Mathlib
import Definitions.Def_NoHair_kerrNewman

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped ContDiff Manifold BigOperators
open Set Matrix

noncomputable section

namespace NoHair.Sol_flat_maxwell

open NoHair

private lemma cb_apply (k i : Fin 4) : coordBasis k i = if i = k then 1 else 0 := by
  simp [coordBasis]

private lemma cb_11 : coordBasis 1 1 = 1 := by simp [coordBasis]
private lemma cb_12 : coordBasis 1 2 = 0 := by simp [coordBasis]
private lemma cb_13 : coordBasis 1 3 = 0 := by simp [coordBasis]
private lemma cb_21 : coordBasis 2 1 = 0 := by simp [coordBasis]
private lemma cb_22 : coordBasis 2 2 = 1 := by simp [coordBasis]
private lemma cb_23 : coordBasis 2 3 = 0 := by simp [coordBasis]
private lemma cb_31 : coordBasis 3 1 = 0 := by simp [coordBasis]
private lemma cb_32 : coordBasis 3 2 = 0 := by simp [coordBasis]
private lemma cb_33 : coordBasis 3 3 = 1 := by simp [coordBasis]

private lemma line_apply (z : E4) (k i : Fin 4) (s : ℝ) :
    (z + s • coordBasis k) i = z i + s * coordBasis k i := by
  simp

private lemma hasDerivAt_line_coord (z : E4) (k i : Fin 4) :
    HasDerivAt (fun s : ℝ => (z + s • coordBasis k) i) (coordBasis k i) 0 := by
  have : (fun s : ℝ => (z + s • coordBasis k) i) = fun s => z i + s * coordBasis k i := by
    funext s; simp
  rw [this]
  simpa using ((hasDerivAt_id (0:ℝ)).mul_const (coordBasis k i)).const_add (z i)

private lemma hasDerivAt_line (z : E4) (k : Fin 4) :
    HasDerivAt (fun s : ℝ => z + s • coordBasis k) (coordBasis k) 0 := by
  simpa using ((hasDerivAt_id (0:ℝ)).smul_const (coordBasis k)).const_add z

private lemma hasDerivAt_comp_line (g : E4 → ℝ) (z : E4) (k : Fin 4)
    (hg : DifferentiableAt ℝ g z) :
    HasDerivAt (fun s : ℝ => g (z + s • coordBasis k)) (coordPartial g k z) 0 := by
  have h2 : HasFDerivAt g (fderiv ℝ g z) (z + (0:ℝ) • coordBasis k) := by
    rw [zero_smul, add_zero]; exact hg.hasFDerivAt
  exact h2.comp_hasDerivAt (0:ℝ) (hasDerivAt_line z k)

private lemma partial_eq_of_line (g : E4 → ℝ) (z : E4) (k : Fin 4)
    (hg : DifferentiableAt ℝ g z) (d : ℝ)
    (h : HasDerivAt (fun s : ℝ => g (z + s • coordBasis k)) d 0) : coordPartial g k z = d :=
  (hasDerivAt_comp_line g z k hg).unique h

/-- t-independence: a function invariant under time translation has zero time derivative. -/
private lemma partial_zero_of_invariant (g : E4 → ℝ) (z : E4)
    (hg : ∀ w : E4, ∀ s : ℝ, g (w + s • coordBasis 0) = g w) : coordPartial g 0 z = 0 := by
  by_cases hd : DifferentiableAt ℝ g z
  · have h1 := hasDerivAt_comp_line g z 0 hd
    have h2 : HasDerivAt (fun s : ℝ => g (z + s • coordBasis 0)) 0 0 := by
      have : (fun s : ℝ => g (z + s • coordBasis 0)) = fun _ => g z := by
        funext s; exact hg z s
      rw [this]; exact hasDerivAt_const _ _
    exact h1.unique h2
  · unfold coordPartial
    rw [fderiv_zero_of_not_differentiableAt hd]
    rfl

private lemma partial_invariant (g : E4 → ℝ) (k : Fin 4)
    (hg : ∀ w : E4, ∀ s : ℝ, g (w + s • coordBasis 0) = g w) (w : E4) (s : ℝ) :
    coordPartial g k (w + s • coordBasis 0) = coordPartial g k w := by
  unfold coordPartial
  rw [← fderiv_comp_add_right]
  congr 2
  funext x
  exact hg x s


private lemma ksRadius_sq (a : ℝ) (z : E4) :
    ksRadius a z ^ 2 = ((z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2)
      + Real.sqrt ((z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 2 * z 3 ^ 2)) / 2 := by
  unfold ksRadius
  simp only
  rw [Real.sq_sqrt]
  have h1 : Real.sqrt ((z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) ^ 2)
      ≤ Real.sqrt ((z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 2 * z 3 ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (a * z 3)])
  rw [Real.sqrt_sq_eq_abs] at h1
  have h2 := neg_abs_le (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2)
  linarith

private lemma ksRadius_C (a : ℝ) (z : E4) :
    ksRadius a z ^ 4 - (z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2) * ksRadius a z ^ 2
      - a ^ 2 * z 3 ^ 2 = 0 := by
  have h := ksRadius_sq a z
  set S := z 1 ^ 2 + z 2 ^ 2 + z 3 ^ 2 - a ^ 2
  have hq := Real.sq_sqrt (show (0:ℝ) ≤ S ^ 2 + 4 * a ^ 2 * z 3 ^ 2 by positivity)
  have h4 : ksRadius a z ^ 4 = (ksRadius a z ^ 2) ^ 2 := by ring
  rw [h4, h]
  linear_combination hq / 4

private lemma ksRadius_contDiffAt (a : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    ContDiffAt ℝ 2 (ksRadius a) y := by
  have hout := Real.sqrt_pos.mp hy
  have hD : (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 - a ^ 2) ^ 2 + 4 * a ^ 2 * y 3 ^ 2 ≠ 0 := by
    intro h0
    have h1 : (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 - a ^ 2) ^ 2 = 0 := by
      have := sq_nonneg (y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 - a ^ 2)
      have : 0 ≤ 4 * a ^ 2 * y 3 ^ 2 := by positivity
      linarith
    have h2 : y 1 ^ 2 + y 2 ^ 2 + y 3 ^ 2 - a ^ 2 = 0 :=
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
    simp only at hout
    rw [h0, Real.sqrt_zero, h2] at hout
    norm_num at hout
  unfold ksRadius
  simp only
  have hout' := ne_of_gt hout
  fun_prop (disch := assumption)

private lemma ksRadius_diff (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    DifferentiableAt ℝ (ksRadius a) z :=
  (ksRadius_contDiffAt a z hz).differentiableAt (by norm_num)

private lemma isOpen_U (a : ℝ) : IsOpen {z : E4 | 0 < ksRadius a z} :=
  isOpen_lt continuous_const (continuous_ksRadius a)

/-- Generic directional derivative of `r` along `coordBasis k`. -/
private def dR (a : ℝ) (z : E4) (k : Fin 4) : ℝ :=
  ksRadius a z * (ksRadius a z ^ 2 * (z 1 * coordBasis k 1 + z 2 * coordBasis k 2
    + z 3 * coordBasis k 3) + a ^ 2 * z 3 * coordBasis k 3) / (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2)

private lemma hasDerivAt_line_R (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) (k : Fin 4) :
    HasDerivAt (fun s : ℝ => ksRadius a (z + s • coordBasis k)) (dR a z k) 0 := by
  have hR := hasDerivAt_comp_line (ksRadius a) z k (ksRadius_diff a z hz)
  set d := coordPartial (ksRadius a) k z
  -- the constraint along the line is identically zero
  have hx := fun i => hasDerivAt_line_coord z k i
  have hΨ := ((((hR.pow 4).sub ((((hx 1).pow 2).add ((hx 2).pow 2)).add ((hx 3).pow 2)
    |>.sub_const (a ^ 2) |>.mul (hR.pow 2))).sub (((hx 3).pow 2).const_mul (a ^ 2))))
  have hzero : HasDerivAt (fun s : ℝ => ksRadius a (z + s • coordBasis k) ^ 4
      - ((z + s • coordBasis k) 1 ^ 2 + (z + s • coordBasis k) 2 ^ 2
        + (z + s • coordBasis k) 3 ^ 2 - a ^ 2) * ksRadius a (z + s • coordBasis k) ^ 2
      - a ^ 2 * (z + s • coordBasis k) 3 ^ 2) 0 0 := by
    have : (fun s : ℝ => ksRadius a (z + s • coordBasis k) ^ 4
      - ((z + s • coordBasis k) 1 ^ 2 + (z + s • coordBasis k) 2 ^ 2
        + (z + s • coordBasis k) 3 ^ 2 - a ^ 2) * ksRadius a (z + s • coordBasis k) ^ 2
      - a ^ 2 * (z + s • coordBasis k) 3 ^ 2) = fun _ => 0 := by
      funext s; exact ksRadius_C a _
    rw [this]; exact hasDerivAt_const _ _
  have heq := hΨ.unique hzero
  simp only [zero_smul, add_zero] at heq
  have hC := ksRadius_C a z
  have hr := hz
  have hD : ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2 ≠ 0 := by positivity
  have hd : d = dR a z k := by
    unfold dR
    rw [eq_div_iff hD]
    norm_num at heq
    linear_combination (ksRadius a z / 2) * heq - d * hC
  rw [← hd]; exact hR


private def Hf (a e : ℝ) (z : E4) : ℝ := e * ksRadius a z ^ 3 / (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2)
private def k1f (a : ℝ) (z : E4) : ℝ := (ksRadius a z * z 1 + a * z 2) / (ksRadius a z ^ 2 + a ^ 2)
private def k2f (a : ℝ) (z : E4) : ℝ := (ksRadius a z * z 2 - a * z 1) / (ksRadius a z ^ 2 + a ^ 2)
private def k3f (a : ℝ) (z : E4) : ℝ := z 3 / ksRadius a z
private def psif (a e : ℝ) (z : E4) : ℝ :=
  e * a * z 3 * ksRadius a z / (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2)

private def Hd (a e : ℝ) (z : E4) (k : Fin 4) : ℝ :=
  e * (3 * ksRadius a z ^ 2 * dR a z k * (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2)
    - ksRadius a z ^ 3 * (4 * ksRadius a z ^ 3 * dR a z k + 2 * a ^ 2 * z 3 * coordBasis k 3))
    / (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2) ^ 2

private lemma hasDerivAt_line_H (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) (k : Fin 4) :
    HasDerivAt (fun s : ℝ => Hf a e (z + s • coordBasis k)) (Hd a e z k) 0 := by
  have hR := hasDerivAt_line_R a z hz k
  have h3 := hasDerivAt_line_coord z k 3
  have h := ((hR.pow 3).const_mul e).div ((hR.pow 4).add ((h3.pow 2).const_mul (a ^ 2)))
    (by simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, zero_smul, add_zero]; positivity)
  refine h.congr_deriv ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, zero_smul, add_zero, Hd]
  push_cast
  ring


private def k1d (a : ℝ) (z : E4) (k : Fin 4) : ℝ :=
  ((dR a z k * z 1 + ksRadius a z * coordBasis k 1 + a * coordBasis k 2) * (ksRadius a z ^ 2 + a ^ 2)
    - (ksRadius a z * z 1 + a * z 2) * (2 * ksRadius a z * dR a z k)) / (ksRadius a z ^ 2 + a ^ 2) ^ 2

private def k2d (a : ℝ) (z : E4) (k : Fin 4) : ℝ :=
  ((dR a z k * z 2 + ksRadius a z * coordBasis k 2 - a * coordBasis k 1) * (ksRadius a z ^ 2 + a ^ 2)
    - (ksRadius a z * z 2 - a * z 1) * (2 * ksRadius a z * dR a z k)) / (ksRadius a z ^ 2 + a ^ 2) ^ 2

private def k3d (a : ℝ) (z : E4) (k : Fin 4) : ℝ :=
  (coordBasis k 3 * ksRadius a z - z 3 * dR a z k) / ksRadius a z ^ 2

private def psid (a e : ℝ) (z : E4) (k : Fin 4) : ℝ :=
  e * a * ((coordBasis k 3 * ksRadius a z + z 3 * dR a z k) * (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2)
    - z 3 * ksRadius a z * (4 * ksRadius a z ^ 3 * dR a z k + 2 * a ^ 2 * z 3 * coordBasis k 3))
    / (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2) ^ 2

private lemma hasDerivAt_line_k1 (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) (k : Fin 4) :
    HasDerivAt (fun s : ℝ => k1f a (z + s • coordBasis k)) (k1d a z k) 0 := by
  have hR := hasDerivAt_line_R a z hz k
  have h1 := hasDerivAt_line_coord z k 1
  have h2 := hasDerivAt_line_coord z k 2
  have h := ((hR.mul h1).add (h2.const_mul a)).div ((hR.pow 2).add_const (a ^ 2))
    (by simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, zero_smul, add_zero]; positivity)
  refine h.congr_deriv ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, zero_smul, add_zero, k1d]
  push_cast
  ring

private lemma hasDerivAt_line_k2 (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) (k : Fin 4) :
    HasDerivAt (fun s : ℝ => k2f a (z + s • coordBasis k)) (k2d a z k) 0 := by
  have hR := hasDerivAt_line_R a z hz k
  have h1 := hasDerivAt_line_coord z k 1
  have h2 := hasDerivAt_line_coord z k 2
  have h := ((hR.mul h2).sub (h1.const_mul a)).div ((hR.pow 2).add_const (a ^ 2))
    (by simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, zero_smul, add_zero]; positivity)
  refine h.congr_deriv ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, zero_smul, add_zero, k2d]
  push_cast
  ring

private lemma hasDerivAt_line_k3 (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) (k : Fin 4) :
    HasDerivAt (fun s : ℝ => k3f a (z + s • coordBasis k)) (k3d a z k) 0 := by
  have hR := hasDerivAt_line_R a z hz k
  have h3 := hasDerivAt_line_coord z k 3
  have h := h3.div hR (by simp only [zero_smul, add_zero]; positivity)
  refine h.congr_deriv ?_
  simp only [zero_smul, add_zero, k3d]

private lemma hasDerivAt_line_psi (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) (k : Fin 4) :
    HasDerivAt (fun s : ℝ => psif a e (z + s • coordBasis k)) (psid a e z k) 0 := by
  have hR := hasDerivAt_line_R a z hz k
  have h3 := hasDerivAt_line_coord z k 3
  have h := ((h3.const_mul (e * a)).mul hR).div ((hR.pow 4).add ((h3.pow 2).const_mul (a ^ 2)))
    (by simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, zero_smul, add_zero]; positivity)
  refine h.congr_deriv ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, zero_smul, add_zero, psid]
  push_cast
  ring


private lemma A0_eq (a e : ℝ) : (fun z => kerrNewmanPotential a e z 0) = Hf a e := by
  funext z; simp [kerrNewmanPotential, ksNull, Hf]

private lemma A1_eq (a e : ℝ) :
    (fun z => kerrNewmanPotential a e z 1) = fun z => Hf a e z * k1f a z := by
  funext z; simp [kerrNewmanPotential, ksNull, Hf, k1f]

private lemma A2_eq (a e : ℝ) :
    (fun z => kerrNewmanPotential a e z 2) = fun z => Hf a e z * k2f a z := by
  funext z; simp [kerrNewmanPotential, ksNull, Hf, k2f]

private lemma A3_eq (a e : ℝ) :
    (fun z => kerrNewmanPotential a e z 3) = fun z => Hf a e z * k3f a z := by
  funext z; simp [kerrNewmanPotential, ksNull, Hf, k3f]

private lemma diff_Hf (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    DifferentiableAt ℝ (Hf a e) z := by
  have hR := ksRadius_diff a z hz
  have h1 : ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2 ≠ 0 := by positivity
  show DifferentiableAt ℝ (fun z => e * ksRadius a z ^ 3 / (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2)) z
  fun_prop (disch := assumption)

private lemma diff_k1 (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    DifferentiableAt ℝ (k1f a) z := by
  have hR := ksRadius_diff a z hz
  have h1 : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  show DifferentiableAt ℝ (fun z => (ksRadius a z * z 1 + a * z 2) / (ksRadius a z ^ 2 + a ^ 2)) z
  fun_prop (disch := assumption)

private lemma diff_k2 (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    DifferentiableAt ℝ (k2f a) z := by
  have hR := ksRadius_diff a z hz
  have h1 : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  show DifferentiableAt ℝ (fun z => (ksRadius a z * z 2 - a * z 1) / (ksRadius a z ^ 2 + a ^ 2)) z
  fun_prop (disch := assumption)

private lemma diff_k3 (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    DifferentiableAt ℝ (k3f a) z := by
  have hR := ksRadius_diff a z hz
  have h1 : ksRadius a z ≠ 0 := ne_of_gt hz
  show DifferentiableAt ℝ (fun z => z 3 / ksRadius a z) z
  fun_prop (disch := assumption)

private lemma diff_psi (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    DifferentiableAt ℝ (psif a e) z := by
  have hR := ksRadius_diff a z hz
  have h1 : ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2 ≠ 0 := by positivity
  show DifferentiableAt ℝ
    (fun z => e * a * z 3 * ksRadius a z / (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2)) z
  fun_prop (disch := assumption)

private lemma partial_H (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) (i : Fin 4) :
    coordPartial (Hf a e) i z = Hd a e z i :=
  partial_eq_of_line _ _ _ (diff_Hf a e z hz) _ (hasDerivAt_line_H a e z hz i)

private lemma partial_psi (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) (i : Fin 4) :
    coordPartial (psif a e) i z = psid a e z i :=
  partial_eq_of_line _ _ _ (diff_psi a e z hz) _ (hasDerivAt_line_psi a e z hz i)

private lemma partial_A1 (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) (i : Fin 4) :
    coordPartial (fun z => kerrNewmanPotential a e z 1) i z
      = Hd a e z i * k1f a z + Hf a e z * k1d a z i := by
  rw [A1_eq]
  refine partial_eq_of_line _ _ _ ((diff_Hf a e z hz).mul (diff_k1 a z hz)) _ ?_
  have h := (hasDerivAt_line_H a e z hz i).mul (hasDerivAt_line_k1 a z hz i)
  refine h.congr_deriv ?_
  simp only [zero_smul, add_zero]

private lemma partial_A2 (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) (i : Fin 4) :
    coordPartial (fun z => kerrNewmanPotential a e z 2) i z
      = Hd a e z i * k2f a z + Hf a e z * k2d a z i := by
  rw [A2_eq]
  refine partial_eq_of_line _ _ _ ((diff_Hf a e z hz).mul (diff_k2 a z hz)) _ ?_
  have h := (hasDerivAt_line_H a e z hz i).mul (hasDerivAt_line_k2 a z hz i)
  refine h.congr_deriv ?_
  simp only [zero_smul, add_zero]

private lemma partial_A3 (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) (i : Fin 4) :
    coordPartial (fun z => kerrNewmanPotential a e z 3) i z
      = Hd a e z i * k3f a z + Hf a e z * k3d a z i := by
  rw [A3_eq]
  refine partial_eq_of_line _ _ _ ((diff_Hf a e z hz).mul (diff_k3 a z hz)) _ ?_
  have h := (hasDerivAt_line_H a e z hz i).mul (hasDerivAt_line_k3 a z hz i)
  refine h.congr_deriv ?_
  simp only [zero_smul, add_zero]

private lemma ksRadius_inv (a : ℝ) (w : E4) (s : ℝ) :
    ksRadius a (w + s • coordBasis 0) = ksRadius a w := by
  simp [ksRadius, coordBasis]

private lemma A_inv (a e : ℝ) (j : Fin 4) (w : E4) (s : ℝ) :
    kerrNewmanPotential a e (w + s • coordBasis 0) j = kerrNewmanPotential a e w j := by
  simp only [kerrNewmanPotential, ksNull, ksRadius_inv]
  simp [coordBasis]

private lemma F_inv (a e : ℝ) (μ ν : Fin 4) (w : E4) (s : ℝ) :
    kerrNewmanField a e (w + s • coordBasis 0) μ ν = kerrNewmanField a e w μ ν := by
  simp only [kerrNewmanField]
  rw [partial_invariant _ _ (A_inv a e ν), partial_invariant _ _ (A_inv a e μ)]


private lemma iden_12 (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    Hd a e z 1 * k2f a z + Hf a e z * k2d a z 1 - (Hd a e z 2 * k1f a z + Hf a e z * k1d a z 2)
      = psid a e z 3 := by
  have hC := ksRadius_C a z
  have h0 : ksRadius a z ≠ 0 := ne_of_gt hz
  have h1 : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  have h2 : ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2 ≠ 0 := by positivity
  have h1' : a ^ 2 + ksRadius a z ^ 2 ≠ 0 := by positivity
  have h2' : a ^ 2 * z 3 ^ 2 + ksRadius a z ^ 4 ≠ 0 := by positivity
  simp only [Hd, Hf, k1f, k2f, k1d, k2d, psid, dR, cb_11, cb_12, cb_13, cb_21, cb_22, cb_23, cb_31, cb_32, cb_33,
    mul_zero, mul_one, add_zero, zero_add, sub_zero]
  linear_combination (norm := skip)
    (a*e*(ksRadius a z)^3*(3*a^4*(z 3)^2 - a^2*(ksRadius a z)^4 + a^2*(ksRadius a z)^2*(z 3)^2
      - 3*(ksRadius a z)^6) / ((a^2 + (ksRadius a z)^2)^2*(a^2*(z 3)^2 + (ksRadius a z)^4)^3)) * hC
  field_simp
  ring

private lemma iden_23 (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    Hd a e z 2 * k3f a z + Hf a e z * k3d a z 2 - (Hd a e z 3 * k2f a z + Hf a e z * k2d a z 3)
      = psid a e z 1 := by
  have h0 : ksRadius a z ≠ 0 := ne_of_gt hz
  have h1 : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  have h2 : ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2 ≠ 0 := by positivity
  simp only [Hd, Hf, k2f, k3f, k2d, k3d, psid, dR, cb_11, cb_12, cb_13, cb_21, cb_22, cb_23, cb_31, cb_32, cb_33,
    mul_zero, mul_one, add_zero, zero_add, sub_zero]
  field_simp
  ring

private lemma iden_31 (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    Hd a e z 3 * k1f a z + Hf a e z * k1d a z 3 - (Hd a e z 1 * k3f a z + Hf a e z * k3d a z 1)
      = psid a e z 2 := by
  have h0 : ksRadius a z ≠ 0 := ne_of_gt hz
  have h1 : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  have h2 : ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2 ≠ 0 := by positivity
  simp only [Hd, Hf, k1f, k3f, k1d, k3d, psid, dR, cb_11, cb_12, cb_13, cb_21, cb_22, cb_23, cb_31, cb_32, cb_33,
    mul_zero, mul_one, add_zero, zero_add, sub_zero]
  field_simp
  ring


private def G1 (a e : ℝ) (z : E4) : ℝ :=
  e * z 1 * ksRadius a z ^ 5 * (3 * a ^ 2 * z 3 ^ 2 - ksRadius a z ^ 4)
    / (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2) ^ 3

private def G2 (a e : ℝ) (z : E4) : ℝ :=
  e * z 2 * ksRadius a z ^ 5 * (3 * a ^ 2 * z 3 ^ 2 - ksRadius a z ^ 4)
    / (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2) ^ 3

private def G3 (a e : ℝ) (z : E4) : ℝ :=
  e * z 3 * ksRadius a z ^ 3 * (-ksRadius a z ^ 6 - 3 * a ^ 2 * ksRadius a z ^ 4
    + 3 * a ^ 2 * ksRadius a z ^ 2 * z 3 ^ 2 + a ^ 4 * z 3 ^ 2)
    / (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2) ^ 3

private lemma Hd_1 (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) : Hd a e z 1 = G1 a e z := by
  have h0 : ksRadius a z ≠ 0 := ne_of_gt hz
  have h2 : ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2 ≠ 0 := by positivity
  simp only [Hd, G1, dR, cb_11, cb_12, cb_13, mul_zero, mul_one, add_zero, zero_add, sub_zero]
  field_simp
  ring

private lemma Hd_2 (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) : Hd a e z 2 = G2 a e z := by
  have h0 : ksRadius a z ≠ 0 := ne_of_gt hz
  have h2 : ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2 ≠ 0 := by positivity
  simp only [Hd, G2, dR, cb_21, cb_22, cb_23, mul_zero, mul_one, add_zero, zero_add, sub_zero]
  field_simp
  ring

private lemma Hd_3 (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) : Hd a e z 3 = G3 a e z := by
  have h0 : ksRadius a z ≠ 0 := ne_of_gt hz
  have h2 : ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2 ≠ 0 := by positivity
  simp only [Hd, G3, dR, cb_31, cb_32, cb_33, mul_zero, mul_one, add_zero, zero_add, sub_zero]
  field_simp
  ring

private def G1d (a e : ℝ) (z : E4) (k : Fin 4) : ℝ :=
  (((e * coordBasis k 1 * ksRadius a z ^ 5 + e * z 1 * (5 * ksRadius a z ^ 4 * dR a z k))
      * (3 * a ^ 2 * z 3 ^ 2 - ksRadius a z ^ 4)
    + e * z 1 * ksRadius a z ^ 5 * (3 * a ^ 2 * (2 * z 3 * coordBasis k 3)
      - 4 * ksRadius a z ^ 3 * dR a z k)) * (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2) ^ 3
   - e * z 1 * ksRadius a z ^ 5 * (3 * a ^ 2 * z 3 ^ 2 - ksRadius a z ^ 4)
      * (3 * (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2) ^ 2
        * (4 * ksRadius a z ^ 3 * dR a z k + a ^ 2 * (2 * z 3 * coordBasis k 3))))
  / ((ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2) ^ 3) ^ 2

private def G2d (a e : ℝ) (z : E4) (k : Fin 4) : ℝ :=
  (((e * coordBasis k 2 * ksRadius a z ^ 5 + e * z 2 * (5 * ksRadius a z ^ 4 * dR a z k))
      * (3 * a ^ 2 * z 3 ^ 2 - ksRadius a z ^ 4)
    + e * z 2 * ksRadius a z ^ 5 * (3 * a ^ 2 * (2 * z 3 * coordBasis k 3)
      - 4 * ksRadius a z ^ 3 * dR a z k)) * (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2) ^ 3
   - e * z 2 * ksRadius a z ^ 5 * (3 * a ^ 2 * z 3 ^ 2 - ksRadius a z ^ 4)
      * (3 * (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2) ^ 2
        * (4 * ksRadius a z ^ 3 * dR a z k + a ^ 2 * (2 * z 3 * coordBasis k 3))))
  / ((ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2) ^ 3) ^ 2

private def G3d (a e : ℝ) (z : E4) (k : Fin 4) : ℝ :=
  (((e * coordBasis k 3 * ksRadius a z ^ 3 + e * z 3 * (3 * ksRadius a z ^ 2 * dR a z k))
      * (-ksRadius a z ^ 6 - 3 * a ^ 2 * ksRadius a z ^ 4
        + 3 * a ^ 2 * ksRadius a z ^ 2 * z 3 ^ 2 + a ^ 4 * z 3 ^ 2)
    + e * z 3 * ksRadius a z ^ 3 * (-(6 * ksRadius a z ^ 5 * dR a z k)
        - 3 * a ^ 2 * (4 * ksRadius a z ^ 3 * dR a z k)
        + 3 * a ^ 2 * (2 * ksRadius a z * dR a z k * z 3 ^ 2
          + ksRadius a z ^ 2 * (2 * z 3 * coordBasis k 3))
        + a ^ 4 * (2 * z 3 * coordBasis k 3))) * (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2) ^ 3
   - e * z 3 * ksRadius a z ^ 3 * (-ksRadius a z ^ 6 - 3 * a ^ 2 * ksRadius a z ^ 4
        + 3 * a ^ 2 * ksRadius a z ^ 2 * z 3 ^ 2 + a ^ 4 * z 3 ^ 2)
      * (3 * (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2) ^ 2
        * (4 * ksRadius a z ^ 3 * dR a z k + a ^ 2 * (2 * z 3 * coordBasis k 3))))
  / ((ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2) ^ 3) ^ 2

private lemma hasDerivAt_line_G1 (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) (k : Fin 4) :
    HasDerivAt (fun s : ℝ => G1 a e (z + s • coordBasis k)) (G1d a e z k) 0 := by
  have hR := hasDerivAt_line_R a z hz k
  have h1 := hasDerivAt_line_coord z k 1
  have h3 := hasDerivAt_line_coord z k 3
  have h := (((h1.const_mul e).mul (hR.pow 5)).mul (((h3.pow 2).const_mul (3 * a ^ 2)).sub
    (hR.pow 4))).div (((hR.pow 4).add ((h3.pow 2).const_mul (a ^ 2))).pow 3)
    (by simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, zero_smul, add_zero]
        positivity)
  refine h.congr_deriv ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, zero_smul, add_zero, G1d]
  push_cast
  ring

private lemma hasDerivAt_line_G2 (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) (k : Fin 4) :
    HasDerivAt (fun s : ℝ => G2 a e (z + s • coordBasis k)) (G2d a e z k) 0 := by
  have hR := hasDerivAt_line_R a z hz k
  have h2 := hasDerivAt_line_coord z k 2
  have h3 := hasDerivAt_line_coord z k 3
  have h := (((h2.const_mul e).mul (hR.pow 5)).mul (((h3.pow 2).const_mul (3 * a ^ 2)).sub
    (hR.pow 4))).div (((hR.pow 4).add ((h3.pow 2).const_mul (a ^ 2))).pow 3)
    (by simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, zero_smul, add_zero]
        positivity)
  refine h.congr_deriv ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, zero_smul, add_zero, G2d]
  push_cast
  ring

private lemma hasDerivAt_line_G3 (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) (k : Fin 4) :
    HasDerivAt (fun s : ℝ => G3 a e (z + s • coordBasis k)) (G3d a e z k) 0 := by
  have hR := hasDerivAt_line_R a z hz k
  have h3 := hasDerivAt_line_coord z k 3
  have h := (((h3.const_mul e).mul (hR.pow 3)).mul (((((hR.pow 6).neg).sub
    ((hR.pow 4).const_mul (3 * a ^ 2))).add (((hR.pow 2).const_mul (3 * a ^ 2)).mul (h3.pow 2))).add
    ((h3.pow 2).const_mul (a ^ 4)))).div (((hR.pow 4).add ((h3.pow 2).const_mul (a ^ 2))).pow 3)
    (by simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, zero_smul, add_zero]
        positivity)
  refine h.congr_deriv ?_
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.neg_apply, zero_smul,
    add_zero, G3d]
  push_cast
  ring


private lemma lap_iden (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    G1d a e z 1 + G2d a e z 2 + G3d a e z 3 = 0 := by
  have hC := ksRadius_C a z
  have h0 : ksRadius a z ≠ 0 := ne_of_gt hz
  have h2 : ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2 ≠ 0 := by positivity
  have h2' : a ^ 2 * z 3 ^ 2 + ksRadius a z ^ 4 ≠ 0 := by positivity
  simp only [G1d, G2d, G3d, dR, cb_11, cb_12, cb_13, cb_21, cb_22, cb_23, cb_31, cb_32, cb_33,
    mul_zero, mul_one, add_zero, zero_add, sub_zero]
  linear_combination (norm := skip)
    (-3*e*(ksRadius a z)^5*(5*a^4*(z 3)^4 - 10*a^2*(ksRadius a z)^4*(z 3)^2 + (ksRadius a z)^8)
      / (a^2*(z 3)^2 + (ksRadius a z)^4)^5) * hC
  field_simp
  ring


private lemma diff_G1 (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    DifferentiableAt ℝ (G1 a e) z := by
  have hR := ksRadius_diff a z hz
  have h1 : (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2) ^ 3 ≠ 0 := by positivity
  show DifferentiableAt ℝ (fun z => e * z 1 * ksRadius a z ^ 5 * (3 * a ^ 2 * z 3 ^ 2
    - ksRadius a z ^ 4) / (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2) ^ 3) z
  fun_prop (disch := assumption)

private lemma diff_G2 (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    DifferentiableAt ℝ (G2 a e) z := by
  have hR := ksRadius_diff a z hz
  have h1 : (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2) ^ 3 ≠ 0 := by positivity
  show DifferentiableAt ℝ (fun z => e * z 2 * ksRadius a z ^ 5 * (3 * a ^ 2 * z 3 ^ 2
    - ksRadius a z ^ 4) / (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2) ^ 3) z
  fun_prop (disch := assumption)

private lemma diff_G3 (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    DifferentiableAt ℝ (G3 a e) z := by
  have hR := ksRadius_diff a z hz
  have h1 : (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2) ^ 3 ≠ 0 := by positivity
  show DifferentiableAt ℝ (fun z => e * z 3 * ksRadius a z ^ 3 * (-ksRadius a z ^ 6
    - 3 * a ^ 2 * ksRadius a z ^ 4 + 3 * a ^ 2 * ksRadius a z ^ 2 * z 3 ^ 2 + a ^ 4 * z 3 ^ 2)
    / (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2) ^ 3) z
  fun_prop (disch := assumption)

private lemma partial_G1 (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) (k : Fin 4) :
    coordPartial (G1 a e) k z = G1d a e z k :=
  partial_eq_of_line _ _ _ (diff_G1 a e z hz) _ (hasDerivAt_line_G1 a e z hz k)

private lemma partial_G2 (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) (k : Fin 4) :
    coordPartial (G2 a e) k z = G2d a e z k :=
  partial_eq_of_line _ _ _ (diff_G2 a e z hz) _ (hasDerivAt_line_G2 a e z hz k)

private lemma partial_G3 (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) (k : Fin 4) :
    coordPartial (G3 a e) k z = G3d a e z k :=
  partial_eq_of_line _ _ _ (diff_G3 a e z hz) _ (hasDerivAt_line_G3 a e z hz k)

private lemma psi_contDiffAt (a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    ContDiffAt ℝ 2 (psif a e) y := by
  have hR := ksRadius_contDiffAt a y hy
  have h1 : ksRadius a y ^ 4 + a ^ 2 * y 3 ^ 2 ≠ 0 := by positivity
  show ContDiffAt ℝ 2
    (fun z => e * a * z 3 * ksRadius a z / (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2)) y
  fun_prop (disch := assumption)

private lemma fderiv_fderiv_apply_eq (f : E4 → ℝ) (y : E4) (hf : ContDiffAt ℝ 2 f y)
    (v w : E4) :
    fderiv ℝ (fun z => fderiv ℝ f z v) y w = fderiv ℝ (fderiv ℝ f) y w v := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) y :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  rw [fderiv_clm_apply hD (differentiableAt_const v)]
  simp

private lemma partial_partial_symm (f : E4 → ℝ) (y : E4) (hf : ContDiffAt ℝ 2 f y) (i k : Fin 4) :
    coordPartial (fun z => coordPartial f k z) i y
      = coordPartial (fun z => coordPartial f i z) k y := by
  unfold coordPartial
  rw [fderiv_fderiv_apply_eq _ _ hf, fderiv_fderiv_apply_eq _ _ hf]
  exact hf.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]) _ _

private lemma diff_partial (f : E4 → ℝ) (y : E4) (hf : ContDiffAt ℝ 2 f y) (k : Fin 4) :
    DifferentiableAt ℝ (fun z => coordPartial f k z) y := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) y :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  exact hD.clm_apply (differentiableAt_const _)

private lemma partial_on (a : ℝ) (f g : E4 → ℝ) (c d : ℝ) (k : Fin 4) (y : E4)
    (hy : 0 < ksRadius a y) (h : ∀ z, 0 < ksRadius a z → c * f z = d * g z)
    (hg : DifferentiableAt ℝ g y) :
    coordPartial (fun z => c * f z) k y = d * coordPartial g k y := by
  have he : (fun z => c * f z) =ᶠ[nhds y] (fun z => d * g z) := by
    filter_upwards [(isOpen_U a).mem_nhds hy] with z hz using h z hz
  unfold coordPartial
  rw [he.fderiv_eq, fderiv_const_mul hg d]
  simp

private lemma integrand_eq (F : E4 → Matrix (Fin 4) (Fin 4) ℝ) (μ ν : Fin 4) :
    (fun z => ∑ α, ∑ β, minkowski μ α * minkowski ν β * F z α β)
      = fun z => minkowski μ μ * minkowski ν ν * F z μ ν := by
  funext z
  simp [minkowski, Matrix.diagonal_apply]

private lemma term0 (a e : ℝ) (y : E4) (ν : Fin 4) :
    coordPartial (fun z => minkowski 0 0 * minkowski ν ν * kerrNewmanField a e z 0 ν) 0 y = 0 :=
  partial_zero_of_invariant _ y (fun w s => by simp only [F_inv])

private lemma term_diag (a e : ℝ) (y : E4) (μ k : Fin 4) (c : ℝ) :
    coordPartial (fun z => c * kerrNewmanField a e z μ μ) k y = 0 := by
  have : (fun z => c * kerrNewmanField a e z μ μ) = fun _ => 0 := by
    funext z; simp [kerrNewmanField]
  rw [this]; unfold coordPartial; simp

private lemma F_i0 (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) (i : Fin 4) :
    kerrNewmanField a e z i 0 = Hd a e z i := by
  simp only [kerrNewmanField]
  rw [A0_eq, partial_H a e z hz, partial_zero_of_invariant _ _ (A_inv a e i)]
  ring

private lemma F_12 (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    kerrNewmanField a e z 1 2 = coordPartial (psif a e) 3 z := by
  simp only [kerrNewmanField]
  rw [partial_A2 a e z hz, partial_A1 a e z hz, partial_psi a e z hz]
  exact iden_12 a e z hz

private lemma F_23 (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    kerrNewmanField a e z 2 3 = coordPartial (psif a e) 1 z := by
  simp only [kerrNewmanField]
  rw [partial_A3 a e z hz, partial_A2 a e z hz, partial_psi a e z hz]
  exact iden_23 a e z hz

private lemma F_31 (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    kerrNewmanField a e z 3 1 = coordPartial (psif a e) 2 z := by
  simp only [kerrNewmanField]
  rw [partial_A1 a e z hz, partial_A3 a e z hz, partial_psi a e z hz]
  exact iden_31 a e z hz

private lemma F_anti (a e : ℝ) (z : E4) (μ ν : Fin 4) :
    kerrNewmanField a e z ν μ = - kerrNewmanField a e z μ ν := by
  simp only [kerrNewmanField]; ring


private lemma maxwell_0 (a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    ∑ μ, coordPartial (fun z => ∑ α, ∑ β, minkowski μ α * minkowski 0 β
      * kerrNewmanField a e z α β) μ y = 0 := by
  simp only [integrand_eq]
  rw [Fin.sum_univ_four, term0]
  rw [partial_on a (fun z => kerrNewmanField a e z 1 0) (G1 a e) (minkowski 1 1 * minkowski 0 0)
    (-1) 1 y hy (fun z hz => by rw [F_i0 a e z hz, Hd_1 a e z hz]; simp [minkowski])
    (diff_G1 a e y hy)]
  rw [partial_on a (fun z => kerrNewmanField a e z 2 0) (G2 a e) (minkowski 2 2 * minkowski 0 0)
    (-1) 2 y hy (fun z hz => by rw [F_i0 a e z hz, Hd_2 a e z hz]; simp [minkowski])
    (diff_G2 a e y hy)]
  rw [partial_on a (fun z => kerrNewmanField a e z 3 0) (G3 a e) (minkowski 3 3 * minkowski 0 0)
    (-1) 3 y hy (fun z hz => by rw [F_i0 a e z hz, Hd_3 a e z hz]; simp [minkowski])
    (diff_G3 a e y hy)]
  rw [partial_G1 a e y hy, partial_G2 a e y hy, partial_G3 a e y hy]
  linear_combination (-1 : ℝ) * lap_iden a e y hy

private lemma maxwell_1 (a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    ∑ μ, coordPartial (fun z => ∑ α, ∑ β, minkowski μ α * minkowski 1 β
      * kerrNewmanField a e z α β) μ y = 0 := by
  have hψ := psi_contDiffAt a e y hy
  simp only [integrand_eq]
  rw [Fin.sum_univ_four, term0, term_diag]
  rw [partial_on a (fun z => kerrNewmanField a e z 2 1) (fun z => coordPartial (psif a e) 3 z)
    (minkowski 2 2 * minkowski 1 1) (-1) 2 y hy
    (fun z hz => by rw [F_anti a e z 1 2, F_12 a e z hz]; simp [minkowski])
    (diff_partial _ y hψ 3)]
  rw [partial_on a (fun z => kerrNewmanField a e z 3 1) (fun z => coordPartial (psif a e) 2 z)
    (minkowski 3 3 * minkowski 1 1) 1 3 y hy
    (fun z hz => by rw [F_31 a e z hz]; simp [minkowski])
    (diff_partial _ y hψ 2)]
  rw [partial_partial_symm _ y hψ 2 3]
  ring

private lemma maxwell_2 (a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    ∑ μ, coordPartial (fun z => ∑ α, ∑ β, minkowski μ α * minkowski 2 β
      * kerrNewmanField a e z α β) μ y = 0 := by
  have hψ := psi_contDiffAt a e y hy
  simp only [integrand_eq]
  rw [Fin.sum_univ_four, term0, term_diag]
  rw [partial_on a (fun z => kerrNewmanField a e z 1 2) (fun z => coordPartial (psif a e) 3 z)
    (minkowski 1 1 * minkowski 2 2) 1 1 y hy
    (fun z hz => by rw [F_12 a e z hz]; simp [minkowski])
    (diff_partial _ y hψ 3)]
  rw [partial_on a (fun z => kerrNewmanField a e z 3 2) (fun z => coordPartial (psif a e) 1 z)
    (minkowski 3 3 * minkowski 2 2) (-1) 3 y hy
    (fun z hz => by rw [F_anti a e z 2 3, F_23 a e z hz]; simp [minkowski])
    (diff_partial _ y hψ 1)]
  rw [partial_partial_symm _ y hψ 1 3]
  ring

private lemma maxwell_3 (a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    ∑ μ, coordPartial (fun z => ∑ α, ∑ β, minkowski μ α * minkowski 3 β
      * kerrNewmanField a e z α β) μ y = 0 := by
  have hψ := psi_contDiffAt a e y hy
  simp only [integrand_eq]
  rw [Fin.sum_univ_four, term0, term_diag]
  rw [partial_on a (fun z => kerrNewmanField a e z 1 3) (fun z => coordPartial (psif a e) 2 z)
    (minkowski 1 1 * minkowski 3 3) (-1) 1 y hy
    (fun z hz => by rw [F_anti a e z 3 1, F_31 a e z hz]; simp [minkowski])
    (diff_partial _ y hψ 2)]
  rw [partial_on a (fun z => kerrNewmanField a e z 2 3) (fun z => coordPartial (psif a e) 1 z)
    (minkowski 2 2 * minkowski 3 3) 1 2 y hy
    (fun z hz => by rw [F_23 a e z hz]; simp [minkowski])
    (diff_partial _ y hψ 1)]
  rw [partial_partial_symm _ y hψ 1 2]
  ring

end NoHair.Sol_flat_maxwell
end

open NoHair NoHair.Sol_flat_maxwell

theorem solution (a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    ∀ ν, ∑ μ, coordPartial
      (fun z => ∑ α, ∑ β, minkowski μ α * minkowski ν β * kerrNewmanField a e z α β) μ y = 0 := by
  intro ν
  fin_cases ν
  · exact maxwell_0 a e y hy
  · exact maxwell_1 a e y hy
  · exact maxwell_2 a e y hy
  · exact maxwell_3 a e y hy
