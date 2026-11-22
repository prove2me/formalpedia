-- Prove2me | solution 1 for McLeishCLT.MDA.exp_approx
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T20:05:52.822162+00:00
-- url     : https://prove2.me/submissions/7bc64eda-98e1-4999-853f-a06033434ce5

import Mathlib
import Definitions.Def_McLeishCLT_MDA_Setting

set_option autoImplicit false

namespace McLeishCLT.MDA.ExpApproxProof

open Complex

theorem one_add_I_mul_ne_zero (t : ℝ) : (1 + I * (t : ℂ)) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

theorem one_le_norm_one_add_I_mul (t : ℝ) : 1 ≤ ‖1 + I * (t : ℂ)‖ := by
  have h := Complex.abs_re_le_norm (1 + I * (t : ℂ))
  simpa using h

/-- `r'(t) = i + t - i/(1 + it)`. -/
theorem hasDerivAt_remR (t : ℝ) :
    HasDerivAt remR (I + (t : ℂ) - I / (1 + I * (t : ℂ))) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
  have hI : HasDerivAt (fun s : ℝ => I * (s : ℂ)) (I * 1) t := h1.const_mul I
  have hsq : HasDerivAt (fun s : ℝ => (s : ℂ) ^ 2 / 2) ((2 : ℕ) * (t : ℂ) ^ (2 - 1) * 1 / 2) t :=
    (h1.pow 2).div_const 2
  have hlin : HasDerivAt (fun s : ℝ => 1 + I * (s : ℂ)) (0 + I * 1) t :=
    (hasDerivAt_const t (1 : ℂ)).add hI
  have hslit : (1 + I * (t : ℂ)) ∈ Complex.slitPlane := by
    left
    simp
  have hlog : HasDerivAt (fun s : ℝ => Complex.log (1 + I * (s : ℂ)))
      ((0 + I * 1) / (1 + I * (t : ℂ))) t := hlin.clog_real hslit
  have hall := (hI.add hsq).sub hlog
  have hfun : remR = fun s : ℝ => I * (s : ℂ) + (s : ℂ) ^ 2 / 2 - Complex.log (1 + I * (s : ℂ)) := by
    funext s
    rfl
  rw [hfun]
  have hall' : HasDerivAt
      (fun s : ℝ => I * (s : ℂ) + (s : ℂ) ^ 2 / 2 - Complex.log (1 + I * (s : ℂ)))
      (I * 1 + ((2 : ℕ) : ℂ) * (t : ℂ) ^ (2 - 1) * 1 / 2 - (0 + I * 1) / (1 + I * (t : ℂ))) t :=
    hall
  refine hall'.congr_deriv ?_
  rw [show (2 - 1 : ℕ) = 1 from rfl, pow_one]
  push_cast
  ring

/-- `‖r'(t)‖ = t² / ‖1 + it‖ ≤ t²`. -/
theorem norm_deriv_remR_le (t : ℝ) : ‖I + (t : ℂ) - I / (1 + I * (t : ℂ))‖ ≤ t ^ 2 := by
  have hne := one_add_I_mul_ne_zero t
  have heq : I + (t : ℂ) - I / (1 + I * (t : ℂ)) = I * (t : ℂ) ^ 2 / (1 + I * (t : ℂ)) := by
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [heq, norm_div, norm_mul, Complex.norm_I, one_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  have h1 := one_le_norm_one_add_I_mul t
  calc t ^ 2 / ‖1 + I * (t : ℂ)‖ ≤ t ^ 2 / 1 :=
        div_le_div_of_nonneg_left (sq_nonneg t) one_pos h1
    _ = t ^ 2 := div_one _

end McLeishCLT.MDA.ExpApproxProof

open Complex McLeishCLT.MDA McLeishCLT.MDA.ExpApproxProof

theorem solution (x : ℝ) :
    Complex.exp (Complex.I * (x : ℂ)) = (1 + Complex.I * (x : ℂ)) * Complex.exp (-(x : ℂ) ^ 2 / 2 + remR x) ∧
      (|x| < 1 → ‖remR x‖ ≤ |x| ^ 3) := by
  constructor
  · have hne := one_add_I_mul_ne_zero x
    have h : -(x : ℂ) ^ 2 / 2 + remR x = I * (x : ℂ) - Complex.log (1 + I * (x : ℂ)) := by
      unfold remR
      ring
    rw [h, Complex.exp_sub, Complex.exp_log hne]
    field_simp
  · intro _
    have hmem0 : (0 : ℝ) ∈ Set.Icc (-|x|) |x| := ⟨by linarith [abs_nonneg x], abs_nonneg x⟩
    have hmemx : x ∈ Set.Icc (-|x|) |x| := ⟨neg_abs_le x, le_abs_self x⟩
    have hbound : ∀ t ∈ Set.Icc (-|x|) |x|, ‖I + (t : ℂ) - I / (1 + I * (t : ℂ))‖ ≤ x ^ 2 := by
      intro t ht
      refine (norm_deriv_remR_le t).trans ?_
      have : |t| ≤ |x| := abs_le.mpr ⟨ht.1, ht.2⟩
      nlinarith [abs_nonneg t, sq_abs t, sq_abs x]
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t _ => (hasDerivAt_remR t).hasDerivWithinAt) hbound (convex_Icc _ _) hmem0 hmemx
    have h0 : remR 0 = 0 := by simp [remR]
    rw [h0, sub_zero, sub_zero, Real.norm_eq_abs] at hmvt
    calc ‖remR x‖ ≤ x ^ 2 * |x| := hmvt
      _ = |x| ^ 3 := by rw [← sq_abs]; ring
