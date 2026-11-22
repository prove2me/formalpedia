-- Prove2me | solution 1 for MasulloRH.augmented_theta_gram_truncation_error
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T16:09:12.995146+00:00
-- url     : https://prove2.me/submissions/ebd0678c-a0a6-4e4d-bf05-d7b190f4cfab

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Theorems.Thm_MasulloRH_theta_reflection
import Theorems.Thm_MasulloRH_theta_gaussian_truncation_error
import Theorems.Thm_MasulloRH_finite_theta_approximation_excludes_rectangle_zeros

open MasulloRH.GaussianApproximation

set_option autoImplicit false

namespace MasulloRH.GramTailEnvelopeBounds

lemma log_four_eq_two_log_two : Real.log 4 = 2 * Real.log 2 := by
  simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num, Nat.cast_ofNat] using
    Real.log_pow (2 : ℝ) 2

lemma exp_ge_half {x : ℝ} (hx : -Real.log 2 ≤ x) : 1 / 2 ≤ Real.exp x := by
  have h := Real.exp_le_exp.mpr hx
  have he : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rwa [he] at h

lemma alpha_ge_quarter_pi {x : ℝ} (hx : -Real.log 2 ≤ x) :
    Real.pi / 4 ≤ Real.pi * (Real.exp x) ^ 2 := by
  have he := exp_ge_half hx
  have hs : (1 / 4 : ℝ) ≤ (Real.exp x) ^ 2 := by
    nlinarith [sq_nonneg (Real.exp x - 1 / 2)]
  have h := mul_le_mul_of_nonneg_left hs Real.pi_pos.le
  nlinarith

lemma reflected_ge_threshold {x : ℝ} (hx : x ≤ -Real.log 2) :
    -Real.log 2 ≤ -x - Real.log 4 := by
  rw [log_four_eq_two_log_two]
  linarith

lemma reflected_exp_sq (x : ℝ) :
    (Real.exp (-x - Real.log 4)) ^ 2 = (Real.exp (-x)) ^ 2 / 16 := by
  rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  ring

lemma exp_neg_three_le_half (a : ℝ) (ha : Real.pi / 4 ≤ a) :
    Real.exp (-3 * a) ≤ 1 / 2 := by
  have he : 2 ≤ Real.exp (3 * a) := by
    have h := Real.add_one_le_exp (3 * a)
    nlinarith [Real.pi_gt_three]
  calc
    Real.exp (-3 * a) = 1 / Real.exp (3 * a) := by
      rw [show -3 * a = -(3 * a) by ring, Real.exp_neg, one_div]
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) he

lemma tail_denominator_ge_half (a : ℝ) (K : ℕ) (ha : Real.pi / 4 ≤ a) :
    1 / 2 ≤ 1 - Real.exp (-a * (2 * (K : ℝ) + 3)) := by
  have ha0 : 0 ≤ a := by nlinarith [Real.pi_pos]
  have he : Real.exp (-a * (2 * (K : ℝ) + 3)) ≤ Real.exp (-3 * a) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg ha0 (show (0 : ℝ) ≤ K by positivity)]
  linarith [exp_neg_three_le_half a ha]

lemma zero_tail_bound_le (a : ℝ) (ha : Real.pi / 4 ≤ a) :
    12 * Real.exp (-a) / (1 - Real.exp (-3 * a)) ≤ 24 * Real.exp (-a) := by
  have hd : (1 / 2 : ℝ) ≤ 1 - Real.exp (-3 * a) := by
    linarith [exp_neg_three_le_half a ha]
  apply (div_le_iff₀ (by linarith : 0 < 1 - Real.exp (-3 * a))).mpr
  nlinarith [mul_nonneg (Real.exp_nonneg (-a)) (sub_nonneg.mpr hd)]

end MasulloRH.GramTailEnvelopeBounds

open MasulloRH.GramTailEnvelopeBounds

lemma MasulloRH.GramTailEnvelopes.norm_reflection (x : ℝ) :
    ‖theta x‖ = (Real.exp (-x) / 2) * ‖theta (-x - Real.log 4)‖ := by
  rw [MasulloRH.theta_reflection x, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos (Real.exp_pos (-x)) (by norm_num : (0 : ℝ) < 2))]

/-- Explicit right-side Gaussian envelope, valid from the reflection midpoint onward. -/
theorem MasulloRH.GramTailEnvelopes.norm_le_right (x : ℝ) (hx : -Real.log 2 ≤ x) :
    ‖theta x‖ ≤ 24 * Real.exp (-Real.pi * (Real.exp x) ^ 2) := by
  have h₀ := MasulloRH.theta_gaussian_truncation_error x 0
  simp only [Finset.range_zero, Finset.sum_empty, mul_zero, sub_zero,
    Nat.cast_zero, zero_add, one_pow, mul_one] at h₀
  have hbound := zero_tail_bound_le (Real.pi * (Real.exp x) ^ 2) (alpha_ge_quarter_pi hx)
  have he₁ : -(Real.pi * (Real.exp x) ^ 2) = -Real.pi * (Real.exp x) ^ 2 := by ring
  have he₃ : -3 * (Real.pi * (Real.exp x) ^ 2) = -Real.pi * (Real.exp x) ^ 2 * 3 := by ring
  rw [he₁, he₃] at hbound
  exact h₀.trans hbound

/-- Explicit reflected Gaussian envelope on the entire left half-line. -/
theorem MasulloRH.GramTailEnvelopes.norm_le_left (x : ℝ) (hx : x ≤ -Real.log 2) :
    ‖theta x‖ ≤ 12 * Real.exp (-x) *
      Real.exp (-(Real.pi / 16) * (Real.exp (-x)) ^ 2) := by
  rw [MasulloRH.GramTailEnvelopes.norm_reflection x]
  calc
    _ ≤ (Real.exp (-x) / 2) *
        (24 * Real.exp (-Real.pi * (Real.exp (-x - Real.log 4)) ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (MasulloRH.GramTailEnvelopes.norm_le_right _ (reflected_ge_threshold hx)) (by positivity)
    _ = _ := by
      rw [reflected_exp_sq]
      have he : -Real.pi * ((Real.exp (-x)) ^ 2 / 16) =
          -(Real.pi / 16) * (Real.exp (-x)) ^ 2 := by ring
      rw [he]
      ring


set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate

namespace MasulloRH.GramTail

/-- An exponential envelope gives an explicit right-ray integral bound. -/
theorem norm_integral_Ioi_le_exp_envelope (f : ℝ → ℂ) (R C ell : ℝ)
    (hell : 0 < ell)
    (hbound : ∀ x : ℝ, R ≤ x → ‖f x‖ ≤ C * Real.exp (-ell * (x - R))) :
    ‖∫ x : ℝ in Ioi R, f x‖ ≤ C / ell := by
  have hform (x : ℝ) :
      C * Real.exp (-ell * (x - R)) =
        (C * Real.exp (ell * R)) * Real.exp ((-ell) * x) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    ring
  have hi : IntegrableOn (fun x : ℝ => C * Real.exp (-ell * (x - R))) (Ioi R) := by
    simp_rw [hform]
    exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos hell) R).const_mul _
  have hle : ‖∫ x : ℝ in Ioi R, f x‖ ≤
      ∫ x : ℝ in Ioi R, C * Real.exp (-ell * (x - R)) := by
    apply norm_integral_le_of_norm_le hi
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hbound x hx.le
  apply hle.trans_eq
  simp_rw [hform]
  rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hell), neg_div_neg_eq,
    ← mul_div_assoc]
  congr 1
  rw [mul_assoc, ← Real.exp_add]
  simp

/-- The corresponding explicit left-ray bound, obtained by reflection. -/
theorem norm_integral_Iic_le_exp_envelope (f : ℝ → ℂ) (R C ell : ℝ)
    (hell : 0 < ell)
    (hbound : ∀ x : ℝ, x ≤ -R → ‖f x‖ ≤ C * Real.exp (-ell * (-x - R))) :
    ‖∫ x : ℝ in Iic (-R), f x‖ ≤ C / ell := by
  rw [← integral_comp_neg_Ioi R f]
  apply norm_integral_Ioi_le_exp_envelope (fun x => f (-x)) R C ell hell
  intro x hx
  simpa only [neg_neg] using hbound (-x) (by linarith)

/-- Explicit truncation error for a weighted Gram entry, from exponential
envelopes for its two columns on both discarded rays. -/
theorem weighted_gram_truncation_of_ray_envelopes
    (f g : ℝ → ℂ) (c b R Cf Cg Df Dg ellf ellg μf μg : ℝ)
    (hR : 0 ≤ R) (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hDf : 0 ≤ Df) (hDg : 0 ≤ Dg)
    (hplus : 0 < ellf + ellg - 2 * (c + b))
    (hminus : 0 < μf + μg + 2 * (c - b))
    (hfp : ∀ x : ℝ, R ≤ x → ‖f x‖ ≤ Cf * Real.exp (-ellf * (x - R)))
    (hgp : ∀ x : ℝ, R ≤ x → ‖g x‖ ≤ Cg * Real.exp (-ellg * (x - R)))
    (hfm : ∀ x : ℝ, x ≤ -R → ‖f x‖ ≤ Df * Real.exp (-μf * (-x - R)))
    (hgm : ∀ x : ℝ, x ≤ -R → ‖g x‖ ≤ Dg * Real.exp (-μg * (-x - R)))
    (hI : Integrable (fun x : ℝ =>
      (Real.exp (2*c*x + 2*b*|x|) : ℂ) * conj (f x) * g x)) :
    ‖(∫ x : ℝ, (Real.exp (2*c*x + 2*b*|x|) : ℂ) * conj (f x) * g x) -
      ∫ x : ℝ in Icc (-R) R,
        (Real.exp (2*c*x + 2*b*|x|) : ℂ) * conj (f x) * g x‖ ≤
      Cf * Cg * Real.exp (2 * (c + b) * R) / (ellf + ellg - 2 * (c + b)) +
      Df * Dg * Real.exp (-2 * (c - b) * R) / (μf + μg + 2 * (c - b)) := by
  let F (x : ℝ) : ℂ := (Real.exp (2*c*x + 2*b*|x|) : ℂ) * conj (f x) * g x
  have hn (x : ℝ) : ‖F x‖ = Real.exp (2*c*x + 2*b*|x|) * ‖f x‖ * ‖g x‖ := by
    simp only [F, norm_mul, Complex.norm_conj, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_nonneg _)]
  have hp : ‖∫ x : ℝ in Ioi R, F x‖ ≤
      Cf * Cg * Real.exp (2 * (c + b) * R) / (ellf + ellg - 2 * (c + b)) := by
    apply norm_integral_Ioi_le_exp_envelope _ _ _ _ hplus
    intro x hx
    rw [hn, abs_of_nonneg (hR.trans hx)]
    calc
      _ ≤ Real.exp (2*c*x + 2*b*x) *
          (Cf * Real.exp (-ellf * (x - R))) * (Cg * Real.exp (-ellg * (x - R))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hfp x hx) (Real.exp_nonneg _))
          (hgp x hx) (norm_nonneg _) (by positivity)
      _ = _ := by
        rw [show Real.exp (2*c*x + 2*b*x) *
            (Cf * Real.exp (-ellf * (x - R))) * (Cg * Real.exp (-ellg * (x - R))) =
          (Cf * Cg) * (Real.exp (2*c*x + 2*b*x) * Real.exp (-ellf * (x - R)) *
            Real.exp (-ellg * (x - R))) by ring]
        rw [← Real.exp_add, ← Real.exp_add, mul_assoc (Cf * Cg), ← Real.exp_add]
        congr 2
        ring
  have hm : ‖∫ x : ℝ in Iic (-R), F x‖ ≤
      Df * Dg * Real.exp (-2 * (c - b) * R) / (μf + μg + 2 * (c - b)) := by
    apply norm_integral_Iic_le_exp_envelope _ _ _ _ hminus
    intro x hx
    rw [hn, abs_of_nonpos (hx.trans (neg_nonpos.mpr hR))]
    calc
      _ ≤ Real.exp (2*c*x + 2*b*(-x)) *
          (Df * Real.exp (-μf * (-x - R))) * (Dg * Real.exp (-μg * (-x - R))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hfm x hx) (Real.exp_nonneg _))
          (hgm x hx) (norm_nonneg _) (by positivity)
      _ = _ := by
        rw [show Real.exp (2*c*x + 2*b*(-x)) *
            (Df * Real.exp (-μf * (-x - R))) * (Dg * Real.exp (-μg * (-x - R))) =
          (Df * Dg) * (Real.exp (2*c*x + 2*b*(-x)) * Real.exp (-μf * (-x - R)) *
            Real.exp (-μg * (-x - R))) by ring]
        rw [← Real.exp_add, ← Real.exp_add, mul_assoc (Df * Dg), ← Real.exp_add]
        congr 2
        ring
  have hsplit : (∫ x : ℝ, F x) - ∫ x : ℝ in Icc (-R) R, F x =
      (∫ x : ℝ in Iic (-R), F x) + ∫ x : ℝ in Ioi R, F x := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (show -R ≤ R by linarith),
      ← intervalIntegral.integral_Iic_sub_Iic hI.integrableOn hI.integrableOn,
      ← intervalIntegral.integral_Iic_add_Ioi hI.integrableOn hI.integrableOn]
    abel
  change ‖(∫ x : ℝ, F x) - ∫ x : ℝ in Icc (-R) R, F x‖ ≤ _
  rw [hsplit]
  exact (norm_add_le _ _).trans (by linarith)

/-- Convexity of the exponential turns a double-exponential Gaussian bound into
an explicit exponential ray envelope. -/
theorem exp_doubleexp_ray_le (A R x : ℝ) (hA : 0 ≤ A) :
    Real.exp (-A * (Real.exp x)^2) ≤
      Real.exp (-A * (Real.exp R)^2) *
        Real.exp (-(2 * A * (Real.exp R)^2) * (x-R)) := by
  have ht := Real.add_one_le_exp (2 * (x-R))
  have he : (Real.exp R)^2 * Real.exp (2*(x-R)) = (Real.exp x)^2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_nat_mul]
    congr 1
    ring
  have hmajor := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ A * (Real.exp R)^2)
  simp only [mul_assoc] at hmajor
  rw [he] at hmajor
  rw [← Real.exp_add, Real.exp_le_exp]
  nlinarith

/-- The Gaussian admits the analogous tangent exponential envelope. -/
theorem exp_gaussian_ray_le (A R x : ℝ) (hA : 0 ≤ A) :
    Real.exp (-A * x^2) ≤
      Real.exp (-A * R^2) * Real.exp (-(2*A*R) * (x-R)) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  nlinarith [mul_nonneg hA (sq_nonneg (x-R))]

/-- A linear exponential factor is absorbed into the decay rate. -/
theorem exp_linear_doubleexp_ray_le (A q R x : ℝ) (hA : 0 ≤ A) :
    Real.exp (q*x - A * (Real.exp x)^2) ≤
      Real.exp (q*R - A * (Real.exp R)^2) *
        Real.exp (-(2 * A * (Real.exp R)^2 - q) * (x-R)) := by
  have ht := Real.add_one_le_exp (2 * (x-R))
  have he : (Real.exp R)^2 * Real.exp (2*(x-R)) = (Real.exp x)^2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_nat_mul]
    congr 1
    ring
  have hmajor := mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ A * (Real.exp R)^2)
  simp only [mul_assoc] at hmajor
  rw [he] at hmajor
  rw [← Real.exp_add, Real.exp_le_exp]
  nlinarith

theorem shifted_right_ray_of_theta_envelope (f : ℝ → ℂ)
    (hf : ∀ z : ℝ, -Real.log 2 ≤ z →
      ‖f z‖ ≤ 24 * Real.exp (-Real.pi * (Real.exp z)^2))
    (y R x : ℝ) (hR : y - Real.log 2 ≤ R) (hx : R ≤ x) :
    ‖f (x-y)‖ ≤
      (24 * Real.exp (-Real.pi * (Real.exp (R-y))^2)) *
        Real.exp (-(2 * Real.pi * (Real.exp (R-y))^2) * (x-R)) := by
  apply (hf (x-y) (by linarith)).trans
  have he := mul_le_mul_of_nonneg_left
    (exp_doubleexp_ray_le Real.pi (R-y) (x-y) Real.pi_pos.le)
    (by norm_num : (0 : ℝ) ≤ 24)
  simpa only [show (x-y)-(R-y) = x-R by ring, mul_assoc] using he

theorem shifted_left_ray_of_theta_envelope (f : ℝ → ℂ)
    (hf : ∀ z : ℝ, z ≤ -Real.log 2 →
      ‖f z‖ ≤ 12 * Real.exp (-z) *
        Real.exp (-(Real.pi/16) * (Real.exp (-z))^2))
    (y R x : ℝ) (hR : Real.log 2 - y ≤ R) (hx : x ≤ -R) :
    ‖f (x-y)‖ ≤
      (12 * Real.exp (R+y - (Real.pi/16) * (Real.exp (R+y))^2)) *
        Real.exp (-(2 * (Real.pi/16) * (Real.exp (R+y))^2 - 1) * (-x-R)) := by
  apply (hf (x-y) (by linarith)).trans
  have he := mul_le_mul_of_nonneg_left
    (exp_linear_doubleexp_ray_le (Real.pi/16) 1 (R+y) (-(x-y)) (by positivity))
    (by norm_num : (0 : ℝ) ≤ 12)
  rw [show -(x-y)-(R+y) = -x-R by ring] at he
  simpa only [one_mul, mul_assoc, ← Real.exp_add, sub_eq_add_neg, neg_mul] using he

end MasulloRH.GramTail

set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators ComplexConjugate
open MasulloRH.GaussianApproximation

namespace MasulloRH.GramTail

private theorem pulse_norm (T x : ℝ) (hT : 0 ≤ T) :
    ‖pulse T x‖ = ((T+1)/Real.sqrt Real.pi) * Real.exp (-(T+1)^2*x^2) := by
  have hC : 0 ≤ (T+1)/Real.sqrt Real.pi := by positivity
  rw [pulse, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC,
    Complex.norm_exp, ← Complex.ofReal_pow, Complex.neg_re, Complex.ofReal_re]
  congr 2
  ring

private theorem pulse_right_ray (T R x : ℝ) (hT : 0 ≤ T) :
    ‖pulse T x‖ ≤
      (((T+1)/Real.sqrt Real.pi) * Real.exp (-(T+1)^2*R^2)) *
        Real.exp (-(2*(T+1)^2*R)*(x-R)) := by
  rw [pulse_norm T x hT]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (exp_gaussian_ray_le ((T+1)^2) R x (sq_nonneg _))
    (by positivity : 0 ≤ (T+1)/Real.sqrt Real.pi)

private theorem pulse_left_ray (T R x : ℝ) (hT : 0 ≤ T) :
    ‖pulse T x‖ ≤
      (((T+1)/Real.sqrt Real.pi) * Real.exp (-(T+1)^2*R^2)) *
        Real.exp (-(2*(T+1)^2*R)*(-x-R)) := by
  rw [pulse_norm T x hT]
  simpa only [neg_sq, mul_assoc] using mul_le_mul_of_nonneg_left
    (exp_gaussian_ray_le ((T+1)^2) R (-x) (sq_nonneg _))
    (by positivity : 0 ≤ (T+1)/Real.sqrt Real.pi)

end MasulloRH.GramTail

/-- A fully explicit exterior-integration error for every entry of the actual
augmented Gaussian-pulse/theta Gram matrix. The denominator conditions are
finite numerical inequalities, not analytic approximation hypotheses. -/
theorem solution
    (m : ℕ) (T c b R : ℝ) (y : Fin m → ℝ)
    (hT : 0 ≤ T) (hR : 0 ≤ R) (hleft : 0 < c-b) (hright : c+b < 1)
    (hshift : ∀ i : Fin m, |y i - Real.log 2| ≤ R) :
    let u : Fin (m+1) → ℝ → ℂ := Fin.cons (pulse T)
      (fun i x => theta (x-y i))
    let Ap : Fin (m+1) → ℝ := Fin.cons
      (((T+1)/Real.sqrt Real.pi) * Real.exp (-(T+1)^2*R^2))
      (fun i => 24 * Real.exp (-Real.pi * (Real.exp (R-y i))^2))
    let Lp : Fin (m+1) → ℝ := Fin.cons (2*(T+1)^2*R)
      (fun i => 2 * Real.pi * (Real.exp (R-y i))^2)
    let Am : Fin (m+1) → ℝ := Fin.cons
      (((T+1)/Real.sqrt Real.pi) * Real.exp (-(T+1)^2*R^2))
      (fun i => 12 * Real.exp (R+y i - (Real.pi/16) * (Real.exp (R+y i))^2))
    let Lm : Fin (m+1) → ℝ := Fin.cons (2*(T+1)^2*R)
      (fun i => 2 * (Real.pi/16) * (Real.exp (R+y i))^2 - 1)
    (∀ i j : Fin (m+1), 0 < Lp i + Lp j - 2*(c+b)) →
    (∀ i j : Fin (m+1), 0 < Lm i + Lm j + 2*(c-b)) →
    ∀ i j : Fin (m+1),
      ‖(∫ x : ℝ, (Real.exp (2*c*x + 2*b*|x|) : ℂ) * conj (u i x) * u j x) -
        ∫ x : ℝ in Icc (-R) R,
          (Real.exp (2*c*x + 2*b*|x|) : ℂ) * conj (u i x) * u j x‖ ≤
        Ap i * Ap j * Real.exp (2*(c+b)*R) / (Lp i + Lp j - 2*(c+b)) +
        Am i * Am j * Real.exp (-2*(c-b)*R) / (Lm i + Lm j + 2*(c-b)) := by
  intro u Ap Lp Am Lm hplus hminus i j
  have hAp (k : Fin (m+1)) : 0 ≤ Ap k := by
    refine Fin.cases ?_ (fun l => ?_) k <;>
      simp only [Ap, Fin.cons_zero, Fin.cons_succ] <;> positivity
  have hAm (k : Fin (m+1)) : 0 ≤ Am k := by
    refine Fin.cases ?_ (fun l => ?_) k <;>
      simp only [Am, Fin.cons_zero, Fin.cons_succ] <;> positivity
  have hup (k : Fin (m+1)) (x : ℝ) (hx : R ≤ x) :
      ‖u k x‖ ≤ Ap k * Real.exp (-Lp k * (x-R)) := by
    refine Fin.cases ?_ (fun l => ?_) k
    · simpa only [u, Ap, Lp, Fin.cons_zero] using
        MasulloRH.GramTail.pulse_right_ray T R x hT
    · simpa only [u, Ap, Lp, Fin.cons_succ] using
        MasulloRH.GramTail.shifted_right_ray_of_theta_envelope theta
          MasulloRH.GramTailEnvelopes.norm_le_right (y l) R x (abs_le.mp (hshift l)).2 hx
  have hum (k : Fin (m+1)) (x : ℝ) (hx : x ≤ -R) :
      ‖u k x‖ ≤ Am k * Real.exp (-Lm k * (-x-R)) := by
    refine Fin.cases ?_ (fun l => ?_) k
    · simpa only [u, Am, Lm, Fin.cons_zero] using
        MasulloRH.GramTail.pulse_left_ray T R x hT
    · have hs : Real.log 2 - y l ≤ R := by
        have hh := (abs_le.mp (hshift l)).1
        linarith
      simpa only [u, Am, Lm, Fin.cons_succ] using
        MasulloRH.GramTail.shifted_left_ray_of_theta_envelope theta
          MasulloRH.GramTailEnvelopes.norm_le_left (y l) R x hs hx
  have hI : Integrable (fun x : ℝ =>
      (Real.exp (2*c*x + 2*b*|x|) : ℂ) * conj (u i x) * u j x) :=
    (MasulloRH.finite_theta_approximation_excludes_rectangle_zeros.1
      m T c b 1 (fun _ => 0) y hT (by norm_num) hleft hright).2.1 i j
  exact MasulloRH.GramTail.weighted_gram_truncation_of_ray_envelopes
    (u i) (u j) c b R (Ap i) (Ap j) (Am i) (Am j) (Lp i) (Lp j) (Lm i) (Lm j)
    hR (hAp i) (hAp j) (hAm i) (hAm j) (hplus i j) (hminus i j)
    (hup i) (hup j) (hum i) (hum j) hI
