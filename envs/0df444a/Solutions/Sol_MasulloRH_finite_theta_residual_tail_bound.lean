-- Prove2me | solution 1 for MasulloRH.finite_theta_residual_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T18:22:01.090605+00:00
-- url     : https://prove2.me/submissions/4495dd03-70a6-4938-b219-048a13844832

import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Theorems.Thm_MasulloRH_theta_reflection
import Theorems.Thm_MasulloRH_theta_gaussian_truncation_error
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace N4FiniteResidualProof
/- Source: Solutions.ThetaReflectionBoundsCore -/
section
set_option autoImplicit false

namespace MasulloRH.ThetaReflectionCore

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

end MasulloRH.ThetaReflectionCore
end


/- Source: PublicThetaNormEnvelopes -/
section
open _root_.MasulloRH.GaussianApproximation _root_.N4FiniteResidualProof.MasulloRH.ThetaReflectionCore
lemma MasulloRH.theta_norm_reflection (x : ℝ) :
    ‖theta x‖ = (Real.exp (-x) / 2) * ‖theta (-x - Real.log 4)‖ := by
  rw [_root_.MasulloRH.theta_reflection x, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos (Real.exp_pos (-x)) (by norm_num : (0 : ℝ) < 2))]

/-- Explicit right-side Gaussian envelope, valid from the reflection midpoint onward. -/
theorem MasulloRH.theta_norm_le_right (x : ℝ) (hx : -Real.log 2 ≤ x) :
    ‖theta x‖ ≤ 24 * Real.exp (-Real.pi * (Real.exp x) ^ 2) := by
  have h₀ := _root_.MasulloRH.theta_gaussian_truncation_error x 0
  simp only [Finset.range_zero, Finset.sum_empty, mul_zero, sub_zero,
    Nat.cast_zero, zero_add, one_pow, mul_one] at h₀
  have hbound := zero_tail_bound_le (Real.pi * (Real.exp x) ^ 2) (alpha_ge_quarter_pi hx)
  have he₁ : -(Real.pi * (Real.exp x) ^ 2) = -Real.pi * (Real.exp x) ^ 2 := by ring
  have he₃ : -3 * (Real.pi * (Real.exp x) ^ 2) = -Real.pi * (Real.exp x) ^ 2 * 3 := by ring
  rw [he₁, he₃] at hbound
  exact h₀.trans hbound

/-- Explicit reflected Gaussian envelope on the entire left half-line. -/
theorem MasulloRH.theta_norm_le_left (x : ℝ) (hx : x ≤ -Real.log 2) :
    ‖theta x‖ ≤ 12 * Real.exp (-x) *
      Real.exp (-(Real.pi / 16) * (Real.exp (-x)) ^ 2) := by
  rw [MasulloRH.theta_norm_reflection x]
  calc
    _ ≤ (Real.exp (-x) / 2) *
        (24 * Real.exp (-Real.pi * (Real.exp (-x - Real.log 4)) ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (MasulloRH.theta_norm_le_right _ (reflected_ge_threshold hx)) (by positivity)
    _ = _ := by
      rw [reflected_exp_sq]
      have he : -Real.pi * ((Real.exp (-x)) ^ 2 / 16) =
          -(Real.pi / 16) * (Real.exp (-x)) ^ 2 := by ring
      rw [he]
      ring
end


/- Source: Solutions.ThetaDirectIntegrability (generic diagonal lemmas only) -/
section
/-!
Direct integrability for the actual mission functions. The weighted theta
domination and Gaussian pulse argument adapt the corresponding elementary
parts of the accepted `gram_identity_solution.lean`; all Mellin and RH
dependencies are replaced here by the proved explicit theta envelopes.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open MeasureTheory Set
open _root_.MasulloRH.GaussianApproximation

namespace MasulloRH.DirectIntegrability

theorem measurable_theta : Measurable theta := by
  unfold theta
  apply Measurable.tsum
  intro k
  fun_prop

theorem theta_decay_right (x : ℝ) : ‖theta x‖ ≤ 24 * Real.exp (-2 * x) := by
  by_cases hx : -Real.log 2 ≤ x
  · have ha : 2 * x ≤ Real.pi * (Real.exp x) ^ 2 := by
      have he := Real.add_one_le_exp (2 * x)
      have heq : Real.exp (2 * x) = (Real.exp x) ^ 2 := by
        simpa only [Nat.cast_ofNat] using Real.exp_nat_mul x 2
      rw [heq] at he
      have hp := mul_le_mul_of_nonneg_right
        (show (1 : ℝ) ≤ Real.pi by linarith [Real.pi_gt_three])
        (sq_nonneg (Real.exp x))
      nlinarith
    exact (MasulloRH.theta_norm_le_right x hx).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num))
  · have hx0 : x ≤ 0 := by
      have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith
    have he : Real.exp (-(Real.pi / 16) * (Real.exp (-x)) ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (by positivity)) (sq_nonneg _))
    calc
      _ ≤ 12 * Real.exp (-x) * Real.exp (-(Real.pi / 16) * (Real.exp (-x)) ^ 2) :=
        MasulloRH.theta_norm_le_left x (le_of_not_ge hx)
      _ ≤ 12 * Real.exp (-x) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left he
          (by positivity : 0 ≤ 12 * Real.exp (-x))
      _ ≤ 24 * Real.exp (-2 * x) := by
        have h := Real.exp_le_exp.mpr (show -x ≤ -2 * x by linarith)
        nlinarith [Real.exp_pos (-2 * x)]

theorem theta_decay_left (x : ℝ) : ‖theta x‖ ≤ 192 * Real.exp x := by
  rw [MasulloRH.theta_norm_reflection]
  calc
    _ ≤ (Real.exp (-x) / 2) * (24 * Real.exp (-2 * (-x - Real.log 4))) :=
      mul_le_mul_of_nonneg_left (theta_decay_right _) (by positivity)
    _ = 192 * Real.exp x := by
      have hfour : Real.exp (2 * Real.log 4) = 16 := by
        have h := Real.exp_nat_mul (Real.log 4) 2
        norm_num [Real.exp_log (by norm_num : (0 : ℝ) < 4)] at h
        exact h
      rw [show -2 * (-x - Real.log 4) = 2 * x + 2 * Real.log 4 by ring,
        Real.exp_add, hfour]
      have he : Real.exp (-x) * Real.exp (2 * x) = Real.exp x := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = 192 * (Real.exp (-x) * Real.exp (2 * x)) := by ring
        _ = _ := by rw [he]

private theorem integrable_exp_neg_two_abs :
    Integrable (fun x : ℝ => Real.exp (-2 * |x|)) := by
  have hp := integrableOn_exp_mul_Ioi (a := (-2 : ℝ)) (by norm_num) 0
  have hm := integrableOn_exp_mul_Iic (a := (2 : ℝ)) (by norm_num) 0
  have h := Integrable.piecewise (s := Ioi (0 : ℝ)) measurableSet_Ioi hp
    (by simpa only [compl_Ioi] using hm)
  apply h.congr
  filter_upwards [] with x
  by_cases hx : 0 < x
  · simp [Set.piecewise, hx, abs_of_pos hx]
  · have hx' : x ≤ 0 := le_of_not_gt hx
    simp [Set.piecewise, hx, abs_of_nonpos hx']

theorem theta_shift_weighted_integrable (c b y : ℝ)
    (hlo : 0 < c - b) (hhi : c + b < 1) :
    Integrable (fun x : ℝ => Real.exp (2 * c * x + 2 * b * |x|) * ‖theta (x-y)‖ ^ 2) := by
  let A : ℝ := 24
  let B : ℝ := 192
  let M := A ^ 2 * Real.exp (4 * y) + B ^ 2 * Real.exp (-2 * y)
  have hm : Measurable (fun x : ℝ =>
      Real.exp (2 * c * x + 2 * b * |x|) * ‖theta (x-y)‖ ^ 2) := by
    have ht : Measurable (fun x : ℝ => theta (x-y)) :=
      measurable_theta.comp (measurable_id.sub measurable_const)
    fun_prop
  apply (integrable_exp_neg_two_abs.const_mul M).mono' hm.aestronglyMeasurable
  refine ae_of_all _ fun x => ?_
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))]
  have hrewrite (u K v : ℝ) : Real.exp u * (K * Real.exp v) ^ 2 = K ^ 2 * Real.exp (u + 2*v) := by
    rw [Real.exp_add, two_mul v, Real.exp_add]
    ring
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    calc
      _ ≤ Real.exp (2*c*x+2*b*x) * (A * Real.exp (-2*(x-y))) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (theta_decay_right (x-y)) 2) (Real.exp_nonneg _)
      _ = A ^ 2 * Real.exp ((2*c*x+2*b*x) + 2*(-2*(x-y))) := hrewrite _ _ _
      _ ≤ A ^ 2 * Real.exp (4*y + (-2*x)) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (sq_nonneg _)
        nlinarith [mul_nonneg (sub_nonneg.mpr hhi.le) hx]
      _ ≤ M * Real.exp (-2*x) := by
        rw [Real.exp_add, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_right (by positivity)) (Real.exp_nonneg _)
  · rw [abs_of_neg (lt_of_not_ge hx)]
    calc
      _ ≤ Real.exp (2*c*x+2*b*(-x)) * (B * Real.exp (x-y)) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) (theta_decay_left (x-y)) 2) (Real.exp_nonneg _)
      _ = B ^ 2 * Real.exp ((2*c*x+2*b*(-x)) + 2*(x-y)) := hrewrite _ _ _
      _ ≤ B ^ 2 * Real.exp (-2*y + (-2*(-x))) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr _) (sq_nonneg _)
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hlo.le (le_of_not_ge hx)]
      _ ≤ M * Real.exp (-2*(-x)) := by
        rw [Real.exp_add, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left (by positivity)) (Real.exp_nonneg _)

private theorem real_gaussian_linear_integrable {k : ℝ} (hk : 0 < k) (v : ℝ) :
    Integrable (fun x : ℝ => Real.exp (-k*x^2+v*x)) := by
  have h := (integrable_cexp_quadratic (b := (k : ℂ)) (by exact hk) (v : ℂ) 0).norm
  convert! h using 1
  try rfl
  funext x
  rw [Complex.norm_exp, add_zero, ← Complex.ofReal_pow]
  simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_im,
    Complex.ofReal_re, Complex.neg_im, neg_zero, mul_zero, sub_zero]

theorem pulse_weighted_integrable {T : ℝ} (hT : 0 ≤ T) (c b : ℝ) :
    Integrable (fun x : ℝ => ‖pulse T x‖ ^ 2 * Real.exp (2*c*x+2*b*|x|)) := by
  let k := 2 * (T+1) ^ 2
  have hk : 0 < k := by dsimp [k]; positivity
  let u := ((T+1) / Real.sqrt Real.pi) ^ 2
  have hL := (real_gaussian_linear_integrable hk (2*c+2*b)).const_mul u
  have hR := (real_gaussian_linear_integrable hk (2*c-2*b)).const_mul u
  have h := Integrable.piecewise (s := Ici (0 : ℝ)) measurableSet_Ici hL.integrableOn hR.integrableOn
  convert! h using 1
  try rfl
  funext x
  have ha : 0 ≤ (T+1) / Real.sqrt Real.pi := by positivity
  rw [pulse, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha,
    ← Complex.ofReal_pow, Complex.neg_re, Complex.ofReal_re, mul_pow, ← Real.exp_nat_mul,
    mul_assoc, ← Real.exp_add]
  by_cases hx : 0 ≤ x
  · rw [piecewise_eq_of_mem _ _ _ (show x ∈ Ici 0 from hx), abs_of_nonneg hx]
    dsimp [k,u]
    congr 2
    ring
  · rw [piecewise_eq_of_notMem _ _ _ (show x ∉ Ici 0 from hx), abs_of_neg (lt_of_not_ge hx)]
    dsimp [k,u]
    congr 2
    ring

end MasulloRH.DirectIntegrability
end

/- Source: Solutions.ThetaGramTailCore -/
section
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
end

/- Source: Solutions.ThetaEnergyTailCore -/
section
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate

namespace MasulloRH.GramTail

/-- The real weighted-energy version of the Gram exterior-integration bound. -/
theorem weighted_energy_truncation_of_ray_envelopes
    (f : ℝ → ℂ) (c b R C D ell mu : ℝ)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hplus : 0 < 2*ell - 2*(c+b)) (hminus : 0 < 2*mu + 2*(c-b))
    (hfp : ∀ x : ℝ, R ≤ x → ‖f x‖ ≤ C * Real.exp (-ell * (x-R)))
    (hfm : ∀ x : ℝ, x ≤ -R → ‖f x‖ ≤ D * Real.exp (-mu * (-x-R)))
    (hI : Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|)*‖f x‖^2)) :
    (∫ x : ℝ, Real.exp (2*c*x+2*b*|x|)*‖f x‖^2) -
      (∫ x : ℝ in Icc (-R) R, Real.exp (2*c*x+2*b*|x|)*‖f x‖^2) ≤
      C^2 * Real.exp (2*(c+b)*R) / (2*ell-2*(c+b)) +
        D^2 * Real.exp (-2*(c-b)*R) / (2*mu+2*(c-b)) := by
  have hp (x : ℝ) :
      (Real.exp (2*c*x+2*b*|x|) : ℂ)*conj (f x)*f x =
        ((Real.exp (2*c*x+2*b*|x|)*‖f x‖^2 : ℝ) : ℂ) := by
    rw [mul_assoc, ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_mul,
      Complex.normSq_eq_norm_sq]
  have hIc : Integrable (fun x : ℝ =>
      (Real.exp (2*c*x+2*b*|x|) : ℂ)*conj (f x)*f x) := by
    convert! (hI.ofReal (𝕜 := ℂ)) using 1
    exact funext hp
  have h := weighted_gram_truncation_of_ray_envelopes f f c b R C C D D ell ell mu mu
    hR hC hC hD hD (by linarith) (by linarith) hfp hfp hfm hfm hIc
  simp_rw [hp, integral_complex_ofReal, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] at h
  have h' := (le_abs_self _).trans h
  simpa only [pow_two, two_mul] using h'

/-- A larger decay rate and smaller amplitude imply a common ray envelope. -/
theorem weaken_ray_envelope (A C L ell u : ℝ) (hAC : A ≤ C) (hC : 0 ≤ C)
    (hL : ell ≤ L) (hu : 0 ≤ u) :
    A * Real.exp (-L*u) ≤ C * Real.exp (-ell*u) := by
  exact mul_le_mul hAC (Real.exp_le_exp.mpr (by nlinarith))
    (Real.exp_nonneg _) hC

end MasulloRH.GramTail
end

/- Source: Solutions.ThetaFiniteResidualTails -/
section
/-!
Direct integrability and an explicit exterior bound for an arbitrary finite
residual formed from the mission's actual Gaussian pulse and theta translates.
The scalar envelope hypotheses below are finite inequalities; neither
integrability nor an approximation/density assertion is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open MeasureTheory Set
open scoped BigOperators
open _root_.MasulloRH.GaussianApproximation

namespace MasulloRH.FiniteResidualTails

private theorem weighted_square_add_integrable
    (w : ℝ → ℝ) (f g : ℝ → ℂ)
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (hf : Measurable f) (hg : Measurable g)
    (hIf : Integrable (fun x => w x * ‖f x‖ ^ 2))
    (hIg : Integrable (fun x => w x * ‖g x‖ ^ 2)) :
    Integrable (fun x => w x * ‖f x + g x‖ ^ 2) := by
  have hm : Measurable (fun x => w x * ‖f x + g x‖ ^ 2) := by fun_prop
  apply ((hIf.add hIg).const_mul 2).mono' hm.aestronglyMeasurable
  refine ae_of_all _ fun x => ?_
  rw [Real.norm_of_nonneg (mul_nonneg (hw0 x) (sq_nonneg _))]
  have hn := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (f x) (g x)) 2
  have hq : ‖f x + g x‖ ^ 2 ≤ 2 * ‖f x‖ ^ 2 + 2 * ‖g x‖ ^ 2 := by
    nlinarith [sq_nonneg (‖f x‖ - ‖g x‖)]
  calc
    _ ≤ w x * (2 * ‖f x‖ ^ 2 + 2 * ‖g x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hq (hw0 x)
    _ = _ := by simp only [Pi.add_apply]; ring

private theorem weighted_square_sum_integrable {ι : Type*}
    (s : Finset ι) (w : ℝ → ℝ) (f : ι → ℝ → ℂ)
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (hf : ∀ i, Measurable (f i))
    (hI : ∀ i, Integrable (fun x => w x * ‖f i x‖ ^ 2)) :
    Integrable (fun x => w x * ‖∑ i ∈ s, f i x‖ ^ 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hm : Measurable (fun x => ∑ j ∈ s, f j x) := by fun_prop
    simpa only [Finset.sum_insert hi] using
      weighted_square_add_integrable w (f i) (fun x => ∑ j ∈ s, f j x)
        hw hw0 (hf i) hm (hI i) ih

/-- Every finite actual theta residual has integrable weighted square in the
mission's open strip. This is proved by finite weighted-square closure. -/
theorem finite_residual_weighted_integrable
    (m : ℕ) (T c b : ℝ) (a : Fin m → ℂ) (y : Fin m → ℝ)
    (hT : 0 ≤ T) (hleft : 0 < c-b) (hright : c+b < 1) :
    Integrable (fun x : ℝ =>
      Real.exp (2*c*x+2*b*|x|) * ‖residual T a y x‖ ^ 2) := by
  let w := fun x : ℝ => Real.exp (2*c*x+2*b*|x|)
  let f := fun (i : Fin m) (x : ℝ) => a i * theta (x-y i)
  have hw : Measurable w := by dsimp [w]; fun_prop
  have hw0 (x : ℝ) : 0 ≤ w x := Real.exp_nonneg _
  have hf (i : Fin m) : Measurable (f i) := by
    have ht : Measurable (fun x : ℝ => theta (x-y i)) :=
      MasulloRH.DirectIntegrability.measurable_theta.comp
        (measurable_id.sub measurable_const)
    dsimp [f]
    fun_prop
  have hfi (i : Fin m) : Integrable (fun x => w x * ‖f i x‖ ^ 2) := by
    have h := (MasulloRH.DirectIntegrability.theta_shift_weighted_integrable
      c b (y i) hleft hright).const_mul (‖a i‖ ^ 2)
    convert h using 1
    funext x
    simp only [f, w, norm_mul, mul_pow]
    ring
  have hs := weighted_square_sum_integrable Finset.univ w f hw hw0 hf hfi
  have hsm : Measurable (fun x => ∑ i, f i x) := by fun_prop
  have hp : Measurable (pulse T) := by unfold pulse; fun_prop
  have hpi : Integrable (fun x => w x * ‖pulse T x‖ ^ 2) := by
    simpa only [w, mul_comm (Real.exp _)] using
      MasulloRH.DirectIntegrability.pulse_weighted_integrable hT c b
  have hni : Integrable (fun x => w x * ‖-(∑ i, f i x)‖ ^ 2) := by
    simpa only [norm_neg] using hs
  simpa only [w, f, _root_.MasulloRH.GaussianApproximation.residual, sub_eq_add_neg] using
    weighted_square_add_integrable w (pulse T) (fun x => -(∑ i, f i x))
      hw hw0 hp hsm.neg hpi hni

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
    (MasulloRH.GramTail.exp_gaussian_ray_le ((T+1)^2) R x (sq_nonneg _))
    (by positivity : 0 ≤ (T+1)/Real.sqrt Real.pi)

private theorem pulse_left_ray (T R x : ℝ) (hT : 0 ≤ T) :
    ‖pulse T x‖ ≤
      (((T+1)/Real.sqrt Real.pi) * Real.exp (-(T+1)^2*R^2)) *
        Real.exp (-(2*(T+1)^2*R)*(-x-R)) := by
  rw [pulse_norm T x hT]
  simpa only [neg_sq, mul_assoc] using mul_le_mul_of_nonneg_left
    (MasulloRH.GramTail.exp_gaussian_ray_le ((T+1)^2) R (-x) (sq_nonneg _))
    (by positivity : 0 ≤ (T+1)/Real.sqrt Real.pi)

private theorem residual_norm_le_sum
    (m : ℕ) (T : ℝ) (a : Fin m → ℂ) (y : Fin m → ℝ) (x : ℝ) :
    ‖residual T a y x‖ ≤
      ‖pulse T x‖ + ∑ i, ‖a i‖ * ‖theta (x-y i)‖ := by
  unfold _root_.MasulloRH.GaussianApproximation.residual
  apply (norm_sub_le _ _).trans
  apply add_le_add le_rfl
  simpa only [norm_mul] using
    (norm_sum_le Finset.univ (fun i : Fin m => a i * theta (x-y i)))

end MasulloRH.FiniteResidualTails

/-- Explicit exterior-integration error for any finite actual theta residual.
The integrability conjunct is derived, not a premise. The finite rate and shift
conditions are sufficient numerical conditions for the stated envelopes. -/
theorem MasulloRH.finite_theta_residual_truncation_error
    (m : ℕ) (T c b R ell mu : ℝ) (a : Fin m → ℂ) (y : Fin m → ℝ)
    (hT : 0 ≤ T) (hR : 0 ≤ R) (hleft : 0 < c-b) (hright : c+b < 1)
    (hshift : ∀ i : Fin m, |y i - Real.log 2| ≤ R)
    (hellp : ell ≤ 2*(T+1)^2*R) (hmup : mu ≤ 2*(T+1)^2*R)
    (helltheta : ∀ i : Fin m, ell ≤ 2*Real.pi*(Real.exp (R-y i))^2)
    (hmutheta : ∀ i : Fin m,
      mu ≤ 2*(Real.pi/16)*(Real.exp (R+y i))^2-1)
    (hplus : 0 < 2*ell-2*(c+b)) (hminus : 0 < 2*mu+2*(c-b)) :
    let A : ℝ := ((T+1)/Real.sqrt Real.pi) * Real.exp (-(T+1)^2*R^2)
    let C : ℝ := A + ∑ i, ‖a i‖ *
      (24 * Real.exp (-Real.pi*(Real.exp (R-y i))^2))
    let D : ℝ := A + ∑ i, ‖a i‖ *
      (12 * Real.exp (R+y i-(Real.pi/16)*(Real.exp (R+y i))^2))
    Integrable (fun x : ℝ =>
      Real.exp (2*c*x+2*b*|x|) * ‖residual T a y x‖ ^ 2) ∧
    0 ≤ energy c b (residual T a y) -
      (∫ x : ℝ in Icc (-R) R,
        Real.exp (2*c*x+2*b*|x|) * ‖residual T a y x‖ ^ 2) ∧
    energy c b (residual T a y) -
      (∫ x : ℝ in Icc (-R) R,
        Real.exp (2*c*x+2*b*|x|) * ‖residual T a y x‖ ^ 2) ≤
      C^2 * Real.exp (2*(c+b)*R) / (2*ell-2*(c+b)) +
      D^2 * Real.exp (-2*(c-b)*R) / (2*mu+2*(c-b)) := by
  intro A C D
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hI := MasulloRH.FiniteResidualTails.finite_residual_weighted_integrable
    m T c b a y hT hleft hright
  have hp (x : ℝ) (hx : R ≤ x) :
      ‖residual T a y x‖ ≤ C * Real.exp (-ell*(x-R)) := by
    have h0 : ‖pulse T x‖ ≤ A * Real.exp (-ell*(x-R)) :=
      (MasulloRH.FiniteResidualTails.pulse_right_ray T R x hT).trans
        (MasulloRH.GramTail.weaken_ray_envelope A A _ ell (x-R)
          le_rfl hA hellp (sub_nonneg.mpr hx))
    have ht (i : Fin m) : ‖theta (x-y i)‖ ≤
        (24 * Real.exp (-Real.pi*(Real.exp (R-y i))^2)) *
          Real.exp (-ell*(x-R)) := by
      have h := MasulloRH.GramTail.shifted_right_ray_of_theta_envelope theta
        MasulloRH.theta_norm_le_right (y i) R x (abs_le.mp (hshift i)).2 hx
      exact h.trans (MasulloRH.GramTail.weaken_ray_envelope _ _ _ ell (x-R)
        le_rfl (by positivity) (helltheta i) (sub_nonneg.mpr hx))
    calc
      _ ≤ ‖pulse T x‖ + ∑ i, ‖a i‖ * ‖theta (x-y i)‖ :=
        MasulloRH.FiniteResidualTails.residual_norm_le_sum m T a y x
      _ ≤ A * Real.exp (-ell*(x-R)) +
          ∑ i, ‖a i‖ * ((24 * Real.exp (-Real.pi*(Real.exp (R-y i))^2)) *
            Real.exp (-ell*(x-R))) :=
        add_le_add h0 (Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (ht i) (norm_nonneg _))
      _ = C * Real.exp (-ell*(x-R)) := by
        simp only [C, add_mul, Finset.sum_mul, mul_assoc]
  have hm (x : ℝ) (hx : x ≤ -R) :
      ‖residual T a y x‖ ≤ D * Real.exp (-mu*(-x-R)) := by
    have hu : 0 ≤ -x-R := by linarith
    have h0 : ‖pulse T x‖ ≤ A * Real.exp (-mu*(-x-R)) :=
      (MasulloRH.FiniteResidualTails.pulse_left_ray T R x hT).trans
        (MasulloRH.GramTail.weaken_ray_envelope A A _ mu (-x-R)
          le_rfl hA hmup hu)
    have ht (i : Fin m) : ‖theta (x-y i)‖ ≤
        (12 * Real.exp (R+y i-(Real.pi/16)*(Real.exp (R+y i))^2)) *
          Real.exp (-mu*(-x-R)) := by
      have hs : Real.log 2 - y i ≤ R := by
        have h := (abs_le.mp (hshift i)).1
        linarith
      have h := MasulloRH.GramTail.shifted_left_ray_of_theta_envelope theta
        MasulloRH.theta_norm_le_left (y i) R x hs hx
      exact h.trans (MasulloRH.GramTail.weaken_ray_envelope _ _ _ mu (-x-R)
        le_rfl (by positivity) (hmutheta i) hu)
    calc
      _ ≤ ‖pulse T x‖ + ∑ i, ‖a i‖ * ‖theta (x-y i)‖ :=
        MasulloRH.FiniteResidualTails.residual_norm_le_sum m T a y x
      _ ≤ A * Real.exp (-mu*(-x-R)) +
          ∑ i, ‖a i‖ * ((12 * Real.exp
            (R+y i-(Real.pi/16)*(Real.exp (R+y i))^2)) *
              Real.exp (-mu*(-x-R))) :=
        add_le_add h0 (Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (ht i) (norm_nonneg _))
      _ = D * Real.exp (-mu*(-x-R)) := by
        simp only [D, add_mul, Finset.sum_mul, mul_assoc]
  refine ⟨hI, ?_, ?_⟩
  · exact sub_nonneg.mpr (setIntegral_le_integral hI
      (ae_of_all _ fun x => mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)))
  · exact MasulloRH.GramTail.weighted_energy_truncation_of_ray_envelopes
      (residual T a y) c b R C D ell mu hR hC hD hplus hminus hp hm hI

/-- A uniform-rate version: beyond a window of radius at least `1/2` containing
all reflection midpoints, the finite rate hypotheses follow automatically. -/
theorem MasulloRH.finite_theta_residual_tail_bound
    (m : ℕ) (T c b R : ℝ) (a : Fin m → ℂ) (y : Fin m → ℝ)
    (hT : 0 ≤ T) (hR : (1/2 : ℝ) ≤ R)
    (hleft : 0 < c-b) (hright : c+b < 1)
    (hshift : ∀ i : Fin m, |y i - Real.log 2| ≤ R) :
    let A : ℝ := ((T+1)/Real.sqrt Real.pi) * Real.exp (-(T+1)^2*R^2)
    let C : ℝ := A + ∑ i, ‖a i‖ *
      (24 * Real.exp (-Real.pi*(Real.exp (R-y i))^2))
    let D : ℝ := A + ∑ i, ‖a i‖ *
      (12 * Real.exp (R+y i-(Real.pi/16)*(Real.exp (R+y i))^2))
    Integrable (fun x : ℝ =>
      Real.exp (2*c*x+2*b*|x|) * ‖residual T a y x‖ ^ 2) ∧
    0 ≤ energy c b (residual T a y) -
      (∫ x : ℝ in Icc (-R) R,
        Real.exp (2*c*x+2*b*|x|) * ‖residual T a y x‖ ^ 2) ∧
    energy c b (residual T a y) -
      (∫ x : ℝ in Icc (-R) R,
        Real.exp (2*c*x+2*b*|x|) * ‖residual T a y x‖ ^ 2) ≤
      C^2 * Real.exp (2*(c+b)*R) / (2-2*(c+b)) +
      D^2 * Real.exp (-2*(c-b)*R) / (2*(c-b)) := by
  have hR0 : 0 ≤ R := by linarith
  have hp : 1 ≤ 2*(T+1)^2*R := by
    have ht : (1 : ℝ) ≤ (T+1)^2 := by nlinarith
    have h := mul_le_mul_of_nonneg_right ht hR0
    nlinarith
  have htheta_plus (i : Fin m) :
      1 ≤ 2*Real.pi*(Real.exp (R-y i))^2 := by
    have hi := (abs_le.mp (hshift i)).2
    have h := MasulloRH.ThetaReflectionCore.alpha_ge_quarter_pi
      (show -Real.log 2 ≤ R-y i by linarith)
    nlinarith [Real.pi_gt_three]
  have htheta_minus (i : Fin m) :
      0 ≤ 2*(Real.pi/16)*(Real.exp (R+y i))^2-1 := by
    have hi := (abs_le.mp (hshift i)).1
    have hx : Real.log 2 ≤ R+y i := by linarith
    have he : 2 ≤ Real.exp (R+y i) := by
      have h := Real.exp_le_exp.mpr hx
      simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using h
    have hs : (4 : ℝ) ≤ (Real.exp (R+y i))^2 := by nlinarith
    have h := mul_le_mul_of_nonneg_left hs Real.pi_pos.le
    nlinarith [Real.pi_gt_three]
  have h := MasulloRH.finite_theta_residual_truncation_error
    m T c b R 1 0 a y hT hR0 hleft hright hshift hp
    (by linarith) htheta_plus htheta_minus (by linarith) (by linarith)
  simpa only [mul_one, mul_zero, zero_add] using h
end

end N4FiniteResidualProof

open MeasureTheory Set
open scoped BigOperators
open _root_.MasulloRH.GaussianApproximation

theorem solution
    (m : ℕ) (T c b R : ℝ) (a : Fin m → ℂ) (y : Fin m → ℝ)
    (hT : 0 ≤ T) (hR : (1/2 : ℝ) ≤ R)
    (hleft : 0 < c-b) (hright : c+b < 1)
    (hshift : ∀ i : Fin m, |y i - Real.log 2| ≤ R) :
    let A : ℝ := ((T+1)/Real.sqrt Real.pi) * Real.exp (-(T+1)^2*R^2)
    let C : ℝ := A + ∑ i, ‖a i‖ *
      (24 * Real.exp (-Real.pi*(Real.exp (R-y i))^2))
    let D : ℝ := A + ∑ i, ‖a i‖ *
      (12 * Real.exp (R+y i-(Real.pi/16)*(Real.exp (R+y i))^2))
    Integrable (fun x : ℝ =>
      Real.exp (2*c*x+2*b*|x|) * ‖residual T a y x‖ ^ 2) ∧
    0 ≤ energy c b (residual T a y) -
      (∫ x : ℝ in Icc (-R) R,
        Real.exp (2*c*x+2*b*|x|) * ‖residual T a y x‖ ^ 2) ∧
    energy c b (residual T a y) -
      (∫ x : ℝ in Icc (-R) R,
        Real.exp (2*c*x+2*b*|x|) * ‖residual T a y x‖ ^ 2) ≤
      C^2 * Real.exp (2*(c+b)*R) / (2-2*(c+b)) +
      D^2 * Real.exp (-2*(c-b)*R) / (2*(c-b)) := by
  exact N4FiniteResidualProof.MasulloRH.finite_theta_residual_tail_bound m T c b R a y hT hR hleft hright hshift

#print axioms solution
