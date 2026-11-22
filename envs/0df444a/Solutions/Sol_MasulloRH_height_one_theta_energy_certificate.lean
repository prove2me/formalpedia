-- Prove2me | solution 1 for MasulloRH.height_one_theta_energy_certificate
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T17:19:13.905051+00:00
-- url     : https://prove2.me/submissions/71d14ee5-fd68-403c-8f62-70f88131812b

import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Theorems.Thm_MasulloRH_theta_reflection
import Theorems.Thm_MasulloRH_theta_gaussian_truncation_error
import Theorems.Thm_MasulloRH_height_one_left_compact_energy_certificate
import Theorems.Thm_MasulloRH_height_one_right_compact_energy_certificate

/-!
Final height-one assembly. The two public compact certificates supply the left
and right integral bounds. Direct integrability and the exterior allowance are
proved below from the actual theta definition and accepted reflection/series-tail
theorems. Copied analytic helpers are isolated under N1FinalProof so full local
proof mirrors of the public compact theorems can coexist without collisions.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
open MeasureTheory Set
open scoped BigOperators ComplexConjugate
open MasulloRH.GaussianApproximation

/- Source: ThetaReflectionBoundsCore.lean. -/
set_option autoImplicit false

namespace N1FinalProof.ReflectionBounds

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

end N1FinalProof.ReflectionBounds


/- Source: ThetaReflection.lean (norm envelopes only). -/
open MasulloRH.GaussianApproximation N1FinalProof.ReflectionBounds
lemma N1FinalProof.theta_norm_reflection (x : ℝ) :
    ‖theta x‖ = (Real.exp (-x) / 2) * ‖theta (-x - Real.log 4)‖ := by
  rw [MasulloRH.theta_reflection x, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos (Real.exp_pos (-x)) (by norm_num : (0 : ℝ) < 2))]

/-- Explicit right-side Gaussian envelope, valid from the reflection midpoint onward. -/
theorem N1FinalProof.theta_norm_le_right (x : ℝ) (hx : -Real.log 2 ≤ x) :
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
theorem N1FinalProof.theta_norm_le_left (x : ℝ) (hx : x ≤ -Real.log 2) :
    ‖theta x‖ ≤ 12 * Real.exp (-x) *
      Real.exp (-(Real.pi / 16) * (Real.exp (-x)) ^ 2) := by
  rw [N1FinalProof.theta_norm_reflection x]
  calc
    _ ≤ (Real.exp (-x) / 2) *
        (24 * Real.exp (-Real.pi * (Real.exp (-x - Real.log 4)) ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (N1FinalProof.theta_norm_le_right _ (reflected_ge_threshold hx)) (by positivity)
    _ = _ := by
      rw [reflected_exp_sq]
      have he : -Real.pi * ((Real.exp (-x)) ^ 2 / 16) =
          -(Real.pi / 16) * (Real.exp (-x)) ^ 2 := by ring
      rw [he]
      ring


/- Source: ThetaDirectIntegrability.lean. -/
/-!
Direct integrability for the actual mission functions. The weighted theta
domination and Gaussian pulse argument adapt the corresponding elementary
parts of the accepted `gram_identity_solution.lean`; all Mellin and RH
dependencies are replaced here by the proved explicit theta envelopes.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open MeasureTheory Set
open MasulloRH.GaussianApproximation

namespace N1FinalProof.DirectIntegrability

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
    exact (N1FinalProof.theta_norm_le_right x hx).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num))
  · have hx0 : x ≤ 0 := by
      have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith
    have he : Real.exp (-(Real.pi / 16) * (Real.exp (-x)) ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (by positivity)) (sq_nonneg _))
    calc
      _ ≤ 12 * Real.exp (-x) * Real.exp (-(Real.pi / 16) * (Real.exp (-x)) ^ 2) :=
        N1FinalProof.theta_norm_le_left x (le_of_not_ge hx)
      _ ≤ 12 * Real.exp (-x) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left he
          (by positivity : 0 ≤ 12 * Real.exp (-x))
      _ ≤ 24 * Real.exp (-2 * x) := by
        have h := Real.exp_le_exp.mpr (show -x ≤ -2 * x by linarith)
        nlinarith [Real.exp_pos (-2 * x)]

theorem theta_decay_left (x : ℝ) : ‖theta x‖ ≤ 192 * Real.exp x := by
  rw [N1FinalProof.theta_norm_reflection]
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

theorem one_translate_weighted_integrable (T c b y : ℝ) (a : ℂ)
    (hT : 0 ≤ T) (hlo : 0 < c-b) (hhi : c+b < 1) :
    Integrable (fun x : ℝ =>
      Real.exp (2*c*x+2*b*|x|) * ‖pulse T x - a * theta (x-y)‖ ^ 2) := by
  have hp : Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|) * ‖pulse T x‖ ^ 2) := by
    simpa only [mul_comm (Real.exp _)] using pulse_weighted_integrable hT c b
  have hq := theta_shift_weighted_integrable c b y hlo hhi
  have hm : Measurable (fun x : ℝ =>
      Real.exp (2*c*x+2*b*|x|) * ‖pulse T x - a * theta (x-y)‖ ^ 2) := by
    have ht : Measurable (fun x : ℝ => theta (x-y)) :=
      measurable_theta.comp (measurable_id.sub measurable_const)
    have hpulse : Measurable (pulse T) := by unfold pulse; fun_prop
    fun_prop
  apply ((hp.const_mul 2).add (hq.const_mul (2 * ‖a‖ ^ 2))).mono' hm.aestronglyMeasurable
  refine ae_of_all _ fun x => ?_
  rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))]
  have hn := norm_sub_le (pulse T x) (a * theta (x-y))
  rw [norm_mul] at hn
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hquad : ‖pulse T x - a * theta (x-y)‖ ^ 2 ≤
      2 * ‖pulse T x‖ ^ 2 + 2 * ‖a‖ ^ 2 * ‖theta (x-y)‖ ^ 2 := by
    nlinarith [sq_nonneg (‖pulse T x‖ - ‖a‖ * ‖theta (x-y)‖)]
  have h := mul_le_mul_of_nonneg_left hquad (Real.exp_nonneg (2*c*x+2*b*|x|))
  change Real.exp (2*c*x+2*b*|x|) * ‖pulse T x - a * theta (x-y)‖ ^ 2 ≤
    2 * (Real.exp (2*c*x+2*b*|x|) * ‖pulse T x‖ ^ 2) +
      2 * ‖a‖ ^ 2 * (Real.exp (2*c*x+2*b*|x|) * ‖theta (x-y)‖ ^ 2)
  exact h.trans_eq (by ring)

theorem height_one_density_integrable :
    Integrable (fun x : ℝ => Real.exp ((3/2)*x+(7/16)*|x|) *
      ‖pulse 1 x - (73/50 : ℂ) * theta (x-3/4)‖ ^ 2) := by
  have h := one_translate_weighted_integrable 1 (3/4) (7/32) (3/4) (73/50)
    (by norm_num) (by norm_num) (by norm_num)
  simpa only [show (2 : ℝ)*(3/4)=3/2 by norm_num,
    show (2 : ℝ)*(7/32)=7/16 by norm_num] using h


end N1FinalProof.DirectIntegrability


/- Source: ThetaGramTailCore.lean. -/
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate

namespace N1FinalProof.GramTail

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

end N1FinalProof.GramTail


/- Source: ThetaEnergyTailCore.lean. -/
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate

namespace N1FinalProof.GramTail

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

end N1FinalProof.GramTail


/- Source: ThetaEnergyHeightOneCore.lean. -/
set_option autoImplicit false
open MeasureTheory Set

namespace N1FinalProof.EnergyCertificate

/-- Common coarse column rays suffice for the height-one residual energy.
The amplitudes and rates here are fully rational constants. -/
theorem height_one_residual_tail_of_column_rays (p q : ℝ → ℂ)
    (hpplus : ∀ x : ℝ, 4 ≤ x →
      ‖p x‖ ≤ (1/16777216 : ℝ)*Real.exp (-32*(x-4)))
    (hqplus : ∀ x : ℝ, 4 ≤ x →
      ‖q x‖ ≤ (1/16777216 : ℝ)*Real.exp (-32*(x-4)))
    (hpminus : ∀ x : ℝ, x ≤ -4 →
      ‖p x‖ ≤ (1/16777216 : ℝ)*Real.exp (-32*(-x-4)))
    (hqminus : ∀ x : ℝ, x ≤ -4 →
      ‖q x‖ ≤ (1/16777216 : ℝ)*Real.exp (-32*(-x-4)))
    (hI : Integrable (fun x : ℝ =>
      Real.exp ((3/2)*x+(7/16)*|x|)*‖p x-(73/50 : ℂ)*q x‖^2)) :
    (∫ x : ℝ, Real.exp ((3/2)*x+(7/16)*|x|)*‖p x-(73/50 : ℂ)*q x‖^2) -
      (∫ x : ℝ in Icc (-4) 4,
        Real.exp ((3/2)*x+(7/16)*|x|)*‖p x-(73/50 : ℂ)*q x‖^2) ≤
          (1/1000000000 : ℝ) := by
  let C : ℝ := (123/50)*(1/16777216)
  let r : ℝ → ℂ := fun x => p x-(73/50 : ℂ)*q x
  have hray (x v : ℝ) (hp : ‖p x‖ ≤ (1/16777216 : ℝ)*v)
      (hq : ‖q x‖ ≤ (1/16777216 : ℝ)*v) : ‖r x‖ ≤ C*v := by
    have h := norm_sub_le (p x) ((73/50 : ℂ)*q x)
    rw [norm_mul, show ‖(73/50 : ℂ)‖ = (73/50 : ℝ) by norm_num [norm_div]] at h
    apply h.trans
    calc
      _ ≤ (1/16777216 : ℝ)*v + (73/50 : ℝ)*((1/16777216 : ℝ)*v) :=
        add_le_add hp (mul_le_mul_of_nonneg_left hq (by norm_num))
      _ = C*v := by dsimp [C]; ring
  have h := N1FinalProof.GramTail.weighted_energy_truncation_of_ray_envelopes
    r (3/4) (7/32) 4 C C 32 32 (by norm_num) (by dsimp [C]; positivity)
    (by dsimp [C]; positivity) (by norm_num) (by norm_num)
    (fun x hx => hray x _ (hpplus x hx) (hqplus x hx))
    (fun x hx => hray x _ (hpminus x hx) (hqminus x hx))
    (by simpa only [r, show (2:ℝ)*(3/4)=3/2 by norm_num,
      show (2:ℝ)*(7/32)=7/16 by norm_num] using hI)
  have hwp : Real.exp (31/4 : ℝ) ≤ 6561 := by
    have hp := pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le 8
    norm_num [Real.exp_one_pow] at hp
    exact (Real.exp_le_exp.mpr (by norm_num : (31/4 : ℝ) ≤ 8)).trans hp
  have hwm : Real.exp (-17/4 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  norm_num [C, r] at h
  nlinarith

end N1FinalProof.EnergyCertificate


/- Source: ThetaGramTailHeightOneCore.lean (column bounds only). -/
set_option autoImplicit false

namespace N1FinalProof.GramTail

private theorem two_pow_le_exp_nat (n : ℕ) : (2 : ℝ)^n ≤ Real.exp n := by
  rw [← Real.exp_one_pow]
  exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_two.le n

private theorem exp_neg_nat_le (n : ℕ) : Real.exp (-(n : ℝ)) ≤ 1/(2 : ℝ)^n := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) (two_pow_le_exp_nat n)

/-- Coarse rational checks for all exterior error terms in the height-one,
one-translate certificate, with R=4 and shift y=3/4. No numerical oracle is used. -/
theorem height_one_column_numeric_bounds :
    let Ap : Fin 2 → ℝ := ![2/Real.sqrt Real.pi * Real.exp (-64),
      24 * Real.exp (-Real.pi * (Real.exp (13/4))^2)]
    let Lp : Fin 2 → ℝ := ![32, 2 * Real.pi * (Real.exp (13/4))^2]
    let Am : Fin 2 → ℝ := ![2/Real.sqrt Real.pi * Real.exp (-64),
      12 * Real.exp (19/4 - (Real.pi/16) * (Real.exp (19/4))^2)]
    let Lm : Fin 2 → ℝ := ![32, 2 * (Real.pi/16) * (Real.exp (19/4))^2 - 1]
    ∀ k : Fin 2, 0 ≤ Ap k ∧ Ap k ≤ (1/16777216 : ℝ) ∧
      0 ≤ Am k ∧ Am k ≤ (1/16777216 : ℝ) ∧ 32 ≤ Lp k ∧ 32 ≤ Lm k := by
  intro Ap Lp Am Lm
  let α : ℝ := Real.pi * (Real.exp (13/4))^2
  let β : ℝ := (Real.pi/16) * (Real.exp (19/4))^2
  have hα : 50 ≤ α := by
    have hx : (17/4 : ℝ) ≤ Real.exp (13/4) := by
      linarith [Real.add_one_le_exp (13/4 : ℝ)]
    have hs : (17/4 : ℝ)^2 ≤ (Real.exp (13/4))^2 :=
      pow_le_pow_left₀ (by norm_num) hx 2
    have hp := mul_le_mul Real.pi_gt_three.le hs (by norm_num : (0:ℝ) ≤ (17/4)^2)
      Real.pi_pos.le
    dsimp [α]
    linarith
  have hβ : 48 ≤ β := by
    have hx : (16 : ℝ) ≤ Real.exp (19/4) := by
      have ht := two_pow_le_exp_nat 4
      norm_num only [Nat.cast_ofNat, pow_succ, pow_zero] at ht
      exact ht.trans (Real.exp_le_exp.mpr (by norm_num))
    have hs : (16 : ℝ)^2 ≤ (Real.exp (19/4))^2 :=
      pow_le_pow_left₀ (by norm_num) hx 2
    have hp := mul_le_mul (div_le_div_of_nonneg_right Real.pi_gt_three.le
      (by norm_num : (0:ℝ) ≤ 16)) hs (by norm_num : (0:ℝ) ≤ 16^2) (by positivity)
    dsimp [β]
    linarith
  have hP : 0 ≤ 2/Real.sqrt Real.pi * Real.exp (-64) ∧
      2/Real.sqrt Real.pi * Real.exp (-64) ≤ (1/16777216 : ℝ) := by
    refine ⟨by positivity, ?_⟩
    have hc : 2/Real.sqrt Real.pi ≤ (2 : ℝ) := div_le_self (by norm_num)
      (Real.one_le_sqrt.mpr (by linarith [Real.pi_gt_three]))
    have he := exp_neg_nat_le 64
    norm_num only [Nat.cast_ofNat] at he
    exact (mul_le_mul hc he (Real.exp_nonneg _) (by norm_num)).trans (by norm_num)
  have hA : 0 ≤ 24 * Real.exp (-α) ∧
      24 * Real.exp (-α) ≤ (1/16777216 : ℝ) := by
    refine ⟨by positivity, ?_⟩
    have he := (Real.exp_le_exp.mpr (neg_le_neg hα)).trans (exp_neg_nat_le 50)
    exact (mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ) ≤ 24)).trans (by norm_num)
  have hB : 0 ≤ 12 * Real.exp (19/4-β) ∧
      12 * Real.exp (19/4-β) ≤ (1/16777216 : ℝ) := by
    refine ⟨by positivity, ?_⟩
    have he := (Real.exp_le_exp.mpr (show (19/4:ℝ)-β ≤ -40 by linarith)).trans
      (exp_neg_nat_le 40)
    exact (mul_le_mul_of_nonneg_left he (by norm_num : (0:ℝ) ≤ 12)).trans (by norm_num)
  have hAp (k : Fin 2) : 0 ≤ Ap k ∧ Ap k ≤ (1/16777216 : ℝ) := by
    fin_cases k
    · simpa [Ap] using hP
    · simpa [Ap, neg_mul, α] using hA
  have hAm (k : Fin 2) : 0 ≤ Am k ∧ Am k ≤ (1/16777216 : ℝ) := by
    fin_cases k
    · simpa [Am] using hP
    · simpa [Am, β] using hB
  have hLp (k : Fin 2) : 32 ≤ Lp k := by
    fin_cases k
    · norm_num [Lp]
    · change 32 ≤ 2*Real.pi*(Real.exp (13/4))^2
      dsimp [α] at hα
      linarith
  have hLm (k : Fin 2) : 32 ≤ Lm k := by
    fin_cases k
    · norm_num [Lm]
    · change 32 ≤ 2*(Real.pi/16)*(Real.exp (19/4))^2-1
      dsimp [β] at hβ
      linarith
  intro k
  exact ⟨(hAp k).1, (hAp k).2, (hAm k).1, (hAm k).2, hLp k, hLm k⟩


end N1FinalProof.GramTail


/- Source: ThetaN1CellCore.lean (density and real pulse only). -/
namespace N1FinalProof.HeightOne

noncomputable def realPulse (x : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) * Real.exp (-4 * x ^ 2)

noncomputable def density (x : ℝ) : ℝ :=
  Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) *
    ‖pulse 1 x - (73 / 50 : ℂ) * theta (x - 3 / 4)‖ ^ 2

theorem pulse_eq_realPulse (x : ℝ) : pulse 1 x = (realPulse x : ℂ) := by
  unfold pulse realPulse
  norm_num only [one_add_one_eq_two]
  rw [show -((2 * x : ℝ) : ℂ) ^ 2 = ((-4 * x ^ 2 : ℝ) : ℂ) by
    push_cast
    ring]
  rw [← Complex.ofReal_exp, ← Complex.ofReal_mul]


end N1FinalProof.HeightOne


/- Source: ThetaEnergyHeightOne.lean (integrability and exterior only). -/
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators
open MasulloRH.GaussianApproximation

namespace N1FinalProof.HeightOne

theorem density_integrable : Integrable density := by
  exact N1FinalProof.DirectIntegrability.height_one_density_integrable

private theorem column_rays :
    (∀ x : ℝ, 4 ≤ x → ‖pulse 1 x‖ ≤
      (1/16777216 : ℝ)*Real.exp (-32*(x-4))) ∧
    (∀ x : ℝ, 4 ≤ x → ‖theta (x-3/4)‖ ≤
      (1/16777216 : ℝ)*Real.exp (-32*(x-4))) ∧
    (∀ x : ℝ, x ≤ -4 → ‖pulse 1 x‖ ≤
      (1/16777216 : ℝ)*Real.exp (-32*(-x-4))) ∧
    (∀ x : ℝ, x ≤ -4 → ‖theta (x-3/4)‖ ≤
      (1/16777216 : ℝ)*Real.exp (-32*(-x-4))) := by
  have hn := N1FinalProof.GramTail.height_one_column_numeric_bounds
  have hP : 2/Real.sqrt Real.pi*Real.exp (-64) ≤ (1/16777216 : ℝ) := (hn 0).2.1
  have hA : 24*Real.exp (-Real.pi*(Real.exp (13/4))^2) ≤ (1/16777216 : ℝ) :=
    (hn 1).2.1
  have hB : 12*Real.exp (19/4-(Real.pi/16)*(Real.exp (19/4))^2) ≤
      (1/16777216 : ℝ) := (hn 1).2.2.2.1
  have hLp : 32 ≤ 2*Real.pi*(Real.exp (13/4))^2 := (hn 1).2.2.2.2.1
  have hLm : 32 ≤ 2*(Real.pi/16)*(Real.exp (19/4))^2-1 := (hn 1).2.2.2.2.2
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at h
    exact h
  have hpulse (x : ℝ) : ‖pulse 1 x‖ = (2/Real.sqrt Real.pi)*Real.exp (-4*x^2) := by
    rw [pulse_eq_realPulse, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by unfold realPulse; positivity)]
    rfl
  have hp (x : ℝ) : ‖pulse 1 x‖ ≤
      (2/Real.sqrt Real.pi*Real.exp (-64))*Real.exp (-32*(x-4)) := by
    rw [hpulse]
    have h := mul_le_mul_of_nonneg_left
      (N1FinalProof.GramTail.exp_gaussian_ray_le 4 4 x (by norm_num))
      (by positivity : 0 ≤ 2/Real.sqrt Real.pi)
    norm_num only [show (-(4:ℝ)*4^2) = -64 by norm_num,
      show (2:ℝ)*4*4 = 32 by norm_num] at h
    simpa only [mul_assoc] using h
  have hm (x : ℝ) : ‖pulse 1 x‖ ≤
      (2/Real.sqrt Real.pi*Real.exp (-64))*Real.exp (-32*(-x-4)) := by
    have h := hp (-x)
    simpa only [hpulse, neg_sq] using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x _hx
    exact (hp x).trans (mul_le_mul_of_nonneg_right hP (Real.exp_nonneg _))
  · intro x hx
    have h := N1FinalProof.GramTail.shifted_right_ray_of_theta_envelope theta
      N1FinalProof.theta_norm_le_right (3/4) 4 x (by linarith) hx
    norm_num at h
    have hw := N1FinalProof.GramTail.weaken_ray_envelope _ _ _ 32 (x-4) hA
      (by norm_num) hLp (by linarith)
    norm_num at hw
    simpa only [neg_mul] using h.trans hw
  · intro x _hx
    exact (hm x).trans (mul_le_mul_of_nonneg_right hP (Real.exp_nonneg _))
  · intro x hx
    have h := N1FinalProof.GramTail.shifted_left_ray_of_theta_envelope theta
      N1FinalProof.theta_norm_le_left (3/4) 4 x (by linarith) hx
    norm_num at h
    have hw := N1FinalProof.GramTail.weaken_ray_envelope _ _ _ 32 (-x-4) hB
      (by norm_num) hLm (by linarith)
    norm_num at hw
    simpa only [neg_mul] using h.trans hw

/-- A completely checked rational upper bound for the discarded energy outside
[-4,4] of the actual one-translate height-one residual. -/
theorem density_outer_error :
    (∫ x : ℝ, density x) - (∫ x : ℝ in Icc (-4) 4, density x) ≤
      (1/1000000000 : ℝ) := by
  obtain ⟨hp, hq, hp', hq'⟩ := column_rays
  exact N1FinalProof.EnergyCertificate.height_one_residual_tail_of_column_rays
    (pulse 1) (fun x => theta (x-3/4)) hp hq hp' hq' density_integrable


end N1FinalProof.HeightOne


open MeasureTheory MasulloRH.GaussianApproximation

theorem solution :
    Integrable (fun x : ℝ =>
      Real.exp (2*(3/4)*x + 2*(7/32)*|x|) *
        ‖residual 1 (fun _ : Fin 1 => (73/50 : ℂ))
          (fun _ : Fin 1 => (3/4 : ℝ)) x‖^2) ∧
    energy (3/4) (7/32)
      (residual 1 (fun _ : Fin 1 => (73/50 : ℂ))
        (fun _ : Fin 1 => (3/4 : ℝ))) < (1/64 : ℝ) := by
  have hI := N1FinalProof.HeightOne.density_integrable
  have hleft :
      (∫ x : ℝ in Icc (-4) 0, N1FinalProof.HeightOne.density x) ≤ (1/250 : ℝ) := by
    simpa only [N1FinalProof.HeightOne.density,
      MasulloRH.GaussianApproximation.residual, Fin.sum_univ_one,
      show (2 : ℝ)*(3/4)=3/2 by norm_num,
      show (2 : ℝ)*(7/32)=7/16 by norm_num] using
      MasulloRH.height_one_left_compact_energy_certificate.2
  have hright :
      (∫ x : ℝ in Icc 0 4, N1FinalProof.HeightOne.density x) ≤ (1/200 : ℝ) := by
    simpa only [N1FinalProof.HeightOne.density,
      MasulloRH.GaussianApproximation.residual, Fin.sum_univ_one,
      show (2 : ℝ)*(3/4)=3/2 by norm_num,
      show (2 : ℝ)*(7/32)=7/16 by norm_num] using
      MasulloRH.height_one_right_compact_energy_certificate.2
  have hsplit :
      (∫ x : ℝ in Icc (-4) 0, N1FinalProof.HeightOne.density x) +
        (∫ x : ℝ in Icc 0 4, N1FinalProof.HeightOne.density x) =
      (∫ x : ℝ in Icc (-4) 4, N1FinalProof.HeightOne.density x) := by
    have h := intervalIntegral.integral_add_adjacent_intervals
      (a := (-4 : ℝ)) (b := (0 : ℝ)) (c := (4 : ℝ))
      hI.intervalIntegrable hI.intervalIntegrable
    rw [intervalIntegral.integral_of_le (by norm_num : (-4 : ℝ) ≤ 0),
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 4),
      intervalIntegral.integral_of_le (by norm_num : (-4 : ℝ) ≤ 4)] at h
    simpa only [← integral_Icc_eq_integral_Ioc] using h
  have houter := N1FinalProof.HeightOne.density_outer_error
  have henergy : (∫ x : ℝ, N1FinalProof.HeightOne.density x) < (1/64 : ℝ) := by
    linarith
  constructor
  · convert! hI using 1
    funext x
    simp only [N1FinalProof.HeightOne.density,
      MasulloRH.GaussianApproximation.residual, Fin.sum_univ_one,
      show (2 : ℝ)*(3/4)=3/2 by norm_num,
      show (2 : ℝ)*(7/32)=7/16 by norm_num]
  · simpa only [energy, N1FinalProof.HeightOne.density,
      MasulloRH.GaussianApproximation.residual, Fin.sum_univ_one,
      show (2 : ℝ)*(3/4)=3/2 by norm_num,
      show (2 : ℝ)*(7/32)=7/16 by norm_num] using henergy

#print axioms solution
