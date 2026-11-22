-- Prove2me | solution 1 for MasulloRH.height_one_left_inner_compact_energy_certificate
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T17:45:37.065404+00:00
-- url     : https://prove2.me/submissions/79a22b38-392a-4357-b229-d7ff5147e2b8

/- Actual height-one density on [-1/4,0]. -/
import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Definitions.Def_MasulloRH_GaussianThetaTruncation
import Theorems.Thm_MasulloRH_theta_reflection
import Theorems.Thm_MasulloRH_theta_gaussian_truncation_error
import Theorems.Thm_MasulloRH_theta_reflected_truncation_error
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

set_option autoImplicit false
namespace N1LeftInnerProof

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
open MasulloRH.GaussianApproximation MasulloRH.ThetaReflectionCore
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

/- Source: PublicReflectedErrorWindow -/
section
set_option autoImplicit false
open MasulloRH.GaussianApproximation

theorem MasulloRH.theta_reflected_truncation_error_on_Icc
    (K : ℕ) (R y x : ℝ) (hx : x ∈ Set.Icc (-R) R) :
    ‖theta (x - y) - thetaPartialReflected K (x - y)‖ ≤
      (24 * Real.exp (-((K : ℝ) + 1) ^ 2 / 3)) *
        max 1 (Real.exp (R + y) / 2) := by
  refine (_root_.MasulloRH.theta_reflected_truncation_error K (x - y)).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply max_le_max le_rfl
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply Real.exp_le_exp.mpr
  linarith only [hx.1]

end

/- Source: Solutions.ThetaFinitePolynomial -/
section
set_option autoImplicit false
open scoped BigOperators

namespace MasulloRH.CertifiedExp

noncomputable def thetaPolynomial (K : ℕ) (r : ℝ) : ℝ :=
  ∑ n ∈ Finset.range K,
    (r ^ ((n + 1) ^ 2) - 3 * r ^ (4 * (n + 1) ^ 2) +
      2 * r ^ (16 * (n + 1) ^ 2))

theorem gaussian_factor_as_power (a z : ℝ) (d n : ℕ) :
    Real.exp (-a * ((d : ℝ) * (((n : ℝ) + 1) * z)) ^ 2) =
      (Real.exp (-a * z ^ 2)) ^ (d ^ 2 * (n + 1) ^ 2) := by
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem gaussian_term_as_powers (x : ℝ) (n : ℕ) :
    Real.exp (-Real.pi * (((n : ℝ) + 1) * Real.exp x) ^ 2) -
      3 * Real.exp (-Real.pi * (2 * (((n : ℝ) + 1) * Real.exp x)) ^ 2) +
      2 * Real.exp (-Real.pi * (4 * (((n : ℝ) + 1) * Real.exp x)) ^ 2) =
    (Real.exp (-Real.pi * Real.exp (2 * x))) ^ ((n + 1) ^ 2) -
      3 * (Real.exp (-Real.pi * Real.exp (2 * x))) ^ (4 * (n + 1) ^ 2) +
      2 * (Real.exp (-Real.pi * Real.exp (2 * x))) ^ (16 * (n + 1) ^ 2) := by
  have h1 := gaussian_factor_as_power Real.pi (Real.exp x) 1 n
  have h2 := gaussian_factor_as_power Real.pi (Real.exp x) 2 n
  have h4 := gaussian_factor_as_power Real.pi (Real.exp x) 4 n
  norm_num only [Nat.cast_ofNat, Nat.reducePow, one_mul] at h1 h2 h4
  have hexp : (Real.exp x) ^ 2 = Real.exp (2 * x) := by
    simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul x 2).symm
  rw [h1, h2, h4, hexp]

open MasulloRH.GaussianApproximation

theorem thetaPartial_eq_polynomial (K : ℕ) (x : ℝ) :
    thetaPartial K x =
      ((2 * thetaPolynomial K (Real.exp (-Real.pi * Real.exp (2 * x))) : ℝ) : ℂ) := by
  have hs : (∑ n ∈ Finset.range K,
      (Real.exp (-Real.pi * (((n : ℝ) + 1) * Real.exp x) ^ 2) -
        3 * Real.exp (-Real.pi * (2 * (((n : ℝ) + 1) * Real.exp x)) ^ 2) +
        2 * Real.exp (-Real.pi * (4 * (((n : ℝ) + 1) * Real.exp x)) ^ 2))) =
      thetaPolynomial K (Real.exp (-Real.pi * Real.exp (2 * x))) := by
    unfold thetaPolynomial
    apply Finset.sum_congr rfl
    intro n _
    exact gaussian_term_as_powers x n
  unfold thetaPartial
  rw [← Complex.ofReal_sum, hs]
  push_cast
  rfl

theorem thetaPartialReflected_eq_direct (K : ℕ) (x : ℝ) (hx : -1 ≤ x) :
    thetaPartialReflected K x =
      ((2 * thetaPolynomial K (Real.exp (-Real.pi * Real.exp (2 * x))) : ℝ) : ℂ) := by
  rw [thetaPartialReflected, if_pos hx, thetaPartial_eq_polynomial]

theorem thetaPartialReflected_eq_reflected (K : ℕ) (x : ℝ) (hx : x < -1) :
    thetaPartialReflected K x =
      ((Real.exp (-x) *
        thetaPolynomial K (Real.exp (-(Real.pi / 16) * Real.exp (-2 * x))) : ℝ) : ℂ) := by
  rw [thetaPartialReflected, if_neg (not_le.mpr hx), thetaPartial_eq_polynomial,
    ← Complex.ofReal_mul]
  have hlog : Real.exp (2 * (-x - Real.log 4)) = Real.exp (-2 * x) / 16 := by
    have hfour : Real.exp (2 * Real.log 4) = 16 := by
      have h := Real.exp_nat_mul (Real.log 4) 2
      norm_num [Real.exp_log (by norm_num : (0 : ℝ) < 4)] at h
      exact h
    rw [show 2 * (-x - Real.log 4) = (-2 * x) - 2 * Real.log 4 by ring,
      Real.exp_sub, hfour]
  rw [hlog]
  have harg : -Real.pi * (Real.exp (-2 * x) / 16) =
      -(Real.pi / 16) * Real.exp (-2 * x) := by ring
  rw [harg]
  congr 1
  ring

theorem thetaPolynomial_enclosure {r lo hi : ℝ} (K : ℕ)
    (hlo : 0 ≤ lo) (hr : lo ≤ r ∧ r ≤ hi) :
    (∑ n ∈ Finset.range K,
      (lo ^ ((n + 1) ^ 2) - 3 * hi ^ (4 * (n + 1) ^ 2) +
        2 * lo ^ (16 * (n + 1) ^ 2))) ≤ thetaPolynomial K r ∧
    thetaPolynomial K r ≤ (∑ n ∈ Finset.range K,
      (hi ^ ((n + 1) ^ 2) - 3 * lo ^ (4 * (n + 1) ^ 2) +
        2 * hi ^ (16 * (n + 1) ^ 2))) := by
  have hr0 := hlo.trans hr.1
  constructor
  · apply Finset.sum_le_sum
    intro n _
    have h1 := pow_le_pow_left₀ hlo hr.1 ((n + 1) ^ 2)
    have h2 := pow_le_pow_left₀ hr0 hr.2 (4 * (n + 1) ^ 2)
    have h4 := pow_le_pow_left₀ hlo hr.1 (16 * (n + 1) ^ 2)
    linarith
  · apply Finset.sum_le_sum
    intro n _
    have h1 := pow_le_pow_left₀ hr0 hr.2 ((n + 1) ^ 2)
    have h2 := pow_le_pow_left₀ hlo hr.1 (4 * (n + 1) ^ 2)
    have h4 := pow_le_pow_left₀ hr0 hr.2 (16 * (n + 1) ^ 2)
    linarith


end MasulloRH.CertifiedExp
end


/- Source: Solutions.ThetaNumericalConstants -/
section
set_option autoImplicit false

namespace MasulloRH.CertifiedExp

theorem pi_rational_enclosure :
    (3141592 / 1000000 : ℝ) ≤ Real.pi ∧
      Real.pi ≤ (3141593 / 1000000 : ℝ) := by
  constructor
  · linarith [Real.pi_gt_d6]
  · linarith [Real.pi_lt_d6]

theorem sqrt_pi_rational_enclosure :
    (1772453 / 1000000 : ℝ) ≤ Real.sqrt Real.pi ∧
      Real.sqrt Real.pi ≤ (1772454 / 1000000 : ℝ) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    nlinarith [pi_rational_enclosure.1]
  · apply (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 1772454 / 1000000)).2
    nlinarith [pi_rational_enclosure.2]

theorem pulse_two_coefficient_enclosure :
    (1128379 / 1000000 : ℝ) ≤ 2 / Real.sqrt Real.pi ∧
      2 / Real.sqrt Real.pi ≤ (1128380 / 1000000 : ℝ) := by
  have hpos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  constructor
  · apply (le_div_iff₀ hpos).2
    nlinarith [sqrt_pi_rational_enclosure.2]
  · apply (div_le_iff₀ hpos).2
    nlinarith [sqrt_pi_rational_enclosure.1]


end MasulloRH.CertifiedExp
end


/- Source: Solutions.ThetaExpCertificateCore -/
section
set_option autoImplicit false

open scoped BigOperators

namespace MasulloRH.CertifiedExp

/-- A finite rational certificate for an exponential on the unit interval. -/
theorem enclosure_of_taylor {x a b : ℝ} {n : ℕ}
    (hx : |x| ≤ 1) (hn : 0 < n)
    (hlo : a ≤ (∑ m ∈ Finset.range n, x ^ m / m.factorial) -
      |x| ^ n * ((n + 1 : ℕ) : ℝ) / (n.factorial * n))
    (hhi : (∑ m ∈ Finset.range n, x ^ m / m.factorial) +
      |x| ^ n * ((n + 1 : ℕ) : ℝ) / (n.factorial * n) ≤ b) :
    a ≤ Real.exp x ∧ Real.exp x ≤ b := by
  have h := Real.exp_bound hx hn
  have h' : |Real.exp x - ∑ m ∈ Finset.range n, x ^ m / m.factorial| ≤
      |x| ^ n * ((n + 1 : ℕ) : ℝ) / (n.factorial * n) := by
    simpa only [Nat.succ_eq_add_one, mul_div_assoc] using h
  constructor <;> linarith [(abs_le.mp h').1, (abs_le.mp h').2]

/-- Scaling, powering and reciprocation preserve certified rational endpoints.
The powers in the two final hypotheses are rational arithmetic only. -/
theorem neg_enclosure_of_scaled {t x a b l u : ℝ} {n : ℕ}
    (ht : t = n * x) (ha : 0 < a)
    (hsmall : a ≤ Real.exp x ∧ Real.exp x ≤ b)
    (hl : l ≤ 1 / b ^ n) (hu : 1 / a ^ n ≤ u) :
    l ≤ Real.exp (-t) ∧ Real.exp (-t) ≤ u := by
  have hlow := pow_le_pow_left₀ ha.le hsmall.1 n
  have hupp := pow_le_pow_left₀ (Real.exp_pos x).le hsmall.2 n
  rw [Real.exp_neg, ht, Real.exp_nat_mul, ← one_div]
  exact ⟨hl.trans (one_div_le_one_div_of_le (pow_pos (Real.exp_pos x) n) hupp),
    (one_div_le_one_div_of_le (pow_pos ha n) hlow).trans hu⟩

theorem enclosure_of_scaled {t x a b l u : ℝ} {n : ℕ}
    (ht : t = n * x) (ha : 0 ≤ a)
    (hsmall : a ≤ Real.exp x ∧ Real.exp x ≤ b)
    (hl : l ≤ a ^ n) (hu : b ^ n ≤ u) :
    l ≤ Real.exp t ∧ Real.exp t ≤ u := by
  rw [ht, Real.exp_nat_mul]
  exact ⟨hl.trans (pow_le_pow_left₀ ha hsmall.1 n),
    (pow_le_pow_left₀ (Real.exp_pos x).le hsmall.2 n).trans hu⟩

/-- A cheap enclosure for every sufficiently negative Gaussian exponent. -/
theorem neg_enclosure_of_twenty_le {t : ℝ} (ht : 20 ≤ t) :
    0 ≤ Real.exp (-t) ∧ Real.exp (-t) ≤ 1 / 1048576 := by
  have hbase : (2 : ℝ) ≤ Real.exp 1 := by
    linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hbase 20
  have hexp : Real.exp 1 ^ (20 : ℕ) = Real.exp 20 := by
    simpa only [Nat.cast_ofNat, mul_one] using (Real.exp_nat_mul (1 : ℝ) 20).symm
  rw [hexp] at hpow
  norm_num at hpow
  have ht' := hpow.trans (Real.exp_le_exp.mpr ht)
  refine ⟨(Real.exp_pos _).le, ?_⟩
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by norm_num) ht'

theorem enclosure_of_argument_interval {x a b l u : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hl : l ≤ Real.exp a) (hu : Real.exp b ≤ u) :
    l ≤ Real.exp x ∧ Real.exp x ≤ u :=
  ⟨hl.trans (Real.exp_le_exp.mpr hx.1), (Real.exp_le_exp.mpr hx.2).trans hu⟩


end MasulloRH.CertifiedExp
end


/- Source: Solutions.ThetaNumericalExponents -/
section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace MasulloRH.CertifiedExp

theorem exp_neg_49_div_3_enclosure :
    (40317 / 500000000000 : ℝ) ≤ Real.exp (-(49 / 3 : ℝ)) ∧
    Real.exp (-(49 / 3 : ℝ)) ≤ (16127 / 200000000000 : ℝ) := by
  have hsmall : (16659852101 / 10000000000 : ℝ) ≤ Real.exp (49 / 96 : ℝ) ∧
      Real.exp (49 / 96 : ℝ) ≤ (16659852109 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (49 / 96 : ℝ))
    (a := (16659852101 / 10000000000 : ℝ)) (b := (16659852109 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem exp_19_div_4_enclosure :
    (28896071 / 250000 : ℝ) ≤ Real.exp (19 / 4 : ℝ) ∧
    Real.exp (19 / 4 : ℝ) ≤ (23116857 / 200000 : ℝ) := by
  have hsmall : (3625063419501 / 3125000000000 : ℝ) ≤ Real.exp (19 / 128 : ℝ) ∧
      Real.exp (19 / 128 : ℝ) ≤ (116002029424033 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (19 / 128 : ℝ))
    (a := (3625063419501 / 3125000000000 : ℝ)) (b := (116002029424033 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem exp_truncation_six_le :
    Real.exp (-(49 / 3 : ℝ)) ≤ (1 / 10000000 : ℝ) :=
  exp_neg_49_div_3_enclosure.2.trans (by norm_num)

theorem exp_window_shift_le : Real.exp (19 / 4 : ℝ) ≤ 120 :=
  exp_19_div_4_enclosure.2.trans (by norm_num)


end MasulloRH.CertifiedExp
end


/- Source: Solutions.ThetaN1CellCore -/
section
set_option autoImplicit false
set_option maxHeartbeats 1000000

open MasulloRH.GaussianApproximation
open MasulloRH.CertifiedExp

namespace MasulloRH.HeightOne

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

theorem theta_error_six (x : ℝ) (hx : x ∈ Set.Icc (-4 : ℝ) 4) :
    ‖theta (x - 3 / 4) - thetaPartialReflected 6 (x - 3 / 4)‖ ≤
      (1 / 5000 : ℝ) := by
  have h := MasulloRH.theta_reflected_truncation_error_on_Icc 6 4 (3 / 4) x hx
  have he : Real.exp (4 + (3 / 4 : ℝ)) ≤ 120 := by
    convert exp_window_shift_le using 1 <;> norm_num
  have hm : max (1 : ℝ) (Real.exp (4 + (3 / 4 : ℝ)) / 2) ≤ 60 := by
    apply max_le (by norm_num)
    linarith
  have ht : Real.exp (-((6 : ℝ) + 1) ^ 2 / 3) ≤ (1 / 10000000 : ℝ) := by
    convert exp_truncation_six_le using 1 <;> norm_num
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 24))
    hm (by positivity) (by norm_num : (0 : ℝ) ≤ 24 * (1 / 10000000))
  norm_num only [Nat.cast_ofNat] at h
  norm_num at hh
  exact h.trans (hh.trans (by norm_num))

/-- A rational cell certificate for the actual height-one residual density.
The finite approximation is used only through an equality and an interval;
the actual theta error is discharged by the proved reflected tail estimate. -/
theorem density_le_of_intervals (x t pL pU tL tU r wU bound : ℝ)
    (hx : x ∈ Set.Icc (-4 : ℝ) 4)
    (htheta : thetaPartialReflected 6 (x - 3 / 4) = (t : ℂ))
    (hp : pL ≤ realPulse x ∧ realPulse x ≤ pU)
    (ht : tL ≤ t ∧ t ≤ tU)
    (hr : 0 ≤ r)
    (hlo : -r ≤ pL - (73 / 50 : ℝ) * tU)
    (hhi : pU - (73 / 50 : ℝ) * tL ≤ r)
    (hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ wU)
    (hfinal : wU * (r + (73 / 250000 : ℝ)) ^ 2 ≤ bound) :
    density x ≤ bound := by
  have hres : |realPulse x - (73 / 50 : ℝ) * t| ≤ r := by
    apply abs_le.mpr
    constructor <;> nlinarith [hp.1, hp.2, ht.1, ht.2]
  have happrox : ‖pulse 1 x - (73 / 50 : ℂ) * thetaPartialReflected 6 (x - 3 / 4)‖ ≤ r := by
    rw [pulse_eq_realPulse, htheta,
      show (73 / 50 : ℂ) = ((73 / 50 : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_mul, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    exact hres
  have herr := theta_error_six x hx
  have hnorm : ‖pulse 1 x - (73 / 50 : ℂ) * theta (x - 3 / 4)‖ ≤
      r + (73 / 250000 : ℝ) := by
    calc
      _ = ‖(pulse 1 x - (73 / 50 : ℂ) * thetaPartialReflected 6 (x - 3 / 4)) +
          (73 / 50 : ℂ) * (thetaPartialReflected 6 (x - 3 / 4) - theta (x - 3 / 4))‖ := by
        congr 1
        ring
      _ ≤ ‖pulse 1 x - (73 / 50 : ℂ) * thetaPartialReflected 6 (x - 3 / 4)‖ +
          ‖(73 / 50 : ℂ) * (thetaPartialReflected 6 (x - 3 / 4) - theta (x - 3 / 4))‖ := norm_add_le _ _
      _ ≤ r + (73 / 250000 : ℝ) := by
        rw [norm_mul, show ‖thetaPartialReflected 6 (x - 3 / 4) - theta (x - 3 / 4)‖ =
          ‖theta (x - 3 / 4) - thetaPartialReflected 6 (x - 3 / 4)‖ from norm_sub_rev _ _]
        have hc : ‖(73 / 50 : ℂ)‖ = (73 / 50 : ℝ) := by norm_num
        rw [hc]
        nlinarith
  unfold density
  calc
    _ ≤ Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) *
        (r + (73 / 250000 : ℝ)) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ wU * (r + (73 / 250000 : ℝ)) ^ 2 :=
      mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    _ ≤ bound := hfinal


end MasulloRH.HeightOne
end


section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
namespace MasulloRH.CertifiedExp
theorem n1_exp_157 :
    (7788007 / 10000000 : ℝ) ≤ Real.exp (-(1 / 4 : ℝ)) ∧
    Real.exp (-(1 / 4 : ℝ)) ≤ (973501 / 1250000 : ℝ) := by
  have hsmall : (2519607743 / 2500000000 : ℝ) ≤ Real.exp (1 / 128 : ℝ) ∧
      Real.exp (1 / 128 : ℝ) ≤ (10078430973 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1 / 128 : ℝ))
    (a := (2519607743 / 2500000000 : ℝ)) (b := (10078430973 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_159 :
    (169169 / 1250000 : ℝ) ≤ Real.exp (-(2 / 1 : ℝ)) ∧
    Real.exp (-(2 / 1 : ℝ)) ≤ (1353353 / 10000000 : ℝ) := by
  have hsmall : (10644944589 / 10000000000 : ℝ) ≤ Real.exp (1 / 16 : ℝ) ∧
      Real.exp (1 / 16 : ℝ) ≤ (1064494459 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1 / 16 : ℝ))
    (a := (10644944589 / 10000000000 : ℝ)) (b := (1064494459 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_160 :
    (174539 / 1250000 : ℝ) ≤ Real.exp (-(63 / 32 : ℝ)) ∧
    Real.exp (-(63 / 32 : ℝ)) ≤ (1396313 / 10000000 : ℝ) := by
  have hsmall : (10634554209 / 10000000000 : ℝ) ≤ Real.exp (63 / 1024 : ℝ) ∧
      Real.exp (63 / 1024 : ℝ) ≤ (1063455421 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (63 / 1024 : ℝ))
    (a := (10634554209 / 10000000000 : ℝ)) (b := (1063455421 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_161 :
    (6448969 / 10000000 : ℝ) ≤ Real.exp (-(548331 / 1250000 : ℝ)) ∧
    Real.exp (-(548331 / 1250000 : ℝ)) ≤ (644897 / 1000000 : ℝ) := by
  have hsmall : (5069013321 / 5000000000 : ℝ) ≤ Real.exp (548331 / 40000000 : ℝ) ∧
      Real.exp (548331 / 40000000 : ℝ) ≤ (10138026643 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (548331 / 40000000 : ℝ))
    (a := (5069013321 / 5000000000 : ℝ)) (b := (10138026643 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_162 :
    (32683 / 50000 : ℝ) ≤ Real.exp (-(4251679 / 10000000 : ℝ)) ∧
    Real.exp (-(4251679 / 10000000 : ℝ)) ≤ (6536601 / 10000000 : ℝ) := by
  have hsmall : (2026750309 / 2000000000 : ℝ) ≤ Real.exp (4251679 / 320000000 : ℝ) ∧
      Real.exp (4251679 / 320000000 : ℝ) ≤ (5066875773 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (4251679 / 320000000 : ℝ))
    (a := (2026750309 / 2000000000 : ℝ)) (b := (5066875773 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_163 :
    (4013691 / 5000000 : ℝ) ≤ Real.exp (-(225 / 1024 : ℝ)) ∧
    Real.exp (-(225 / 1024 : ℝ)) ≤ (8027383 / 10000000 : ℝ) := by
  have hsmall : (314653151 / 312500000 : ℝ) ≤ Real.exp (225 / 32768 : ℝ) ∧
      Real.exp (225 / 32768 : ℝ) ≤ (10068900833 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (225 / 32768 : ℝ))
    (a := (314653151 / 312500000 : ℝ)) (b := (10068900833 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_164 :
    (7795617 / 10000000 : ℝ) ≤ Real.exp (-(255 / 1024 : ℝ)) ∧
    Real.exp (-(255 / 1024 : ℝ)) ≤ (3897809 / 5000000 : ℝ) := by
  have hsmall : (10078123407 / 10000000000 : ℝ) ≤ Real.exp (255 / 32768 : ℝ) ∧
      Real.exp (255 / 32768 : ℝ) ≤ (629882713 / 625000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (255 / 32768 : ℝ))
    (a := (10078123407 / 10000000000 : ℝ)) (b := (629882713 / 625000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_165 :
    (360159 / 2500000 : ℝ) ≤ Real.exp (-(31 / 16 : ℝ)) ∧
    Real.exp (-(31 / 16 : ℝ)) ≤ (1440637 / 10000000 : ℝ) := by
  have hsmall : (2656043493 / 2500000000 : ℝ) ≤ Real.exp (31 / 512 : ℝ) ∧
      Real.exp (31 / 512 : ℝ) ≤ (10624173973 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (31 / 512 : ℝ))
    (a := (2656043493 / 2500000000 : ℝ)) (b := (10624173973 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_166 :
    (635979 / 1000000 : ℝ) ≤ Real.exp (-(565737 / 1250000 : ℝ)) ∧
    Real.exp (-(565737 / 1250000 : ℝ)) ≤ (6359791 / 10000000 : ℝ) := by
  have hsmall : (2535609791 / 2500000000 : ℝ) ≤ Real.exp (565737 / 40000000 : ℝ) ∧
      Real.exp (565737 / 40000000 : ℝ) ≤ (2028487833 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (565737 / 40000000 : ℝ))
    (a := (2535609791 / 2500000000 : ℝ)) (b := (2028487833 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_167 :
    (1612243 / 2500000 : ℝ) ≤ Real.exp (-(2193321 / 5000000 : ℝ)) ∧
    Real.exp (-(2193321 / 5000000 : ℝ)) ≤ (6448973 / 10000000 : ℝ) := by
  have hsmall : (2534506613 / 2500000000 : ℝ) ≤ Real.exp (2193321 / 160000000 : ℝ) ∧
      Real.exp (2193321 / 160000000 : ℝ) ≤ (10138026453 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2193321 / 160000000 : ℝ))
    (a := (2534506613 / 2500000000 : ℝ)) (b := (10138026453 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_168 :
    (825797 / 1000000 : ℝ) ≤ Real.exp (-(49 / 256 : ℝ)) ∧
    Real.exp (-(49 / 256 : ℝ)) ≤ (8257971 / 10000000 : ℝ) := by
  have hsmall : (5029996849 / 5000000000 : ℝ) ≤ Real.exp (49 / 8192 : ℝ) ∧
      Real.exp (49 / 8192 : ℝ) ≤ (10059993699 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (49 / 8192 : ℝ))
    (a := (5029996849 / 5000000000 : ℝ)) (b := (10059993699 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_169 :
    (1981529 / 2500000 : ℝ) ≤ Real.exp (-(119 / 512 : ℝ)) ∧
    Real.exp (-(119 / 512 : ℝ)) ≤ (7926117 / 10000000 : ℝ) := by
  have hsmall : (2518224061 / 2500000000 : ℝ) ≤ Real.exp (119 / 16384 : ℝ) ∧
      Real.exp (119 / 16384 : ℝ) ≤ (2014579249 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (119 / 16384 : ℝ))
    (a := (2518224061 / 2500000000 : ℝ)) (b := (2014579249 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_170 :
    (1486367 / 10000000 : ℝ) ≤ Real.exp (-(61 / 32 : ℝ)) ∧
    Real.exp (-(61 / 32 : ℝ)) ≤ (46449 / 312500 : ℝ) := by
  have hsmall : (5306901933 / 5000000000 : ℝ) ≤ Real.exp (61 / 1024 : ℝ) ∧
      Real.exp (61 / 1024 : ℝ) ≤ (10613803867 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (61 / 1024 : ℝ))
    (a := (5306901933 / 5000000000 : ℝ)) (b := (10613803867 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_171 :
    (3134537 / 5000000 : ℝ) ≤ Real.exp (-(1167391 / 2500000 : ℝ)) ∧
    Real.exp (-(1167391 / 2500000 : ℝ)) ≤ (250763 / 400000 : ℝ) := by
  have hsmall : (10146993761 / 10000000000 : ℝ) ≤ Real.exp (1167391 / 80000000 : ℝ) ∧
      Real.exp (1167391 / 80000000 : ℝ) ≤ (5073496881 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1167391 / 80000000 : ℝ))
    (a := (10146993761 / 10000000000 : ℝ)) (b := (5073496881 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_172 :
    (3179897 / 5000000 : ℝ) ≤ Real.exp (-(452589 / 1000000 : ℝ)) ∧
    Real.exp (-(452589 / 1000000 : ℝ)) ≤ (1271959 / 2000000 : ℝ) := by
  have hsmall : (5071219487 / 5000000000 : ℝ) ≤ Real.exp (452589 / 32000000 : ℝ) ∧
      Real.exp (452589 / 32000000 : ℝ) ≤ (405697559 / 400000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (452589 / 32000000 : ℝ))
    (a := (5071219487 / 5000000000 : ℝ)) (b := (405697559 / 400000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_173 :
    (1695721 / 2000000 : ℝ) ≤ Real.exp (-(169 / 1024 : ℝ)) ∧
    Real.exp (-(169 / 1024 : ℝ)) ≤ (4239303 / 5000000 : ℝ) := by
  have hsmall : (10051707933 / 10000000000 : ℝ) ≤ Real.exp (169 / 32768 : ℝ) ∧
      Real.exp (169 / 32768 : ℝ) ≤ (5025853967 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (169 / 32768 : ℝ))
    (a := (10051707933 / 10000000000 : ℝ)) (b := (5025853967 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_174 :
    (20147 / 25000 : ℝ) ≤ Real.exp (-(221 / 1024 : ℝ)) ∧
    Real.exp (-(221 / 1024 : ℝ)) ≤ (8058801 / 10000000 : ℝ) := by
  have hsmall : (10067671793 / 10000000000 : ℝ) ≤ Real.exp (221 / 32768 : ℝ) ∧
      Real.exp (221 / 32768 : ℝ) ≤ (5033835897 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (221 / 32768 : ℝ))
    (a := (10067671793 / 10000000000 : ℝ)) (b := (5033835897 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_175 :
    (1533549 / 10000000 : ℝ) ≤ Real.exp (-(15 / 8 : ℝ)) ∧
    Real.exp (-(15 / 8 : ℝ)) ≤ (30671 / 200000 : ℝ) := by
  have hsmall : (10603443883 / 10000000000 : ℝ) ≤ Real.exp (15 / 256 : ℝ) ∧
      Real.exp (15 / 256 : ℝ) ≤ (2650860971 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (15 / 256 : ℝ))
    (a := (10603443883 / 10000000000 : ℝ)) (b := (2650860971 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_176 :
    (1235367 / 2000000 : ℝ) ≤ Real.exp (-(481779 / 1000000 : ℝ)) ∧
    Real.exp (-(481779 / 1000000 : ℝ)) ≤ (1544209 / 2500000 : ℝ) := by
  have hsmall : (10151695001 / 10000000000 : ℝ) ≤ Real.exp (481779 / 32000000 : ℝ) ∧
      Real.exp (481779 / 32000000 : ℝ) ≤ (5075847501 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (481779 / 32000000 : ℝ))
    (a := (10151695001 / 10000000000 : ℝ)) (b := (5075847501 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_177 :
    (6269077 / 10000000 : ℝ) ≤ Real.exp (-(2334779 / 5000000 : ℝ)) ∧
    Real.exp (-(2334779 / 5000000 : ℝ)) ≤ (3134539 / 5000000 : ℝ) := by
  have hsmall : (10146993571 / 10000000000 : ℝ) ≤ Real.exp (2334779 / 160000000 : ℝ) ∧
      Real.exp (2334779 / 160000000 : ℝ) ≤ (2536748393 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2334779 / 160000000 : ℝ))
    (a := (10146993571 / 10000000000 : ℝ)) (b := (2536748393 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_178 :
    (173763 / 200000 : ℝ) ≤ Real.exp (-(9 / 64 : ℝ)) ∧
    Real.exp (-(9 / 64 : ℝ)) ≤ (8688151 / 10000000 : ℝ) := by
  have hsmall : (10044042013 / 10000000000 : ℝ) ≤ Real.exp (9 / 2048 : ℝ) ∧
      Real.exp (9 / 2048 : ℝ) ≤ (5022021007 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (9 / 2048 : ℝ))
    (a := (10044042013 / 10000000000 : ℝ)) (b := (5022021007 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_179 :
    (4096853 / 5000000 : ℝ) ≤ Real.exp (-(51 / 256 : ℝ)) ∧
    Real.exp (-(51 / 256 : ℝ)) ≤ (8193707 / 10000000 : ℝ) := by
  have hsmall : (10062450051 / 10000000000 : ℝ) ≤ Real.exp (51 / 8192 : ℝ) ∧
      Real.exp (51 / 8192 : ℝ) ≤ (2515612513 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (51 / 8192 : ℝ))
    (a := (10062450051 / 10000000000 : ℝ)) (b := (2515612513 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_180 :
    (1582229 / 10000000 : ℝ) ≤ Real.exp (-(59 / 32 : ℝ)) ∧
    Real.exp (-(59 / 32 : ℝ)) ≤ (158223 / 1000000 : ℝ) := by
  have hsmall : (2648273503 / 2500000000 : ℝ) ≤ Real.exp (59 / 1024 : ℝ) ∧
      Real.exp (59 / 1024 : ℝ) ≤ (10593094013 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (59 / 1024 : ℝ))
    (a := (2648273503 / 2500000000 : ℝ)) (b := (10593094013 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_181 :
    (608309 / 1000000 : ℝ) ≤ Real.exp (-(4970723 / 10000000 : ℝ)) ∧
    Real.exp (-(4970723 / 10000000 : ℝ)) ≤ (6083091 / 10000000 : ℝ) := by
  have hsmall : (5078273907 / 5000000000 : ℝ) ≤ Real.exp (4970723 / 320000000 : ℝ) ∧
      Real.exp (4970723 / 320000000 : ℝ) ≤ (2031309563 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (4970723 / 320000000 : ℝ))
    (a := (5078273907 / 5000000000 : ℝ)) (b := (2031309563 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_182 :
    (3088419 / 5000000 : ℝ) ≤ Real.exp (-(963557 / 2000000 : ℝ)) ∧
    Real.exp (-(963557 / 2000000 : ℝ)) ≤ (6176839 / 10000000 : ℝ) := by
  have hsmall : (5075847421 / 5000000000 : ℝ) ≤ Real.exp (963557 / 64000000 : ℝ) ∧
      Real.exp (963557 / 64000000 : ℝ) ≤ (10151694843 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (963557 / 64000000 : ℝ))
    (a := (5075847421 / 5000000000 : ℝ)) (b := (10151694843 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_183 :
    (4442751 / 5000000 : ℝ) ≤ Real.exp (-(121 / 1024 : ℝ)) ∧
    Real.exp (-(121 / 1024 : ℝ)) ≤ (8885503 / 10000000 : ℝ) := by
  have hsmall : (1003699453 / 1000000000 : ℝ) ≤ Real.exp (121 / 32768 : ℝ) ∧
      Real.exp (121 / 32768 : ℝ) ≤ (10036994531 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (121 / 32768 : ℝ))
    (a := (1003699453 / 1000000000 : ℝ)) (b := (10036994531 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_184 :
    (833087 / 1000000 : ℝ) ≤ Real.exp (-(187 / 1024 : ℝ)) ∧
    Real.exp (-(187 / 1024 : ℝ)) ≤ (8330871 / 10000000 : ℝ) := by
  have hsmall : (5028615509 / 5000000000 : ℝ) ≤ Real.exp (187 / 32768 : ℝ) ∧
      Real.exp (187 / 32768 : ℝ) ≤ (10057231019 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (187 / 32768 : ℝ))
    (a := (5028615509 / 5000000000 : ℝ)) (b := (10057231019 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_185 :
    (326491 / 2000000 : ℝ) ≤ Real.exp (-(29 / 16 : ℝ)) ∧
    Real.exp (-(29 / 16 : ℝ)) ≤ (204057 / 1250000 : ℝ) := by
  have hsmall : (10582754243 / 10000000000 : ℝ) ≤ Real.exp (29 / 512 : ℝ) ∧
      Real.exp (29 / 512 : ℝ) ≤ (2645688561 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (29 / 512 : ℝ))
    (a := (10582754243 / 10000000000 : ℝ)) (b := (2645688561 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_186 :
    (2993929 / 5000000 : ℝ) ≤ Real.exp (-(5128513 / 10000000 : ℝ)) ∧
    Real.exp (-(5128513 / 10000000 : ℝ)) ≤ (5987859 / 10000000 : ℝ) := by
  have hsmall : (10161557179 / 10000000000 : ℝ) ≤ Real.exp (5128513 / 320000000 : ℝ) ∧
      Real.exp (5128513 / 320000000 : ℝ) ≤ (508077859 / 500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5128513 / 320000000 : ℝ))
    (a := (10161557179 / 10000000000 : ℝ)) (b := (508077859 / 500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_187 :
    (6083093 / 10000000 : ℝ) ≤ Real.exp (-(4970717 / 10000000 : ℝ)) ∧
    Real.exp (-(4970717 / 10000000 : ℝ)) ≤ (3041547 / 5000000 : ℝ) := by
  have hsmall : (1269568453 / 1250000000 : ℝ) ≤ Real.exp (4970717 / 320000000 : ℝ) ∧
      Real.exp (4970717 / 320000000 : ℝ) ≤ (81252381 / 80000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (4970717 / 320000000 : ℝ))
    (a := (1269568453 / 1250000000 : ℝ)) (b := (81252381 / 80000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_188 :
    (4534803 / 5000000 : ℝ) ≤ Real.exp (-(25 / 256 : ℝ)) ∧
    Real.exp (-(25 / 256 : ℝ)) ≤ (9069607 / 10000000 : ℝ) := by
  have hsmall : (10030564191 / 10000000000 : ℝ) ≤ Real.exp (25 / 8192 : ℝ) ∧
      Real.exp (25 / 8192 : ℝ) ≤ (313455131 / 312500000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (25 / 8192 : ℝ))
    (a := (10030564191 / 10000000000 : ℝ)) (b := (313455131 / 312500000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_189 :
    (8470329 / 10000000 : ℝ) ≤ Real.exp (-(85 / 512 : ℝ)) ∧
    Real.exp (-(85 / 512 : ℝ)) ≤ (8470331 / 10000000 : ℝ) := by
  have hsmall : (10052014691 / 10000000000 : ℝ) ≤ Real.exp (85 / 16384 : ℝ) ∧
      Real.exp (85 / 16384 : ℝ) ≤ (2513003673 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (85 / 16384 : ℝ))
    (a := (10052014691 / 10000000000 : ℝ)) (b := (2513003673 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_190 :
    (842137 / 5000000 : ℝ) ≤ Real.exp (-(57 / 32 : ℝ)) ∧
    Real.exp (-(57 / 32 : ℝ)) ≤ (67371 / 400000 : ℝ) := by
  have hsmall : (5286212283 / 5000000000 : ℝ) ≤ Real.exp (57 / 1024 : ℝ) ∧
      Real.exp (57 / 1024 : ℝ) ≤ (10572424567 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (57 / 1024 : ℝ))
    (a := (5286212283 / 5000000000 : ℝ)) (b := (10572424567 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_191 :
    (184099 / 312500 : ℝ) ≤ Real.exp (-(5291307 / 10000000 : ℝ)) ∧
    Real.exp (-(5291307 / 10000000 : ℝ)) ≤ (5891169 / 10000000 : ℝ) := by
  have hsmall : (2541681999 / 2500000000 : ℝ) ≤ Real.exp (5291307 / 320000000 : ℝ) ∧
      Real.exp (5291307 / 320000000 : ℝ) ≤ (10166727997 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5291307 / 320000000 : ℝ))
    (a := (2541681999 / 2500000000 : ℝ)) (b := (10166727997 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_192 :
    (5987861 / 10000000 : ℝ) ≤ Real.exp (-(5128507 / 10000000 : ℝ)) ∧
    Real.exp (-(5128507 / 10000000 : ℝ)) ≤ (2993931 / 5000000 : ℝ) := by
  have hsmall : (10161556989 / 10000000000 : ℝ) ≤ Real.exp (5128507 / 320000000 : ℝ) ∧
      Real.exp (5128507 / 320000000 : ℝ) ≤ (1016155699 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5128507 / 320000000 : ℝ))
    (a := (10161556989 / 10000000000 : ℝ)) (b := (1016155699 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_193 :
    (461973 / 500000 : ℝ) ≤ Real.exp (-(81 / 1024 : ℝ)) ∧
    Real.exp (-(81 / 1024 : ℝ)) ≤ (9239461 / 10000000 : ℝ) := by
  have hsmall : (2004949963 / 2000000000 : ℝ) ≤ Real.exp (81 / 32768 : ℝ) ∧
      Real.exp (81 / 32768 : ℝ) ≤ (1253093727 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (81 / 32768 : ℝ))
    (a := (2004949963 / 2000000000 : ℝ)) (b := (1253093727 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_194 :
    (2153031 / 2500000 : ℝ) ≤ Real.exp (-(153 / 1024 : ℝ)) ∧
    Real.exp (-(153 / 1024 : ℝ)) ≤ (68897 / 80000 : ℝ) := by
  have hsmall : (10046801071 / 10000000000 : ℝ) ≤ Real.exp (153 / 32768 : ℝ) ∧
      Real.exp (153 / 32768 : ℝ) ≤ (627925067 / 625000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (153 / 32768 : ℝ))
    (a := (10046801071 / 10000000000 : ℝ)) (b := (627925067 / 625000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_195 :
    (1737739 / 10000000 : ℝ) ≤ Real.exp (-(7 / 4 : ℝ)) ∧
    Real.exp (-(7 / 4 : ℝ)) ≤ (86887 / 500000 : ℝ) := by
  have hsmall : (10562104973 / 10000000000 : ℝ) ≤ Real.exp (7 / 128 : ℝ) ∧
      Real.exp (7 / 128 : ℝ) ≤ (5281052487 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7 / 128 : ℝ))
    (a := (10562104973 / 10000000000 : ℝ)) (b := (5281052487 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_196 :
    (1448261 / 2500000 : ℝ) ≤ Real.exp (-(682409 / 1250000 : ℝ)) ∧
    Real.exp (-(682409 / 1250000 : ℝ)) ≤ (1158609 / 2000000 : ℝ) := by
  have hsmall : (10172065817 / 10000000000 : ℝ) ≤ Real.exp (682409 / 40000000 : ℝ) ∧
      Real.exp (682409 / 40000000 : ℝ) ≤ (5086032909 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (682409 / 40000000 : ℝ))
    (a := (10172065817 / 10000000000 : ℝ)) (b := (5086032909 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_197 :
    (1472793 / 2500000 : ℝ) ≤ Real.exp (-(5291301 / 10000000 : ℝ)) ∧
    Real.exp (-(5291301 / 10000000 : ℝ)) ≤ (5891173 / 10000000 : ℝ) := by
  have hsmall : (2033345561 / 2000000000 : ℝ) ≤ Real.exp (5291301 / 320000000 : ℝ) ∧
      Real.exp (5291301 / 320000000 : ℝ) ≤ (5083363903 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5291301 / 320000000 : ℝ))
    (a := (2033345561 / 2000000000 : ℝ)) (b := (5083363903 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_198 :
    (939413 / 1000000 : ℝ) ≤ Real.exp (-(1 / 16 : ℝ)) ∧
    Real.exp (-(1 / 16 : ℝ)) ≤ (9394131 / 10000000 : ℝ) := by
  have hsmall : (2003910067 / 2000000000 : ℝ) ≤ Real.exp (1 / 512 : ℝ) ∧
      Real.exp (1 / 512 : ℝ) ≤ (78277737 / 78125000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1 / 512 : ℝ))
    (a := (2003910067 / 2000000000 : ℝ)) (b := (78277737 / 78125000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_199 :
    (2189073 / 2500000 : ℝ) ≤ Real.exp (-(17 / 128 : ℝ)) ∧
    Real.exp (-(17 / 128 : ℝ)) ≤ (8756293 / 10000000 : ℝ) := by
  have hsmall : (5020795077 / 5000000000 : ℝ) ≤ Real.exp (17 / 4096 : ℝ) ∧
      Real.exp (17 / 4096 : ℝ) ≤ (2008318031 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (17 / 4096 : ℝ))
    (a := (5020795077 / 5000000000 : ℝ)) (b := (2008318031 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_200 :
    (1792901 / 10000000 : ℝ) ≤ Real.exp (-(55 / 32 : ℝ)) ∧
    Real.exp (-(55 / 32 : ℝ)) ≤ (896451 / 5000000 : ℝ) := by
  have hsmall : (2637948863 / 2500000000 : ℝ) ≤ Real.exp (55 / 1024 : ℝ) ∧
      Real.exp (55 / 1024 : ℝ) ≤ (10551795453 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (55 / 1024 : ℝ))
    (a := (2637948863 / 2500000000 : ℝ)) (b := (10551795453 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_201 :
    (5693517 / 10000000 : ℝ) ≤ Real.exp (-(5632569 / 10000000 : ℝ)) ∧
    Real.exp (-(5632569 / 10000000 : ℝ)) ≤ (2846759 / 5000000 : ℝ) := by
  have hsmall : (10177576023 / 10000000000 : ℝ) ≤ Real.exp (5632569 / 320000000 : ℝ) ∧
      Real.exp (5632569 / 320000000 : ℝ) ≤ (1272197003 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5632569 / 320000000 : ℝ))
    (a := (10177576023 / 10000000000 : ℝ)) (b := (1272197003 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_202 :
    (5793047 / 10000000 : ℝ) ≤ Real.exp (-(2729633 / 5000000 : ℝ)) ∧
    Real.exp (-(2729633 / 5000000 : ℝ)) ≤ (724131 / 1250000 : ℝ) := by
  have hsmall : (5086032813 / 5000000000 : ℝ) ≤ Real.exp (2729633 / 160000000 : ℝ) ∧
      Real.exp (2729633 / 160000000 : ℝ) ≤ (10172065627 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2729633 / 160000000 : ℝ))
    (a := (5086032813 / 5000000000 : ℝ)) (b := (10172065627 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_203 :
    (595797 / 625000 : ℝ) ≤ Real.exp (-(49 / 1024 : ℝ)) ∧
    Real.exp (-(49 / 1024 : ℝ)) ≤ (9532753 / 10000000 : ℝ) := by
  have hsmall : (10014964799 / 10000000000 : ℝ) ≤ Real.exp (49 / 32768 : ℝ) ∧
      Real.exp (49 / 32768 : ℝ) ≤ (6259353 / 6250000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (49 / 32768 : ℝ))
    (a := (10014964799 / 10000000000 : ℝ)) (b := (6259353 / 6250000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_204 :
    (4451437 / 5000000 : ℝ) ≤ Real.exp (-(119 / 1024 : ℝ)) ∧
    Real.exp (-(119 / 1024 : ℝ)) ≤ (71223 / 80000 : ℝ) := by
  have hsmall : (501819097 / 500000000 : ℝ) ≤ Real.exp (119 / 32768 : ℝ) ∧
      Real.exp (119 / 32768 : ℝ) ≤ (10036381941 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (119 / 32768 : ℝ))
    (a := (501819097 / 500000000 : ℝ)) (b := (10036381941 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_205 :
    (1849813 / 10000000 : ℝ) ≤ Real.exp (-(27 / 16 : ℝ)) ∧
    Real.exp (-(27 / 16 : ℝ)) ≤ (369963 / 2000000 : ℝ) := by
  have hsmall : (5270747997 / 5000000000 : ℝ) ≤ Real.exp (27 / 512 : ℝ) ∧
      Real.exp (27 / 512 : ℝ) ≤ (2108299199 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (27 / 512 : ℝ))
    (a := (5270747997 / 5000000000 : ℝ)) (b := (2108299199 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_206 :
    (5592623 / 10000000 : ℝ) ≤ Real.exp (-(2905683 / 5000000 : ℝ)) ∧
    Real.exp (-(2905683 / 5000000 : ℝ)) ≤ (349539 / 625000 : ℝ) := by
  have hsmall : (10183264237 / 10000000000 : ℝ) ≤ Real.exp (2905683 / 160000000 : ℝ) ∧
      Real.exp (2905683 / 160000000 : ℝ) ≤ (5091632119 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2905683 / 160000000 : ℝ))
    (a := (10183264237 / 10000000000 : ℝ)) (b := (5091632119 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_207 :
    (71169 / 125000 : ℝ) ≤ Real.exp (-(5632563 / 10000000 : ℝ)) ∧
    Real.exp (-(5632563 / 10000000 : ℝ)) ≤ (5693521 / 10000000 : ℝ) := by
  have hsmall : (1272196979 / 1250000000 : ℝ) ≤ Real.exp (5632563 / 320000000 : ℝ) ∧
      Real.exp (5632563 / 320000000 : ℝ) ≤ (10177575833 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5632563 / 320000000 : ℝ))
    (a := (1272196979 / 1250000000 : ℝ)) (b := (10177575833 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_208 :
    (1930909 / 2000000 : ℝ) ≤ Real.exp (-(9 / 256 : ℝ)) ∧
    Real.exp (-(9 / 256 : ℝ)) ≤ (4827273 / 5000000 : ℝ) := by
  have hsmall : (2002198473 / 2000000000 : ℝ) ≤ Real.exp (9 / 8192 : ℝ) ∧
      Real.exp (9 / 8192 : ℝ) ≤ (5005496183 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (9 / 8192 : ℝ))
    (a := (2002198473 / 2000000000 : ℝ)) (b := (5005496183 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_209 :
    (9051909 / 10000000 : ℝ) ≤ Real.exp (-(51 / 512 : ℝ)) ∧
    Real.exp (-(51 / 512 : ℝ)) ≤ (905191 / 1000000 : ℝ) := by
  have hsmall : (10031176427 / 10000000000 : ℝ) ≤ Real.exp (51 / 16384 : ℝ) ∧
      Real.exp (51 / 16384 : ℝ) ≤ (2507794107 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (51 / 16384 : ℝ))
    (a := (10031176427 / 10000000000 : ℝ)) (b := (2507794107 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_210 :
    (1908533 / 10000000 : ℝ) ≤ Real.exp (-(53 / 32 : ℝ)) ∧
    Real.exp (-(53 / 32 : ℝ)) ≤ (954267 / 5000000 : ℝ) := by
  have hsmall : (10531206589 / 10000000000 : ℝ) ≤ Real.exp (53 / 1024 : ℝ) ∧
      Real.exp (53 / 1024 : ℝ) ≤ (1053120659 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (53 / 1024 : ℝ))
    (a := (10531206589 / 10000000000 : ℝ)) (b := (1053120659 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_211 :
    (6863 / 12500 : ℝ) ≤ Real.exp (-(2997919 / 5000000 : ℝ)) ∧
    Real.exp (-(2997919 / 5000000 : ℝ)) ≤ (5490401 / 10000000 : ℝ) := by
  have hsmall : (10189136327 / 10000000000 : ℝ) ≤ Real.exp (2997919 / 160000000 : ℝ) ∧
      Real.exp (2997919 / 160000000 : ℝ) ≤ (1273642041 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2997919 / 160000000 : ℝ))
    (a := (10189136327 / 10000000000 : ℝ)) (b := (1273642041 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_212 :
    (1398157 / 2500000 : ℝ) ≤ Real.exp (-(5811357 / 10000000 : ℝ)) ∧
    Real.exp (-(5811357 / 10000000 : ℝ)) ≤ (5592629 / 10000000 : ℝ) := by
  have hsmall : (10183263951 / 10000000000 : ℝ) ≤ Real.exp (5811357 / 320000000 : ℝ) ∧
      Real.exp (5811357 / 320000000 : ℝ) ≤ (636453997 / 625000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5811357 / 320000000 : ℝ))
    (a := (10183263951 / 10000000000 : ℝ)) (b := (636453997 / 625000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_213 :
    (1951763 / 2000000 : ℝ) ≤ Real.exp (-(25 / 1024 : ℝ)) ∧
    Real.exp (-(25 / 1024 : ℝ)) ≤ (304963 / 312500 : ℝ) := by
  have hsmall : (2001526461 / 2000000000 : ℝ) ≤ Real.exp (25 / 32768 : ℝ) ∧
      Real.exp (25 / 32768 : ℝ) ≤ (5003816153 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (25 / 32768 : ℝ))
    (a := (2001526461 / 2000000000 : ℝ)) (b := (5003816153 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_214 :
    (9203439 / 10000000 : ℝ) ≤ Real.exp (-(85 / 1024 : ℝ)) ∧
    Real.exp (-(85 / 1024 : ℝ)) ≤ (115043 / 125000 : ℝ) := by
  have hsmall : (5012986807 / 5000000000 : ℝ) ≤ Real.exp (85 / 32768 : ℝ) ∧
      Real.exp (85 / 32768 : ℝ) ≤ (2005194723 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (85 / 32768 : ℝ))
    (a := (5012986807 / 5000000000 : ℝ)) (b := (2005194723 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_215 :
    (492279 / 2500000 : ℝ) ≤ Real.exp (-(13 / 8 : ℝ)) ∧
    Real.exp (-(13 / 8 : ℝ)) ≤ (1969117 / 10000000 : ℝ) := by
  have hsmall : (2630231807 / 2500000000 : ℝ) ≤ Real.exp (13 / 256 : ℝ) ∧
      Real.exp (13 / 256 : ℝ) ≤ (10520927229 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (13 / 256 : ℝ))
    (a := (2630231807 / 2500000000 : ℝ)) (b := (10520927229 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_216 :
    (5386891 / 10000000 : ℝ) ≤ Real.exp (-(1237233 / 2000000 : ℝ)) ∧
    Real.exp (-(1237233 / 2000000 : ℝ)) ≤ (1346723 / 2500000 : ℝ) := by
  have hsmall : (10195198341 / 10000000000 : ℝ) ≤ Real.exp (1237233 / 64000000 : ℝ) ∧
      Real.exp (1237233 / 64000000 : ℝ) ≤ (5097599171 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1237233 / 64000000 : ℝ))
    (a := (10195198341 / 10000000000 : ℝ)) (b := (5097599171 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_217 :
    (1372601 / 2500000 : ℝ) ≤ Real.exp (-(749479 / 1250000 : ℝ)) ∧
    Real.exp (-(749479 / 1250000 : ℝ)) ≤ (1098081 / 2000000 : ℝ) := by
  have hsmall : (1273642017 / 1250000000 : ℝ) ≤ Real.exp (749479 / 40000000 : ℝ) ∧
      Real.exp (749479 / 40000000 : ℝ) ≤ (10189136137 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (749479 / 40000000 : ℝ))
    (a := (1273642017 / 1250000000 : ℝ)) (b := (10189136137 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_218 :
    (2461241 / 2500000 : ℝ) ≤ Real.exp (-(1 / 64 : ℝ)) ∧
    Real.exp (-(1 / 64 : ℝ)) ≤ (1968993 / 2000000 : ℝ) := by
  have hsmall : (2501221001 / 2500000000 : ℝ) ≤ Real.exp (1 / 2048 : ℝ) ∧
      Real.exp (1 / 2048 : ℝ) ≤ (2000976801 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1 / 2048 : ℝ))
    (a := (2501221001 / 2500000000 : ℝ)) (b := (2000976801 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_219 :
    (4678753 / 5000000 : ℝ) ≤ Real.exp (-(17 / 256 : ℝ)) ∧
    Real.exp (-(17 / 256 : ℝ)) ≤ (9357507 / 10000000 : ℝ) := by
  have hsmall : (20041547 / 20000000 : ℝ) ≤ Real.exp (17 / 8192 : ℝ) ∧
      Real.exp (17 / 8192 : ℝ) ≤ (10020773501 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (17 / 8192 : ℝ))
    (a := (20041547 / 20000000 : ℝ)) (b := (10020773501 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_220 :
    (2031623 / 10000000 : ℝ) ≤ Real.exp (-(51 / 32 : ℝ)) ∧
    Real.exp (-(51 / 32 : ℝ)) ≤ (253953 / 1250000 : ℝ) := by
  have hsmall : (105106579 / 100000000 : ℝ) ≤ Real.exp (51 / 1024 : ℝ) ∧
      Real.exp (51 / 1024 : ℝ) ≤ (10510657901 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (51 / 1024 : ℝ))
    (a := (105106579 / 100000000 : ℝ)) (b := (10510657901 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_221 :
    (264107 / 500000 : ℝ) ≤ Real.exp (-(797817 / 1250000 : ℝ)) ∧
    Real.exp (-(797817 / 1250000 : ℝ)) ≤ (5282141 / 10000000 : ℝ) := by
  have hsmall : (1992472 / 1953125 : ℝ) ≤ Real.exp (797817 / 40000000 : ℝ) ∧
      Real.exp (797817 / 40000000 : ℝ) ≤ (10201456641 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (797817 / 40000000 : ℝ))
    (a := (1992472 / 1953125 : ℝ)) (b := (10201456641 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_222 :
    (1077379 / 2000000 : ℝ) ≤ Real.exp (-(6186159 / 10000000 : ℝ)) ∧
    Real.exp (-(6186159 / 10000000 : ℝ)) ≤ (336681 / 625000 : ℝ) := by
  have hsmall : (203903963 / 200000000 : ℝ) ≤ Real.exp (6186159 / 320000000 : ℝ) ∧
      Real.exp (6186159 / 320000000 : ℝ) ≤ (10195198151 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (6186159 / 320000000 : ℝ))
    (a := (203903963 / 200000000 : ℝ)) (b := (10195198151 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_223 :
    (4956247 / 5000000 : ℝ) ≤ Real.exp (-(9 / 1024 : ℝ)) ∧
    Real.exp (-(9 / 1024 : ℝ)) ≤ (1982499 / 2000000 : ℝ) := by
  have hsmall : (10002746959 / 10000000000 : ℝ) ≤ Real.exp (9 / 32768 : ℝ) ∧
      Real.exp (9 / 32768 : ℝ) ≤ (125034337 / 125000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (9 / 32768 : ℝ))
    (a := (10002746959 / 10000000000 : ℝ)) (b := (125034337 / 125000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_224 :
    (1189269 / 1250000 : ℝ) ≤ Real.exp (-(51 / 1024 : ℝ)) ∧
    Real.exp (-(51 / 1024 : ℝ)) ≤ (9514153 / 10000000 : ℝ) := by
  have hsmall : (5007788041 / 5000000000 : ℝ) ≤ Real.exp (51 / 32768 : ℝ) ∧
      Real.exp (51 / 32768 : ℝ) ≤ (10015576083 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (51 / 32768 : ℝ))
    (a := (5007788041 / 5000000000 : ℝ)) (b := (10015576083 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_225 :
    (2096113 / 10000000 : ℝ) ≤ Real.exp (-(25 / 16 : ℝ)) ∧
    Real.exp (-(25 / 16 : ℝ)) ≤ (1048057 / 5000000 : ℝ) := by
  have hsmall : (2625099649 / 2500000000 : ℝ) ≤ Real.exp (25 / 512 : ℝ) ∧
      Real.exp (25 / 512 : ℝ) ≤ (10500398597 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (25 / 512 : ℝ))
    (a := (2625099649 / 2500000000 : ℝ)) (b := (10500398597 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_226 :
    (25881 / 50000 : ℝ) ≤ Real.exp (-(3292569 / 5000000 : ℝ)) ∧
    Real.exp (-(3292569 / 5000000 : ℝ)) ≤ (5176201 / 10000000 : ℝ) := by
  have hsmall : (5103958773 / 5000000000 : ℝ) ≤ Real.exp (3292569 / 160000000 : ℝ) ∧
      Real.exp (3292569 / 160000000 : ℝ) ≤ (10207917547 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3292569 / 160000000 : ℝ))
    (a := (5103958773 / 5000000000 : ℝ)) (b := (10207917547 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_227 :
    (165067 / 312500 : ℝ) ≤ Real.exp (-(638253 / 1000000 : ℝ)) ∧
    Real.exp (-(638253 / 1000000 : ℝ)) ≤ (1056429 / 2000000 : ℝ) := by
  have hsmall : (10201456449 / 10000000000 : ℝ) ≤ Real.exp (638253 / 32000000 : ℝ) ∧
      Real.exp (638253 / 32000000 : ℝ) ≤ (204029129 / 200000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (638253 / 32000000 : ℝ))
    (a := (10201456449 / 10000000000 : ℝ)) (b := (204029129 / 200000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_228 :
    (9961013 / 10000000 : ℝ) ≤ Real.exp (-(1 / 256 : ℝ)) ∧
    Real.exp (-(1 / 256 : ℝ)) ≤ (4980507 / 5000000 : ℝ) := by
  have hsmall : (10001220777 / 10000000000 : ℝ) ≤ Real.exp (1 / 8192 : ℝ) ∧
      Real.exp (1 / 8192 : ℝ) ≤ (5000610389 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1 / 8192 : ℝ))
    (a := (10001220777 / 10000000000 : ℝ)) (b := (5000610389 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_229 :
    (483671 / 500000 : ℝ) ≤ Real.exp (-(17 / 512 : ℝ)) ∧
    Real.exp (-(17 / 512 : ℝ)) ≤ (9673421 / 10000000 : ℝ) := by
  have hsmall : (10010381361 / 10000000000 : ℝ) ≤ Real.exp (17 / 16384 : ℝ) ∧
      Real.exp (17 / 16384 : ℝ) ≤ (5005190681 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (17 / 16384 : ℝ))
    (a := (10010381361 / 10000000000 : ℝ)) (b := (5005190681 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_230 :
    (2162651 / 10000000 : ℝ) ≤ Real.exp (-(49 / 32 : ℝ)) ∧
    Real.exp (-(49 / 32 : ℝ)) ≤ (540663 / 2500000 : ℝ) := by
  have hsmall : (5245074653 / 5000000000 : ℝ) ≤ Real.exp (49 / 1024 : ℝ) ∧
      Real.exp (49 / 1024 : ℝ) ≤ (10490149307 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (49 / 1024 : ℝ))
    (a := (5245074653 / 5000000000 : ℝ)) (b := (10490149307 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_231 :
    (2534561 / 5000000 : ℝ) ≤ Real.exp (-(6794173 / 10000000 : ℝ)) ∧
    Real.exp (-(6794173 / 10000000 : ℝ)) ≤ (5069123 / 10000000 : ℝ) := by
  have hsmall : (10214587887 / 10000000000 : ℝ) ≤ Real.exp (6794173 / 320000000 : ℝ) ∧
      Real.exp (6794173 / 320000000 : ℝ) ≤ (638411743 / 625000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (6794173 / 320000000 : ℝ))
    (a := (10214587887 / 10000000000 : ℝ)) (b := (638411743 / 625000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_232 :
    (1294051 / 2500000 : ℝ) ≤ Real.exp (-(6585131 / 10000000 : ℝ)) ∧
    Real.exp (-(6585131 / 10000000 : ℝ)) ≤ (1035241 / 2000000 : ℝ) := by
  have hsmall : (10207917323 / 10000000000 : ℝ) ≤ Real.exp (6585131 / 320000000 : ℝ) ∧
      Real.exp (6585131 / 320000000 : ℝ) ≤ (2551979331 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (6585131 / 320000000 : ℝ))
    (a := (10207917323 / 10000000000 : ℝ)) (b := (2551979331 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_233 :
    (9990239 / 10000000 : ℝ) ≤ Real.exp (-(1 / 1024 : ℝ)) ∧
    Real.exp (-(1 / 1024 : ℝ)) ≤ (62439 / 62500 : ℝ) := by
  have hsmall : (500015259 / 500000000 : ℝ) ≤ Real.exp (1 / 32768 : ℝ) ∧
      Real.exp (1 / 32768 : ℝ) ≤ (10000305181 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1 / 32768 : ℝ))
    (a := (500015259 / 500000000 : ℝ)) (b := (10000305181 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_234 :
    (4917677 / 5000000 : ℝ) ≤ Real.exp (-(17 / 1024 : ℝ)) ∧
    Real.exp (-(17 / 1024 : ℝ)) ≤ (1967071 / 2000000 : ℝ) := by
  have hsmall : (5002594667 / 5000000000 : ℝ) ≤ Real.exp (17 / 32768 : ℝ) ∧
      Real.exp (17 / 32768 : ℝ) ≤ (2001037867 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (17 / 32768 : ℝ))
    (a := (5002594667 / 5000000000 : ℝ)) (b := (2001037867 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_235 :
    (2231301 / 10000000 : ℝ) ≤ Real.exp (-(3 / 2 : ℝ)) ∧
    Real.exp (-(3 / 2 : ℝ)) ≤ (1115651 / 5000000 : ℝ) := by
  have hsmall : (523995501 / 500000000 : ℝ) ≤ Real.exp (3 / 64 : ℝ) ∧
      Real.exp (3 / 64 : ℝ) ≤ (10479910021 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3 / 64 : ℝ))
    (a := (523995501 / 500000000 : ℝ)) (b := (10479910021 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_236 :
    (4960967 / 10000000 : ℝ) ≤ Real.exp (-(7009843 / 10000000 : ℝ)) ∧
    Real.exp (-(7009843 / 10000000 : ℝ)) ≤ (620121 / 1250000 : ℝ) := by
  have hsmall : (10221474521 / 10000000000 : ℝ) ≤ Real.exp (7009843 / 320000000 : ℝ) ∧
      Real.exp (7009843 / 320000000 : ℝ) ≤ (5110737261 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7009843 / 320000000 : ℝ))
    (a := (10221474521 / 10000000000 : ℝ)) (b := (5110737261 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_237 :
    (40553 / 80000 : ℝ) ≤ Real.exp (-(6794167 / 10000000 : ℝ)) ∧
    Real.exp (-(6794167 / 10000000 : ℝ)) ≤ (2534563 / 5000000 : ℝ) := by
  have hsmall : (638411731 / 625000000 : ℝ) ≤ Real.exp (6794167 / 320000000 : ℝ) ∧
      Real.exp (6794167 / 320000000 : ℝ) ≤ (10214587697 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (6794167 / 320000000 : ℝ))
    (a := (638411731 / 625000000 : ℝ)) (b := (10214587697 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_238 :
    (1 / 1 : ℝ) ≤ Real.exp (0 / 1 : ℝ) ∧
    Real.exp (0 / 1 : ℝ) ≤ (1 / 1 : ℝ) := by
  have hsmall : (1 / 1 : ℝ) ≤ Real.exp (0 / 1 : ℝ) ∧
      Real.exp (0 / 1 : ℝ) ≤ (1 / 1 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (0 / 1 : ℝ))
    (a := (1 / 1 : ℝ)) (b := (1 / 1 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)
end MasulloRH.CertifiedExp
end

/- Source: Solutions.ThetaPolynomialCertificateCore -/
section
set_option autoImplicit false

namespace MasulloRH.CertifiedExp

theorem nonneg_product_enclosure {x y a b c d : ℝ}
    (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    a * c ≤ x * y ∧ x * y ≤ b * d :=
  ⟨mul_le_mul hx.1 hy.1 hc (ha.trans hx.1),
    mul_le_mul hx.2 hy.2 (hc.trans hy.1) (ha.trans (hx.1.trans hx.2))⟩

/-- The left factor is nonnegative; the right factor may straddle zero.
The four extra inequalities are finite rational arithmetic in applications. -/
theorem nonneg_left_product_enclosure {x y a b c d L U : ℝ}
    (ha : 0 ≤ a) (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d)
    (hL₁ : L ≤ a * c) (hL₂ : L ≤ b * c)
    (hU₁ : a * d ≤ U) (hU₂ : b * d ≤ U) :
    L ≤ x * y ∧ x * y ≤ U := by
  have hx0 := ha.trans hx.1
  have hlo : L ≤ x * c := by
    rcases le_total 0 c with hc | hc
    · exact hL₁.trans (mul_le_mul_of_nonneg_right hx.1 hc)
    · exact hL₂.trans (mul_le_mul_of_nonpos_right hx.2 hc)
  have hhi : x * d ≤ U := by
    rcases le_total 0 d with hd | hd
    · exact (mul_le_mul_of_nonneg_right hx.2 hd).trans hU₂
    · exact (mul_le_mul_of_nonpos_right hx.1 hd).trans hU₁
  exact ⟨hlo.trans (mul_le_mul_of_nonneg_left hy.1 hx0),
    (mul_le_mul_of_nonneg_left hy.2 hx0).trans hhi⟩

theorem thetaPolynomial_six_eq (r : ℝ) :
    thetaPolynomial 6 r = r - 2 * r ^ 4 + r ^ 9 + r ^ 25 - 2 * r ^ 36 -
      r ^ 64 - 3 * r ^ 100 - r ^ 144 + 2 * r ^ 256 + 2 * r ^ 400 + 2 * r ^ 576 := by
  norm_num [thetaPolynomial, Finset.sum_range_succ]
  ring

/-- A compact enclosure using exact cancellation in the six-term dyadic sum.
Only powers up to 64 appear in the certificate's rational arithmetic. -/
theorem thetaPolynomial_six_enclosure {r lo hi : ℝ}
    (hlo : 0 ≤ lo) (hhi : hi ≤ 1) (hr : lo ≤ r ∧ r ≤ hi) :
    lo - 2 * hi ^ 4 + lo ^ 9 + lo ^ 25 - 2 * hi ^ 36 - 5 * hi ^ 64 ≤
      thetaPolynomial 6 r ∧
    thetaPolynomial 6 r ≤
      hi - 2 * lo ^ 4 + hi ^ 9 + hi ^ 25 - 2 * lo ^ 36 + 6 * hi ^ 64 := by
  have hr0 := hlo.trans hr.1
  have hhi0 := hr0.trans hr.2
  have hpow (n : ℕ) (hn : 64 ≤ n) : 0 ≤ r ^ n ∧ r ^ n ≤ hi ^ 64 := by
    exact ⟨pow_nonneg hr0 n,
      (pow_le_pow_left₀ hr0 hr.2 n).trans (pow_le_pow_of_le_one hhi0 hhi hn)⟩
  have h64 := hpow 64 (by decide)
  have h100 := hpow 100 (by decide)
  have h144 := hpow 144 (by decide)
  have h256 := hpow 256 (by decide)
  have h400 := hpow 400 (by decide)
  have h576 := hpow 576 (by decide)
  have hl4 := pow_le_pow_left₀ hlo hr.1 4
  have hu4 := pow_le_pow_left₀ hr0 hr.2 4
  have hl9 := pow_le_pow_left₀ hlo hr.1 9
  have hu9 := pow_le_pow_left₀ hr0 hr.2 9
  have hl25 := pow_le_pow_left₀ hlo hr.1 25
  have hu25 := pow_le_pow_left₀ hr0 hr.2 25
  have hl36 := pow_le_pow_left₀ hlo hr.1 36
  have hu36 := pow_le_pow_left₀ hr0 hr.2 36
  rw [thetaPolynomial_six_eq]
  constructor <;> linarith

theorem thetaPolynomial_six_enclosure_of_bounds {r lo hi L U : ℝ}
    (hlo : 0 ≤ lo) (hhi : hi ≤ 1) (hr : lo ≤ r ∧ r ≤ hi)
    (hL : L ≤ lo - 2 * hi ^ 4 + lo ^ 9 + lo ^ 25 - 2 * hi ^ 36 - 5 * hi ^ 64)
    (hU : hi - 2 * lo ^ 4 + hi ^ 9 + hi ^ 25 - 2 * lo ^ 36 + 6 * hi ^ 64 ≤ U) :
    L ≤ thetaPolynomial 6 r ∧ thetaPolynomial 6 r ≤ U := by
  have h := thetaPolynomial_six_enclosure hlo hhi hr
  exact ⟨hL.trans h.1, h.2.trans hU⟩


end MasulloRH.CertifiedExp
end


section
set_option maxHeartbeats 4000000
open MasulloRH.GaussianApproximation MasulloRH.CertifiedExp
namespace MasulloRH.HeightOne
theorem cell_026 (x : ℝ) (hx : x ∈ Set.Ioo (-1 / 4 : ℝ) (-15 / 64 : ℝ)) :
    density x ≤ (546899 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (169169 / 1250000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (1396313 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_159.1 n1_exp_160.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (169169 / 1250000 : ℝ)) pi_rational_enclosure hi
  have ha : (4251679 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (548331 / 1250000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (6448969 / 10000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (6536601 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_161.1 n1_exp_162.2
  have hpoly : (29908537 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (32953721 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (6448969 / 10000000 : ℝ))
      (by norm_num : (6536601 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (29908537 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (32953721 / 50000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-15 / 64 : ℝ))
    (show -(-15 / 64 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-1 / 4 : ℝ) by linarith only [hx.1]) 2
  have hpe : (7788007 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (8027383 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_157.1 n1_exp_163.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (7788007 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (17575647 / 20000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (18115877 / 20000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (3897809 / 5000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_164.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (17575647 / 20000000 : ℝ) (18115877 / 20000000 : ℝ) (29908537 / 50000000 : ℝ) (32953721 / 50000000 : ℝ)
    (8346631 / 100000000 : ℝ) (3897809 / 5000000 : ℝ) (546899 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_027 (x : ℝ) (hx : x ∈ Set.Ioo (-15 / 64 : ℝ) (-7 / 32 : ℝ)) :
    density x ≤ (244771 / 50000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (174539 / 1250000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (1440637 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_160.1 n1_exp_165.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (174539 / 1250000 : ℝ)) pi_rational_enclosure hi
  have ha : (2193321 / 5000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (565737 / 1250000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (635979 / 1000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (6448973 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_166.1 n1_exp_167.2
  have hpoly : (959621 / 3125000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (33701727 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (635979 / 1000000 : ℝ))
      (by norm_num : (6448973 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (959621 / 1562500 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (33701727 / 50000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-7 / 32 : ℝ))
    (show -(-7 / 32 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-15 / 64 : ℝ) by linarith only [hx.1]) 2
  have hpe : (4013691 / 5000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (8257971 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_163.1 n1_exp_168.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (4013691 / 5000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (22644823 / 25000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (46590647 / 50000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (7926117 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_169.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (22644823 / 25000000 : ℝ) (46590647 / 50000000 : ℝ) (959621 / 1562500 : ℝ) (33701727 / 50000000 : ℝ)
    (7829751 / 100000000 : ℝ) (7926117 / 10000000 : ℝ) (244771 / 50000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_028 (x : ℝ) (hx : x ∈ Set.Ioo (-7 / 32 : ℝ) (-13 / 64 : ℝ)) :
    density x ≤ (432233 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (360159 / 2500000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (46449 / 312500 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_165.1 n1_exp_170.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (360159 / 2500000 : ℝ)) pi_rational_enclosure hi
  have ha : (452589 / 1000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (1167391 / 2500000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (3134537 / 5000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (1271959 / 2000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_171.1 n1_exp_172.2
  have hpoly : (15734021 / 50000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (6881889 / 20000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (3134537 / 5000000 : ℝ))
      (by norm_num : (1271959 / 2000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (15734021 / 25000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (6881889 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-13 / 64 : ℝ))
    (show -(-13 / 64 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-7 / 32 : ℝ) by linarith only [hx.1]) 2
  have hpe : (825797 / 1000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (4239303 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_168.1 n1_exp_173.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (825797 / 1000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (93181199 / 100000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (19134179 / 20000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (8058801 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_174.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (93181199 / 100000000 : ℝ) (19134179 / 20000000 : ℝ) (15734021 / 25000000 : ℝ) (6881889 / 10000000 : ℝ)
    (7294381 / 100000000 : ℝ) (8058801 / 10000000 : ℝ) (432233 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_029 (x : ℝ) (hx : x ∈ Set.Ioo (-13 / 64 : ℝ) (-3 / 16 : ℝ)) :
    density x ≤ (375979 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (1486367 / 10000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (30671 / 200000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_170.1 n1_exp_175.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1486367 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (2334779 / 5000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (481779 / 1000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (1235367 / 2000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (3134539 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_176.1 n1_exp_177.2
  have hpoly : (6437177 / 20000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (7014763 / 20000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (1235367 / 2000000 : ℝ))
      (by norm_num : (3134539 / 5000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (6437177 / 10000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (7014763 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-3 / 16 : ℝ))
    (show -(-3 / 16 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-13 / 64 : ℝ) by linarith only [hx.1]) 2
  have hpe : (1695721 / 2000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (8688151 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_173.1 n1_exp_178.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1695721 / 2000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (47835399 / 50000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (98035359 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (8193707 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_179.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (47835399 / 50000000 : ℝ) (98035359 / 100000000 : ℝ) (6437177 / 10000000 : ℝ) (7014763 / 10000000 : ℝ)
    (3372371 / 50000000 : ℝ) (8193707 / 10000000 : ℝ) (375979 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_030 (x : ℝ) (hx : x ∈ Set.Ioo (-3 / 16 : ℝ) (-11 / 64 : ℝ)) :
    density x ≤ (321731 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (1533549 / 10000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (158223 / 1000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_175.1 n1_exp_180.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1533549 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (963557 / 2000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (4970723 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (608309 / 1000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (6176839 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_181.1 n1_exp_182.2
  have hpoly : (8214577 / 25000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (8922987 / 25000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (608309 / 1000000 : ℝ))
      (by norm_num : (6176839 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (8214577 / 12500000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (8922987 / 12500000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-11 / 64 : ℝ))
    (show -(-11 / 64 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-3 / 16 : ℝ) by linarith only [hx.1]) 2
  have hpe : (173763 / 200000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (8885503 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_178.1 n1_exp_183.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (173763 / 200000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (4901763 / 5000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (100262239 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (8330871 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_184.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (4901763 / 5000000 : ℝ) (100262239 / 100000000 : ℝ) (8214577 / 12500000 : ℝ) (8922987 / 12500000 : ℝ)
    (6185229 / 100000000 : ℝ) (8330871 / 10000000 : ℝ) (321731 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_031 (x : ℝ) (hx : x ∈ Set.Ioo (-11 / 64 : ℝ) (-5 / 32 : ℝ)) :
    density x ≤ (13517 / 5000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (1582229 / 10000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (204057 / 1250000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_180.1 n1_exp_185.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1582229 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (4970717 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (5128513 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (2993929 / 5000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (3041547 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_186.1 n1_exp_187.2
  have hpoly : (33482441 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (9065271 / 25000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (2993929 / 5000000 : ℝ))
      (by norm_num : (3041547 / 5000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (33482441 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (9065271 / 12500000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-5 / 32 : ℝ))
    (show -(-5 / 32 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-11 / 64 : ℝ) by linarith only [hx.1]) 2
  have hpe : (4442751 / 5000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (9069607 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_183.1 n1_exp_188.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (4442751 / 5000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (50131069 / 50000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (6396227 / 6250000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (8470331 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_189.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (50131069 / 50000000 : ℝ) (6396227 / 6250000 : ℝ) (33482441 / 50000000 : ℝ) (9065271 / 12500000 : ℝ)
    (1405057 / 25000000 : ℝ) (8470331 / 10000000 : ℝ) (13517 / 5000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_032 (x : ℝ) (hx : x ∈ Set.Ioo (-5 / 32 : ℝ) (-9 / 64 : ℝ)) :
    density x ≤ (55627 / 25000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (326491 / 2000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (67371 / 400000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_185.1 n1_exp_190.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (326491 / 2000000 : ℝ)) pi_rational_enclosure hi
  have ha : (5128507 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (5291307 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (184099 / 312500 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (2993931 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_191.1 n1_exp_192.2
  have hpoly : (2128479 / 6250000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (9194631 / 25000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (184099 / 312500 : ℝ))
      (by norm_num : (2993931 / 5000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (2128479 / 3125000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (9194631 / 12500000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-9 / 64 : ℝ))
    (show -(-9 / 64 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-5 / 32 : ℝ) by linarith only [hx.1]) 2
  have hpe : (4534803 / 5000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (9239461 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_188.1 n1_exp_193.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (4534803 / 5000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (102339529 / 100000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (104256231 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (68897 / 80000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_194.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (102339529 / 100000000 : ℝ) (104256231 / 100000000 : ℝ) (2128479 / 3125000 : ℝ) (9194631 / 12500000 : ℝ)
    (2526881 / 50000000 : ℝ) (68897 / 80000 : ℝ) (55627 / 25000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_033 (x : ℝ) (hx : x ∈ Set.Ioo (-9 / 64 : ℝ) (-1 / 8 : ℝ)) :
    density x ≤ (112573 / 50000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (842137 / 5000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (86887 / 500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_190.1 n1_exp_195.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (842137 / 5000000 : ℝ)) pi_rational_enclosure hi
  have ha : (5291301 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (682409 / 1250000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (1448261 / 2500000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (5891173 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_196.1 n1_exp_197.2
  have hpoly : (34575327 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (37242003 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (1448261 / 2500000 : ℝ))
      (by norm_num : (5891173 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (34575327 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (37242003 / 50000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-1 / 8 : ℝ))
    (show -(-1 / 8 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-9 / 64 : ℝ) by linarith only [hx.1]) 2
  have hpe : (461973 / 500000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (9394131 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_193.1 n1_exp_198.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (461973 / 500000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (52128063 / 50000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (13250187 / 12500000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (8756293 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_199.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (52128063 / 50000000 : ℝ) (13250187 / 12500000 : ℝ) (34575327 / 50000000 : ℝ) (37242003 / 50000000 : ℝ)
    (2520771 / 50000000 : ℝ) (8756293 / 10000000 : ℝ) (112573 / 50000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_034 (x : ℝ) (hx : x ∈ Set.Ioo (-1 / 8 : ℝ) (-7 / 64 : ℝ)) :
    density x ≤ (9929 / 4000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (1737739 / 10000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (896451 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_195.1 n1_exp_200.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1737739 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (2729633 / 5000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (5632569 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (5693517 / 10000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (724131 / 1250000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_201.1 n1_exp_202.2
  have hpoly : (17519623 / 50000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (37649273 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (5693517 / 10000000 : ℝ))
      (by norm_num : (724131 / 1250000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (17519623 / 25000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (37649273 / 50000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-7 / 64 : ℝ))
    (show -(-7 / 64 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-1 / 8 : ℝ) by linarith only [hx.1]) 2
  have hpe : (939413 / 1000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (9532753 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_198.1 n1_exp_203.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (939413 / 1000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (10600139 / 10000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (107565679 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (71223 / 80000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_204.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (10600139 / 10000000 : ℝ) (107565679 / 100000000 : ℝ) (17519623 / 25000000 : ℝ) (37649273 / 50000000 : ℝ)
    (5251081 / 100000000 : ℝ) (71223 / 80000 : ℝ) (9929 / 4000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_035 (x : ℝ) (hx : x ∈ Set.Ioo (-7 / 64 : ℝ) (-3 / 32 : ℝ)) :
    density x ≤ (270723 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (1792901 / 10000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (369963 / 2000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_200.1 n1_exp_205.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1792901 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (5632563 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (2905683 / 5000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (5592623 / 10000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (5693521 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_206.1 n1_exp_207.2
  have hpoly : (35445331 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (3799841 / 10000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (5592623 / 10000000 : ℝ))
      (by norm_num : (5693521 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (35445331 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (3799841 / 5000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-3 / 32 : ℝ))
    (show -(-3 / 32 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-7 / 64 : ℝ) by linarith only [hx.1]) 2
  have hpe : (595797 / 625000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (4827273 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_203.1 n1_exp_208.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (595797 / 625000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (107565571 / 100000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (108939967 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (905191 / 1000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_209.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (107565571 / 100000000 : ℝ) (108939967 / 100000000 : ℝ) (35445331 / 50000000 : ℝ) (3799841 / 5000000 : ℝ)
    (5439601 / 100000000 : ℝ) (905191 / 1000000 : ℝ) (270723 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_036 (x : ℝ) (hx : x ∈ Set.Ioo (-3 / 32 : ℝ) (-5 / 64 : ℝ)) :
    density x ≤ (292119 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (1849813 / 10000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (954267 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_205.1 n1_exp_210.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1849813 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (5811357 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (2997919 / 5000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (6863 / 12500 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (5592629 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_211.1 n1_exp_212.2
  have hpoly : (279623 / 781250 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (19143883 / 50000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (6863 / 12500 : ℝ))
      (by norm_num : (5592629 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (279623 / 390625 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (19143883 / 25000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-5 / 64 : ℝ))
    (show -(-5 / 64 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-3 / 32 : ℝ) by linarith only [hx.1]) 2
  have hpe : (1930909 / 2000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (304963 / 312500 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_208.1 n1_exp_213.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1930909 / 2000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (54469929 / 50000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (6882283 / 6250000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (115043 / 125000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_214.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (54469929 / 50000000 : ℝ) (6882283 / 6250000 : ℝ) (279623 / 390625 : ℝ) (19143883 / 25000000 : ℝ)
    (1401159 / 25000000 : ℝ) (115043 / 125000 : ℝ) (292119 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_037 (x : ℝ) (hx : x ∈ Set.Ioo (-5 / 64 : ℝ) (-1 / 16 : ℝ)) :
    density x ≤ (311849 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (1908533 / 10000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (1969117 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_210.1 n1_exp_215.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1908533 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (749479 / 1250000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (1237233 / 2000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (5386891 / 10000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (1098081 / 2000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_216.1 n1_exp_217.2
  have hpoly : (36077037 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (38515861 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (5386891 / 10000000 : ℝ))
      (by norm_num : (1098081 / 2000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (36077037 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (38515861 / 50000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-1 / 16 : ℝ))
    (show -(-1 / 16 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-5 / 64 : ℝ) by linarith only [hx.1]) 2
  have hpe : (1951763 / 2000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (1968993 / 2000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_213.1 n1_exp_218.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1951763 / 2000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (110116419 / 100000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (111088617 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (9357507 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_219.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (110116419 / 100000000 : ℝ) (111088617 / 100000000 : ℝ) (36077037 / 50000000 : ℝ) (38515861 / 50000000 : ℝ)
    (5743669 / 100000000 : ℝ) (9357507 / 10000000 : ℝ) (311849 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_038 (x : ℝ) (hx : x ∈ Set.Ioo (-1 / 16 : ℝ) (-3 / 64 : ℝ)) :
    density x ≤ (164707 / 50000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (492279 / 2500000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (253953 / 1250000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_215.1 n1_exp_220.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (492279 / 2500000 : ℝ)) pi_rational_enclosure hi
  have ha : (6186159 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (797817 / 1250000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (264107 / 500000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (336681 / 625000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_221.1 n1_exp_222.2
  have hpoly : (290399 / 800000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (19340823 / 50000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (264107 / 500000 : ℝ))
      (by norm_num : (336681 / 625000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (290399 / 400000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (19340823 / 25000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-3 / 64 : ℝ))
    (show -(-3 / 64 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-1 / 16 : ℝ) by linarith only [hx.1]) 2
  have hpe : (2461241 / 2500000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (1982499 / 2000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_218.1 n1_exp_223.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (2461241 / 2500000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (55544253 / 50000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (27962653 / 25000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (9514153 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_224.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (55544253 / 50000000 : ℝ) (27962653 / 25000000 : ℝ) (290399 / 400000 : ℝ) (19340823 / 25000000 : ℝ)
    (5854977 / 100000000 : ℝ) (9514153 / 10000000 : ℝ) (164707 / 50000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_039 (x : ℝ) (hx : x ∈ Set.Ioo (-3 / 64 : ℝ) (-1 / 32 : ℝ)) :
    density x ≤ (172149 / 50000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (2031623 / 10000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (1048057 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_220.1 n1_exp_225.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (2031623 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (638253 / 1000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (3292569 / 5000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (25881 / 50000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (1056429 / 2000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_226.1 n1_exp_227.2
  have hpoly : (11667 / 32000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (38784221 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (25881 / 50000 : ℝ))
      (by norm_num : (1056429 / 2000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (11667 / 16000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (38784221 / 50000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-1 / 32 : ℝ))
    (show -(-1 / 32 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-3 / 64 : ℝ) by linarith only [hx.1]) 2
  have hpe : (4956247 / 5000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (4980507 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_223.1 n1_exp_228.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (4956247 / 5000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (223701 / 200000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (11239809 / 10000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (9673421 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_229.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (223701 / 200000 : ℝ) (11239809 / 10000000 : ℝ) (11667 / 16000 : ℝ) (38784221 / 50000000 : ℝ)
    (1187343 / 20000000 : ℝ) (9673421 / 10000000 : ℝ) (172149 / 50000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_040 (x : ℝ) (hx : x ∈ Set.Ioo (-1 / 32 : ℝ) (-1 / 64 : ℝ)) :
    density x ≤ (356081 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (2096113 / 10000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (540663 / 2500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_225.1 n1_exp_230.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (2096113 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (6585131 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (6794173 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (2534561 / 5000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (1035241 / 2000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_231.1 n1_exp_232.2
  have hpoly : (36554823 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (38823121 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (2534561 / 5000000 : ℝ))
      (by norm_num : (1035241 / 2000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (36554823 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (38823121 / 50000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-1 / 64 : ℝ))
    (show -(-1 / 64 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-1 / 32 : ℝ) by linarith only [hx.1]) 2
  have hpe : (9961013 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (62439 / 62500 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_228.1 n1_exp_233.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (9961013 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (56198989 / 50000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (112727871 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (1967071 / 2000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_234.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (56198989 / 50000000 : ℝ) (112727871 / 100000000 : ℝ) (36554823 / 50000000 : ℝ) (38823121 / 50000000 : ℝ)
    (1496947 / 25000000 : ℝ) (1967071 / 2000000 : ℝ) (356081 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_041 (x : ℝ) (hx : x ∈ Set.Ioo (-1 / 64 : ℝ) (0 / 1 : ℝ)) :
    density x ≤ (364359 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (2162651 / 10000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (1115651 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_230.1 n1_exp_235.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (2162651 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (6794167 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (7009843 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (4960967 / 10000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (2534563 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_236.1 n1_exp_237.2
  have hpoly : (7317191 / 20000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (38798051 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (4960967 / 10000000 : ℝ))
      (by norm_num : (2534563 / 5000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (7317191 / 10000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (38798051 / 50000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(0 / 1 : ℝ))
    (show -(0 / 1 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-1 / 64 : ℝ) by linarith only [hx.1]) 2
  have hpe : (9990239 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (1 / 1 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_233.1 n1_exp_238.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (9990239 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (56363879 / 50000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (56419 / 50000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (1 / 1 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_238.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (56363879 / 50000000 : ℝ) (56419 / 50000 : ℝ) (7317191 / 10000000 : ℝ) (38798051 / 50000000 : ℝ)
    (1501753 / 25000000 : ℝ) (1 / 1 : ℝ) (364359 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)
end MasulloRH.HeightOne
end

/- Source: Solutions.ThetaEnergyPartition -/
section
set_option autoImplicit false
open MeasureTheory Set
open scoped BigOperators

namespace MasulloRH.EnergyCertificate

/-- Upper bounds on the open cells of a finite contiguous partition bound the
integral. Endpoints need no pointwise check because they have measure zero. -/
theorem integral_le_nat_partition_sum (f : ℝ → ℝ) (n : ℕ)
    (t B : ℕ → ℝ) (hI : Integrable f)
    (hstep : ∀ k < n, t k ≤ t (k+1))
    (hbound : ∀ k < n, ∀ x ∈ Ioo (t k) (t (k+1)), f x ≤ B k) :
    (∫ x : ℝ in (t 0)..(t n), f x) ≤
      ∑ k ∈ Finset.range n, B k * (t (k+1)-t k) := by
  rw [← intervalIntegral.sum_integral_adjacent_intervals
    (fun k (_hk : k < n) => hI.intervalIntegrable)]
  apply Finset.sum_le_sum
  intro k hk
  have h := intervalIntegral.integral_mono_on_of_le_Ioo
    (hstep k (Finset.mem_range.mp hk)) hI.intervalIntegrable
    intervalIntegrable_const (hbound k (Finset.mem_range.mp hk))
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h

/-- A version directly usable with a finite rational endpoint table and one
certified density bound per cell. -/
theorem integral_le_fin_partition_sum (f : ℝ → ℝ) (n : ℕ)
    (t : Fin (n+1) → ℝ) (B : Fin n → ℝ) (hI : Integrable f)
    (hstep : ∀ k : Fin n, t k.castSucc ≤ t k.succ)
    (hbound : ∀ k : Fin n, ∀ x ∈ Ioo (t k.castSucc) (t k.succ), f x ≤ B k) :
    (∫ x : ℝ in (t 0)..(t (Fin.last n)), f x) ≤
      ∑ k : Fin n, B k * (t k.succ - t k.castSucc) := by
  let tn : ℕ → ℝ := fun k => t ⟨min k n, Nat.lt_succ_of_le (Nat.min_le_right k n)⟩
  let Bn : ℕ → ℝ := fun k => if hk : k < n then B ⟨k,hk⟩ else 0
  have hs (k : ℕ) (hk : k < n) : tn k ≤ tn (k+1) := by
    dsimp only [tn]
    simp only [Nat.min_eq_left hk.le, Nat.min_eq_left (Nat.succ_le_of_lt hk)]
    exact hstep ⟨k,hk⟩
  have hb (k : ℕ) (hk : k < n) :
      ∀ x ∈ Ioo (tn k) (tn (k+1)), f x ≤ Bn k := by
    dsimp only [tn, Bn]
    simp only [Nat.min_eq_left hk.le, Nat.min_eq_left (Nat.succ_le_of_lt hk), dif_pos hk]
    exact hbound ⟨k,hk⟩
  have h := integral_le_nat_partition_sum f n tn Bn hI hs hb
  rw [Finset.sum_range] at h
  have hsum : (∑ k : Fin n, Bn k * (tn (k+1)-tn k)) =
      ∑ k : Fin n, B k * (t k.succ-t k.castSucc) := by
    apply Finset.sum_congr rfl
    intro k _hk
    dsimp only [tn, Bn]
    simp only [Nat.min_eq_left k.is_lt.le,
      Nat.min_eq_left (Nat.succ_le_of_lt k.is_lt), dif_pos k.is_lt]
    rfl
  rw [hsum] at h
  have htzero : tn 0 = t 0 := by
    dsimp only [tn]
    congr 1 <;> apply Fin.ext <;> simp
  have htlast : tn n = t (Fin.last n) := by
    dsimp only [tn]
    congr 1 <;> apply Fin.ext <;> simp
  rw [htzero, htlast] at h
  exact h

/-- Set-integral version with explicit endpoints, suitable for a certificate
whose table covers exactly [-R,R]. -/
theorem compact_integral_le_fin_partition_sum (f : ℝ → ℝ) (n : ℕ)
    (t : Fin (n+1) → ℝ) (B : Fin n → ℝ) (R : ℝ)
    (hI : Integrable f) (hR : 0 ≤ R) (hfirst : t 0 = -R)
    (hlast : t (Fin.last n) = R)
    (hstep : ∀ k : Fin n, t k.castSucc ≤ t k.succ)
    (hbound : ∀ k : Fin n, ∀ x ∈ Ioo (t k.castSucc) (t k.succ), f x ≤ B k) :
    (∫ x : ℝ in Icc (-R) R, f x) ≤
      ∑ k : Fin n, B k * (t k.succ-t k.castSucc) := by
  have h := integral_le_fin_partition_sum f n t B hI hstep hbound
  rw [hfirst, hlast, intervalIntegral.integral_of_le (show -R ≤ R by linarith),
    ← integral_Icc_eq_integral_Ioc] at h
  exact h

end MasulloRH.EnergyCertificate
end

/- Source: Solutions.ThetaDirectIntegrability -/
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
open MasulloRH.GaussianApproximation

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


end MasulloRH.DirectIntegrability
end

section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open MeasureTheory Set
open scoped BigOperators
namespace MasulloRH.HeightOne

noncomputable def endpoints : Fin 17 → ℝ :=
  ![(-1 / 4 : ℝ), (-15 / 64 : ℝ), (-7 / 32 : ℝ), (-13 / 64 : ℝ), (-3 / 16 : ℝ), (-11 / 64 : ℝ), (-5 / 32 : ℝ), (-9 / 64 : ℝ), (-1 / 8 : ℝ), (-7 / 64 : ℝ), (-3 / 32 : ℝ), (-5 / 64 : ℝ), (-1 / 16 : ℝ), (-3 / 64 : ℝ), (-1 / 32 : ℝ), (-1 / 64 : ℝ), (0 / 1 : ℝ)]

noncomputable def cellBounds : Fin 16 → ℝ :=
  ![(546899 / 100000000 : ℝ), (244771 / 50000000 : ℝ), (432233 / 100000000 : ℝ), (375979 / 100000000 : ℝ), (321731 / 100000000 : ℝ), (13517 / 5000000 : ℝ), (55627 / 25000000 : ℝ), (112573 / 50000000 : ℝ), (9929 / 4000000 : ℝ), (270723 / 100000000 : ℝ), (292119 / 100000000 : ℝ), (311849 / 100000000 : ℝ), (164707 / 50000000 : ℝ), (172149 / 50000000 : ℝ), (356081 / 100000000 : ℝ), (364359 / 100000000 : ℝ)]

theorem endpoint_first : endpoints 0 = (-1 / 4 : ℝ) := by norm_num [endpoints]
theorem endpoint_last : endpoints (Fin.last 16) = (0 : ℝ) := by norm_num [endpoints, Fin.last]

theorem endpoints_step (k : Fin 16) : endpoints k.castSucc ≤ endpoints k.succ := by
  fin_cases k
  · change (-1 / 4 : ℝ) ≤ (-15 / 64 : ℝ)
    norm_num
  · change (-15 / 64 : ℝ) ≤ (-7 / 32 : ℝ)
    norm_num
  · change (-7 / 32 : ℝ) ≤ (-13 / 64 : ℝ)
    norm_num
  · change (-13 / 64 : ℝ) ≤ (-3 / 16 : ℝ)
    norm_num
  · change (-3 / 16 : ℝ) ≤ (-11 / 64 : ℝ)
    norm_num
  · change (-11 / 64 : ℝ) ≤ (-5 / 32 : ℝ)
    norm_num
  · change (-5 / 32 : ℝ) ≤ (-9 / 64 : ℝ)
    norm_num
  · change (-9 / 64 : ℝ) ≤ (-1 / 8 : ℝ)
    norm_num
  · change (-1 / 8 : ℝ) ≤ (-7 / 64 : ℝ)
    norm_num
  · change (-7 / 64 : ℝ) ≤ (-3 / 32 : ℝ)
    norm_num
  · change (-3 / 32 : ℝ) ≤ (-5 / 64 : ℝ)
    norm_num
  · change (-5 / 64 : ℝ) ≤ (-1 / 16 : ℝ)
    norm_num
  · change (-1 / 16 : ℝ) ≤ (-3 / 64 : ℝ)
    norm_num
  · change (-3 / 64 : ℝ) ≤ (-1 / 32 : ℝ)
    norm_num
  · change (-1 / 32 : ℝ) ≤ (-1 / 64 : ℝ)
    norm_num
  · change (-1 / 64 : ℝ) ≤ (0 / 1 : ℝ)
    norm_num

 theorem cell_bound_sum_le :
    (∑ k : Fin 16, cellBounds k * (endpoints k.succ - endpoints k.castSucc)) ≤
      (7 / 8000 : ℝ) := by
  norm_num [endpoints, cellBounds, Fin.sum_univ_succ]

theorem cell_bounds (k : Fin 16) (x : ℝ)
    (hx : x ∈ Ioo (endpoints k.castSucc) (endpoints k.succ)) :
    density x ≤ cellBounds k := by
  fin_cases k
  · change density x ≤ (546899 / 100000000 : ℝ)
    change x ∈ Ioo (-1 / 4 : ℝ) (-15 / 64 : ℝ) at hx
    exact cell_026 x hx
  · change density x ≤ (244771 / 50000000 : ℝ)
    change x ∈ Ioo (-15 / 64 : ℝ) (-7 / 32 : ℝ) at hx
    exact cell_027 x hx
  · change density x ≤ (432233 / 100000000 : ℝ)
    change x ∈ Ioo (-7 / 32 : ℝ) (-13 / 64 : ℝ) at hx
    exact cell_028 x hx
  · change density x ≤ (375979 / 100000000 : ℝ)
    change x ∈ Ioo (-13 / 64 : ℝ) (-3 / 16 : ℝ) at hx
    exact cell_029 x hx
  · change density x ≤ (321731 / 100000000 : ℝ)
    change x ∈ Ioo (-3 / 16 : ℝ) (-11 / 64 : ℝ) at hx
    exact cell_030 x hx
  · change density x ≤ (13517 / 5000000 : ℝ)
    change x ∈ Ioo (-11 / 64 : ℝ) (-5 / 32 : ℝ) at hx
    exact cell_031 x hx
  · change density x ≤ (55627 / 25000000 : ℝ)
    change x ∈ Ioo (-5 / 32 : ℝ) (-9 / 64 : ℝ) at hx
    exact cell_032 x hx
  · change density x ≤ (112573 / 50000000 : ℝ)
    change x ∈ Ioo (-9 / 64 : ℝ) (-1 / 8 : ℝ) at hx
    exact cell_033 x hx
  · change density x ≤ (9929 / 4000000 : ℝ)
    change x ∈ Ioo (-1 / 8 : ℝ) (-7 / 64 : ℝ) at hx
    exact cell_034 x hx
  · change density x ≤ (270723 / 100000000 : ℝ)
    change x ∈ Ioo (-7 / 64 : ℝ) (-3 / 32 : ℝ) at hx
    exact cell_035 x hx
  · change density x ≤ (292119 / 100000000 : ℝ)
    change x ∈ Ioo (-3 / 32 : ℝ) (-5 / 64 : ℝ) at hx
    exact cell_036 x hx
  · change density x ≤ (311849 / 100000000 : ℝ)
    change x ∈ Ioo (-5 / 64 : ℝ) (-1 / 16 : ℝ) at hx
    exact cell_037 x hx
  · change density x ≤ (164707 / 50000000 : ℝ)
    change x ∈ Ioo (-1 / 16 : ℝ) (-3 / 64 : ℝ) at hx
    exact cell_038 x hx
  · change density x ≤ (172149 / 50000000 : ℝ)
    change x ∈ Ioo (-3 / 64 : ℝ) (-1 / 32 : ℝ) at hx
    exact cell_039 x hx
  · change density x ≤ (356081 / 100000000 : ℝ)
    change x ∈ Ioo (-1 / 32 : ℝ) (-1 / 64 : ℝ) at hx
    exact cell_040 x hx
  · change density x ≤ (364359 / 100000000 : ℝ)
    change x ∈ Ioo (-1 / 64 : ℝ) (0 / 1 : ℝ) at hx
    exact cell_041 x hx

theorem compact_certificate :
    IntegrableOn density (Icc (-1 / 4 : ℝ) (0 : ℝ)) ∧
      (∫ x : ℝ in Icc (-1 / 4 : ℝ) (0 : ℝ), density x) ≤ (7 / 8000 : ℝ) := by
  have hI : Integrable density :=
    MasulloRH.DirectIntegrability.height_one_density_integrable
  refine ⟨hI.integrableOn, ?_⟩
  have h := MasulloRH.EnergyCertificate.integral_le_fin_partition_sum
    density 16 endpoints cellBounds hI endpoints_step cell_bounds
  rw [endpoint_first, endpoint_last,
    intervalIntegral.integral_of_le (show (-1 / 4 : ℝ) ≤ (0 : ℝ) by norm_num),
    ← integral_Icc_eq_integral_Ioc] at h
  exact h.trans cell_bound_sum_le

end MasulloRH.HeightOne
end

end N1LeftInnerProof

open MeasureTheory MasulloRH.GaussianApproximation

theorem solution :
    IntegrableOn (fun x : ℝ =>
      Real.exp (2*(3/4)*x + 2*(7/32)*|x|) *
        ‖residual 1 (fun _ : Fin 1 => (73/50 : ℂ))
          (fun _ : Fin 1 => (3/4 : ℝ)) x‖^2) (Set.Icc (-1 / 4 : ℝ) (0 : ℝ)) ∧
    (∫ x : ℝ in Set.Icc (-1 / 4 : ℝ) (0 : ℝ),
      Real.exp (2*(3/4)*x + 2*(7/32)*|x|) *
        ‖residual 1 (fun _ : Fin 1 => (73/50 : ℂ))
          (fun _ : Fin 1 => (3/4 : ℝ)) x‖^2) ≤ (7 / 8000 : ℝ) := by
  have hF : (fun x : ℝ =>
      Real.exp (2*(3/4)*x + 2*(7/32)*|x|) *
        ‖residual 1 (fun _ : Fin 1 => (73/50 : ℂ))
          (fun _ : Fin 1 => (3/4 : ℝ)) x‖^2) =
      N1LeftInnerProof.MasulloRH.HeightOne.density := by
    funext x
    simp only [N1LeftInnerProof.MasulloRH.HeightOne.density,
      MasulloRH.GaussianApproximation.residual, Fin.sum_univ_one,
      show (2 : ℝ)*(3/4)=3/2 by norm_num,
      show (2 : ℝ)*(7/32)=7/16 by norm_num]
  rw [hF]
  exact N1LeftInnerProof.MasulloRH.HeightOne.compact_certificate

#print axioms solution
