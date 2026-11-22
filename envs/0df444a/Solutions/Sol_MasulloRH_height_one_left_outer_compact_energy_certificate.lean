-- Prove2me | solution 1 for MasulloRH.height_one_left_outer_compact_energy_certificate
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T17:45:32.922827+00:00
-- url     : https://prove2.me/submissions/f4e91e95-5985-4330-84b5-1ffdb2926a2d

/- Actual height-one density on [-4,-1/4]. -/
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
namespace N1LeftOuterProof

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
theorem n1_exp_000 :
    (1570953301 / 5000000 : ℝ) ≤ Real.exp (23 / 4 : ℝ) ∧
    Real.exp (23 / 4 : ℝ) ≤ (3141906603 / 10000000 : ℝ) := by
  have hsmall : (59842164557381 / 50000000000000 : ℝ) ≤ Real.exp (23 / 128 : ℝ) ∧
      Real.exp (23 / 128 : ℝ) ≤ (119684329114763 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (23 / 128 : ℝ))
    (a := (59842164557381 / 50000000000000 : ℝ)) (b := (119684329114763 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_001 :
    (16699658537 / 1250000 : ℝ) ≤ Real.exp (19 / 2 : ℝ) ∧
    Real.exp (19 / 2 : ℝ) ≤ (133597268297 / 10000000 : ℝ) := by
  have hsmall : (134564708304941 / 100000000000000 : ℝ) ≤ Real.exp (19 / 64 : ℝ) ∧
      Real.exp (19 / 64 : ℝ) ≤ (67282354152471 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (19 / 64 : ℝ))
    (a := (134564708304941 / 100000000000000 : ℝ)) (b := (67282354152471 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_002 :
    (0 : ℝ) ≤ Real.exp (-(13115882591 / 5000000 : ℝ)) ∧
    Real.exp (-(13115882591 / 5000000 : ℝ)) ≤ (1 / 1048576 : ℝ) :=
  neg_enclosure_of_twenty_le (by norm_num)

theorem n1_exp_003 :
    (0 : ℝ) ≤ Real.exp (-(61691179 / 1000000 : ℝ)) ∧
    Real.exp (-(61691179 / 1000000 : ℝ)) ≤ (1 / 1048576 : ℝ) :=
  neg_enclosure_of_twenty_le (by norm_num)

theorem n1_exp_004 :
    (177254241 / 10000000 : ℝ) ≤ Real.exp (23 / 8 : ℝ) ∧
    Real.exp (23 / 8 : ℝ) ≤ (88627121 / 5000000 : ℝ) := by
  have hsmall : (10940033323293 / 10000000000000 : ℝ) ≤ Real.exp (23 / 256 : ℝ) ∧
      Real.exp (23 / 256 : ℝ) ≤ (109400333232931 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (23 / 256 : ℝ))
    (a := (10940033323293 / 10000000000000 : ℝ)) (b := (109400333232931 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_005 :
    (231168569 / 2000000 : ℝ) ≤ Real.exp (19 / 4 : ℝ) ∧
    Real.exp (19 / 4 : ℝ) ≤ (577921423 / 5000000 : ℝ) := by
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

theorem n1_exp_006 :
    (0 : ℝ) ≤ Real.exp (-(64 / 1 : ℝ)) ∧
    Real.exp (-(64 / 1 : ℝ)) ≤ (1 / 1048576 : ℝ) :=
  neg_enclosure_of_twenty_le (by norm_num)

theorem n1_exp_007 :
    (0 / 1 : ℝ) ≤ Real.exp (-(289 / 16 : ℝ)) ∧
    Real.exp (-(289 / 16 : ℝ)) ≤ (1 / 10000000 : ℝ) := by
  have hsmall : (8792429229 / 5000000000 : ℝ) ≤ Real.exp (289 / 512 : ℝ) ∧
      Real.exp (289 / 512 : ℝ) ≤ (17584858479 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (289 / 512 : ℝ))
    (a := (8792429229 / 5000000000 : ℝ)) (b := (17584858479 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_008 :
    (104579 / 1000000 : ℝ) ≤ Real.exp (-(289 / 128 : ℝ)) ∧
    Real.exp (-(289 / 128 : ℝ)) ≤ (1045791 / 10000000 : ℝ) := by
  have hsmall : (1073105349 / 1000000000 : ℝ) ≤ Real.exp (289 / 4096 : ℝ) ∧
      Real.exp (289 / 4096 : ℝ) ≤ (10731053491 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (289 / 4096 : ℝ))
    (a := (1073105349 / 1000000000 : ℝ)) (b := (10731053491 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_009 :
    (240913491 / 5000000 : ℝ) ≤ Real.exp (31 / 8 : ℝ) ∧
    Real.exp (31 / 8 : ℝ) ≤ (481826983 / 10000000 : ℝ) := by
  have hsmall : (112873072591281 / 100000000000000 : ℝ) ≤ Real.exp (31 / 256 : ℝ) ∧
      Real.exp (31 / 256 : ℝ) ≤ (56436536295641 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (31 / 256 : ℝ))
    (a := (112873072591281 / 100000000000000 : ℝ)) (b := (56436536295641 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_010 :
    (0 : ℝ) ≤ Real.exp (-(616911987 / 10000000 : ℝ)) ∧
    Real.exp (-(616911987 / 10000000 : ℝ)) ≤ (1 / 1048576 : ℝ) :=
  neg_enclosure_of_twenty_le (by norm_num)

theorem n1_exp_011 :
    (389 / 5000000 : ℝ) ≤ Real.exp (-(94606487 / 10000000 : ℝ)) ∧
    Real.exp (-(94606487 / 10000000 : ℝ)) ≤ (779 / 10000000 : ℝ) := by
  have hsmall : (33599833 / 25000000 : ℝ) ≤ Real.exp (94606487 / 320000000 : ℝ) ∧
      Real.exp (94606487 / 320000000 : ℝ) ≤ (13439933201 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (94606487 / 320000000 : ℝ))
    (a := (33599833 / 25000000 : ℝ)) (b := (13439933201 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_012 :
    (34706879 / 5000000 : ℝ) ≤ Real.exp (31 / 16 : ℝ) ∧
    Real.exp (31 / 16 : ℝ) ≤ (69413759 / 10000000 : ℝ) := by
  have hsmall : (106241739721863 / 100000000000000 : ℝ) ≤ Real.exp (31 / 512 : ℝ) ∧
      Real.exp (31 / 512 : ℝ) ≤ (13280217465233 / 12500000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (31 / 512 : ℝ))
    (a := (106241739721863 / 100000000000000 : ℝ)) (b := (13280217465233 / 12500000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_013 :
    (17753 / 5000000 : ℝ) ≤ Real.exp (-(361 / 64 : ℝ)) ∧
    Real.exp (-(361 / 64 : ℝ)) ≤ (35507 / 10000000 : ℝ) := by
  have hsmall : (2981898753 / 2500000000 : ℝ) ≤ Real.exp (361 / 2048 : ℝ) ∧
      Real.exp (361 / 2048 : ℝ) ≤ (11927595013 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (361 / 2048 : ℝ))
    (a := (2981898753 / 2500000000 : ℝ)) (b := (11927595013 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_014 :
    (2831669 / 10000000 : ℝ) ≤ Real.exp (-(323 / 256 : ℝ)) ∧
    Real.exp (-(323 / 256 : ℝ)) ≤ (283167 / 1000000 : ℝ) := by
  have hsmall : (10402163401 / 10000000000 : ℝ) ≤ Real.exp (323 / 8192 : ℝ) ∧
      Real.exp (323 / 8192 : ℝ) ≤ (5201081701 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (323 / 8192 : ℝ))
    (a := (10402163401 / 10000000000 : ℝ)) (b := (5201081701 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_015 :
    (301519621 / 10000000 : ℝ) ≤ Real.exp (109 / 32 : ℝ) ∧
    Real.exp (109 / 32 : ℝ) ≤ (150759811 / 5000000 : ℝ) := by
  have hsmall : (2780792737353 / 2500000000000 : ℝ) ≤ Real.exp (109 / 1024 : ℝ) ∧
      Real.exp (109 / 1024 : ℝ) ≤ (111231709494121 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (109 / 1024 : ℝ))
    (a := (2780792737353 / 2500000000000 : ℝ)) (b := (111231709494121 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_016 :
    (389 / 5000000 : ℝ) ≤ Real.exp (-(47303259 / 5000000 : ℝ)) ∧
    Real.exp (-(47303259 / 5000000 : ℝ)) ≤ (779 / 10000000 : ℝ) := by
  have hsmall : (6719967251 / 5000000000 : ℝ) ≤ Real.exp (47303259 / 160000000 : ℝ) ∧
      Real.exp (47303259 / 160000000 : ℝ) ≤ (13439934503 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (47303259 / 160000000 : ℝ))
    (a := (6719967251 / 5000000000 : ℝ)) (b := (13439934503 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_017 :
    (26843 / 10000000 : ℝ) ≤ Real.exp (-(29601613 / 5000000 : ℝ)) ∧
    Real.exp (-(29601613 / 5000000 : ℝ)) ≤ (6711 / 2500000 : ℝ) := by
  have hsmall : (12032305701 / 10000000000 : ℝ) ≤ Real.exp (29601613 / 160000000 : ℝ) ∧
      Real.exp (29601613 / 160000000 : ℝ) ≤ (6016152851 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (29601613 / 160000000 : ℝ))
    (a := (12032305701 / 10000000000 : ℝ)) (b := (6016152851 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_018 :
    (27455401 / 5000000 : ℝ) ≤ Real.exp (109 / 64 : ℝ) ∧
    Real.exp (109 / 64 : ℝ) ≤ (54910803 / 10000000 : ℝ) := by
  have hsmall : (52733222330453 / 50000000000000 : ℝ) ≤ Real.exp (109 / 2048 : ℝ) ∧
      Real.exp (109 / 2048 : ℝ) ≤ (105466444660907 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (109 / 2048 : ℝ))
    (a := (52733222330453 / 50000000000000 : ℝ)) (b := (105466444660907 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_019 :
    (264159 / 10000000 : ℝ) ≤ Real.exp (-(3721 / 1024 : ℝ)) ∧
    Real.exp (-(3721 / 1024 : ℝ)) ≤ (1651 / 62500 : ℝ) := by
  have hsmall : (2240509037 / 2000000000 : ℝ) ≤ Real.exp (3721 / 32768 : ℝ) ∧
      Real.exp (3721 / 32768 : ℝ) ≤ (5601272593 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3721 / 32768 : ℝ))
    (a := (2240509037 / 2000000000 : ℝ)) (b := (5601272593 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_020 :
    (1816193 / 5000000 : ℝ) ≤ Real.exp (-(1037 / 1024 : ℝ)) ∧
    Real.exp (-(1037 / 1024 : ℝ)) ≤ (3632387 / 10000000 : ℝ) := by
  have hsmall : (10321528107 / 10000000000 : ℝ) ≤ Real.exp (1037 / 32768 : ℝ) ∧
      Real.exp (1037 / 32768 : ℝ) ≤ (2580382027 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1037 / 32768 : ℝ))
    (a := (10321528107 / 10000000000 : ℝ)) (b := (2580382027 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_021 :
    (59630413 / 2500000 : ℝ) ≤ Real.exp (203 / 64 : ℝ) ∧
    Real.exp (203 / 64 : ℝ) ≤ (238521653 / 10000000 : ℝ) := by
  have hsmall : (110420000318251 / 100000000000000 : ℝ) ≤ Real.exp (203 / 2048 : ℝ) ∧
      Real.exp (203 / 2048 : ℝ) ≤ (27605000079563 / 25000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (203 / 2048 : ℝ))
    (a := (110420000318251 / 100000000000000 : ℝ)) (b := (27605000079563 / 25000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_022 :
    (26843 / 10000000 : ℝ) ≤ Real.exp (-(29601623 / 5000000 : ℝ)) ∧
    Real.exp (-(29601623 / 5000000 : ℝ)) ≤ (6711 / 2500000 : ℝ) := by
  have hsmall : (12032306453 / 10000000000 : ℝ) ≤ Real.exp (29601623 / 160000000 : ℝ) ∧
      Real.exp (29601623 / 160000000 : ℝ) ≤ (6016153227 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (29601623 / 160000000 : ℝ))
    (a := (12032306453 / 10000000000 : ℝ)) (b := (6016153227 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_023 :
    (46239 / 5000000 : ℝ) ≤ Real.exp (-(46833607 / 10000000 : ℝ)) ∧
    Real.exp (-(46833607 / 10000000 : ℝ)) ≤ (92479 / 10000000 : ℝ) := by
  have hsmall : (11576070909 / 10000000000 : ℝ) ≤ Real.exp (46833607 / 320000000 : ℝ) ∧
      Real.exp (46833607 / 320000000 : ℝ) ≤ (1157607091 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (46833607 / 320000000 : ℝ))
    (a := (11576070909 / 10000000000 : ℝ)) (b := (1157607091 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_024 :
    (24419339 / 5000000 : ℝ) ≤ Real.exp (203 / 128 : ℝ) ∧
    Real.exp (203 / 128 : ℝ) ≤ (48838679 / 10000000 : ℝ) := by
  have hsmall : (52540460675143 / 50000000000000 : ℝ) ≤ Real.exp (203 / 4096 : ℝ) ∧
      Real.exp (203 / 4096 : ℝ) ≤ (105080921350287 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (203 / 4096 : ℝ))
    (a := (52540460675143 / 50000000000000 : ℝ)) (b := (105080921350287 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_025 :
    (611047 / 10000000 : ℝ) ≤ Real.exp (-(11449 / 4096 : ℝ)) ∧
    Real.exp (-(11449 / 4096 : ℝ)) ≤ (76381 / 1250000 : ℝ) := by
  have hsmall : (5456387007 / 5000000000 : ℝ) ≤ Real.exp (11449 / 131072 : ℝ) ∧
      Real.exp (11449 / 131072 : ℝ) ≤ (2182554803 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (11449 / 131072 : ℝ))
    (a := (5456387007 / 5000000000 : ℝ)) (b := (2182554803 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_026 :
    (4114023 / 10000000 : ℝ) ≤ Real.exp (-(1819 / 2048 : ℝ)) ∧
    Real.exp (-(1819 / 2048 : ℝ)) ≤ (514253 / 1250000 : ℝ) := by
  have hsmall : (10281445163 / 10000000000 : ℝ) ≤ Real.exp (1819 / 65536 : ℝ) ∧
      Real.exp (1819 / 65536 : ℝ) ≤ (2570361291 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1819 / 65536 : ℝ))
    (a := (10281445163 / 10000000000 : ℝ)) (b := (2570361291 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_027 :
    (212145549 / 10000000 : ℝ) ≤ Real.exp (391 / 128 : ℝ) ∧
    Real.exp (391 / 128 : ℝ) ≤ (4242911 / 200000 : ℝ) := by
  have hsmall : (6876023107543 / 6250000000000 : ℝ) ≤ Real.exp (391 / 4096 : ℝ) ∧
      Real.exp (391 / 4096 : ℝ) ≤ (110016369720689 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (391 / 4096 : ℝ))
    (a := (6876023107543 / 6250000000000 : ℝ)) (b := (110016369720689 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_028 :
    (46239 / 5000000 : ℝ) ≤ Real.exp (-(46833623 / 10000000 : ℝ)) ∧
    Real.exp (-(46833623 / 10000000 : ℝ)) ≤ (92479 / 10000000 : ℝ) := by
  have hsmall : (180876117 / 156250000 : ℝ) ≤ Real.exp (46833623 / 320000000 : ℝ) ∧
      Real.exp (46833623 / 320000000 : ℝ) ≤ (11576071489 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (46833623 / 320000000 : ℝ))
    (a := (180876117 / 156250000 : ℝ)) (b := (11576071489 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_029 :
    (19403 / 1250000 : ℝ) ≤ Real.exp (-(2603417 / 625000 : ℝ)) ∧
    Real.exp (-(2603417 / 625000 : ℝ)) ≤ (6209 / 400000 : ℝ) := by
  have hsmall : (11390229687 / 10000000000 : ℝ) ≤ Real.exp (2603417 / 20000000 : ℝ) ∧
      Real.exp (2603417 / 20000000 : ℝ) ≤ (1423778711 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2603417 / 20000000 : ℝ))
    (a := (11390229687 / 10000000000 : ℝ)) (b := (1423778711 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_030 :
    (2302963 / 500000 : ℝ) ≤ Real.exp (391 / 256 : ℝ) ∧
    Real.exp (391 / 256 : ℝ) ≤ (46059261 / 10000000 : ℝ) := by
  have hsmall : (20977737696967 / 20000000000000 : ℝ) ≤ Real.exp (391 / 8192 : ℝ) ∧
      Real.exp (391 / 8192 : ℝ) ≤ (26222172121209 / 25000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (391 / 8192 : ℝ))
    (a := (20977737696967 / 20000000000000 : ℝ)) (b := (26222172121209 / 25000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_031 :
    (2787 / 31250 : ℝ) ≤ Real.exp (-(39601 / 16384 : ℝ)) ∧
    Real.exp (-(39601 / 16384 : ℝ)) ≤ (891841 / 10000000 : ℝ) := by
  have hsmall : (5392293613 / 5000000000 : ℝ) ≤ Real.exp (39601 / 524288 : ℝ) ∧
      Real.exp (39601 / 524288 : ℝ) ≤ (10784587227 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (39601 / 524288 : ℝ))
    (a := (5392293613 / 5000000000 : ℝ)) (b := (10784587227 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_032 :
    (2189143 / 5000000 : ℝ) ≤ Real.exp (-(3383 / 4096 : ℝ)) ∧
    Real.exp (-(3383 / 4096 : ℝ)) ≤ (4378287 / 10000000 : ℝ) := by
  have hsmall : (5130731051 / 5000000000 : ℝ) ≤ Real.exp (3383 / 131072 : ℝ) ∧
      Real.exp (3383 / 131072 : ℝ) ≤ (10261462103 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3383 / 131072 : ℝ))
    (a := (5130731051 / 5000000000 : ℝ)) (b := (10261462103 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_033 :
    (188686157 / 10000000 : ℝ) ≤ Real.exp (47 / 16 : ℝ) ∧
    Real.exp (47 / 16 : ℝ) ≤ (94343079 / 5000000 : ℝ) := by
  have hsmall : (109614214559267 / 100000000000000 : ℝ) ≤ Real.exp (47 / 512 : ℝ) ∧
      Real.exp (47 / 512 : ℝ) ≤ (27403553639817 / 25000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (47 / 512 : ℝ))
    (a := (109614214559267 / 100000000000000 : ℝ)) (b := (27403553639817 / 25000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_034 :
    (19403 / 1250000 : ℝ) ≤ Real.exp (-(20827343 / 5000000 : ℝ)) ∧
    Real.exp (-(20827343 / 5000000 : ℝ)) ≤ (6209 / 400000 : ℝ) := by
  have hsmall : (5695115093 / 5000000000 : ℝ) ≤ Real.exp (20827343 / 160000000 : ℝ) ∧
      Real.exp (20827343 / 160000000 : ℝ) ≤ (11390230187 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (20827343 / 160000000 : ℝ))
    (a := (5695115093 / 5000000000 : ℝ)) (b := (11390230187 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_035 :
    (6151 / 250000 : ℝ) ≤ Real.exp (-(2315527 / 625000 : ℝ)) ∧
    Real.exp (-(2315527 / 625000 : ℝ)) ≤ (246041 / 10000000 : ℝ) := by
  have hsmall : (11227447421 / 10000000000 : ℝ) ≤ Real.exp (2315527 / 20000000 : ℝ) ∧
      Real.exp (2315527 / 20000000 : ℝ) ≤ (5613723711 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2315527 / 20000000 : ℝ))
    (a := (11227447421 / 10000000000 : ℝ)) (b := (5613723711 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_036 :
    (43438019 / 10000000 : ℝ) ≤ Real.exp (47 / 32 : ℝ) ∧
    Real.exp (47 / 32 : ℝ) ≤ (2171901 / 500000 : ℝ) := by
  have hsmall : (52348403643107 / 50000000000000 : ℝ) ≤ Real.exp (47 / 1024 : ℝ) ∧
      Real.exp (47 / 1024 : ℝ) ≤ (20939361457243 / 20000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (47 / 1024 : ℝ))
    (a := (52348403643107 / 50000000000000 : ℝ)) (b := (20939361457243 / 20000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_037 :
    (1583 / 12500 : ℝ) ≤ Real.exp (-(529 / 256 : ℝ)) ∧
    Real.exp (-(529 / 256 : ℝ)) ≤ (1266401 / 10000000 : ℝ) := by
  have hsmall : (2133411573 / 2000000000 : ℝ) ≤ Real.exp (529 / 8192 : ℝ) ∧
      Real.exp (529 / 8192 : ℝ) ≤ (5333528933 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (529 / 8192 : ℝ))
    (a := (2133411573 / 2000000000 : ℝ)) (b := (5333528933 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_038 :
    (4659523 / 10000000 : ℝ) ≤ Real.exp (-(391 / 512 : ℝ)) ∧
    Real.exp (-(391 / 512 : ℝ)) ≤ (1164881 / 2500000 : ℝ) := by
  have hsmall : (10241517879 / 10000000000 : ℝ) ≤ Real.exp (391 / 16384 : ℝ) ∧
      Real.exp (391 / 16384 : ℝ) ≤ (256037947 / 250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (391 / 16384 : ℝ))
    (a := (10241517879 / 10000000000 : ℝ)) (b := (256037947 / 250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_039 :
    (83910471 / 5000000 : ℝ) ≤ Real.exp (361 / 128 : ℝ) ∧
    Real.exp (361 / 128 : ℝ) ≤ (167820943 / 10000000 : ℝ) := by
  have hsmall : (54606764720331 / 50000000000000 : ℝ) ≤ Real.exp (361 / 4096 : ℝ) ∧
      Real.exp (361 / 4096 : ℝ) ≤ (109213529440663 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (361 / 4096 : ℝ))
    (a := (54606764720331 / 50000000000000 : ℝ)) (b := (109213529440663 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_040 :
    (6151 / 250000 : ℝ) ≤ Real.exp (-(7409689 / 2000000 : ℝ)) ∧
    Real.exp (-(7409689 / 2000000 : ℝ)) ≤ (246041 / 10000000 : ℝ) := by
  have hsmall : (5613723939 / 5000000000 : ℝ) ≤ Real.exp (7409689 / 64000000 : ℝ) ∧
      Real.exp (7409689 / 64000000 : ℝ) ≤ (11227447879 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7409689 / 64000000 : ℝ))
    (a := (5613723939 / 5000000000 : ℝ)) (b := (11227447879 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_041 :
    (185311 / 5000000 : ℝ) ≤ Real.exp (-(16475779 / 5000000 : ℝ)) ∧
    Real.exp (-(16475779 / 5000000 : ℝ)) ≤ (370623 / 10000000 : ℝ) := by
  have hsmall : (554231083 / 500000000 : ℝ) ≤ Real.exp (16475779 / 160000000 : ℝ) ∧
      Real.exp (16475779 / 160000000 : ℝ) ≤ (11084621661 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (16475779 / 160000000 : ℝ))
    (a := (554231083 / 500000000 : ℝ)) (b := (11084621661 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_042 :
    (20482977 / 5000000 : ℝ) ≤ Real.exp (361 / 256 : ℝ) ∧
    Real.exp (361 / 256 : ℝ) ≤ (8193191 / 2000000 : ℝ) := by
  have hsmall : (26126319277773 / 25000000000000 : ℝ) ≤ Real.exp (361 / 8192 : ℝ) ∧
      Real.exp (361 / 8192 : ℝ) ≤ (104505277111093 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (361 / 8192 : ℝ))
    (a := (26126319277773 / 25000000000000 : ℝ)) (b := (104505277111093 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_043 :
    (109347 / 625000 : ℝ) ≤ Real.exp (-(28561 / 16384 : ℝ)) ∧
    Real.exp (-(28561 / 16384 : ℝ)) ≤ (1749553 / 10000000 : ℝ) := by
  have hsmall : (5279934523 / 5000000000 : ℝ) ≤ Real.exp (28561 / 524288 : ℝ) ∧
      Real.exp (28561 / 524288 : ℝ) ≤ (10559869047 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (28561 / 524288 : ℝ))
    (a := (5279934523 / 5000000000 : ℝ)) (b := (10559869047 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_044 :
    (2479413 / 5000000 : ℝ) ≤ Real.exp (-(2873 / 4096 : ℝ)) ∧
    Real.exp (-(2873 / 4096 : ℝ)) ≤ (4958827 / 10000000 : ℝ) := by
  have hsmall : (10221612421 / 10000000000 : ℝ) ≤ Real.exp (2873 / 131072 : ℝ) ∧
      Real.exp (2873 / 131072 : ℝ) ≤ (5110806211 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2873 / 131072 : ℝ))
    (a := (10221612421 / 10000000000 : ℝ)) (b := (5110806211 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_045 :
    (79135111 / 5000000 : ℝ) ≤ Real.exp (707 / 256 : ℝ) ∧
    Real.exp (707 / 256 : ℝ) ≤ (158270223 / 10000000 : ℝ) := by
  have hsmall : (109013736467393 / 100000000000000 : ℝ) ≤ Real.exp (707 / 8192 : ℝ) ∧
      Real.exp (707 / 8192 : ℝ) ≤ (54506868233697 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (707 / 8192 : ℝ))
    (a := (109013736467393 / 100000000000000 : ℝ)) (b := (54506868233697 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_046 :
    (185311 / 5000000 : ℝ) ≤ Real.exp (-(32951569 / 10000000 : ℝ)) ∧
    Real.exp (-(32951569 / 10000000 : ℝ)) ≤ (370623 / 10000000 : ℝ) := by
  have hsmall : (11084622041 / 10000000000 : ℝ) ≤ Real.exp (32951569 / 320000000 : ℝ) ∧
      Real.exp (32951569 / 320000000 : ℝ) ≤ (5542311021 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (32951569 / 320000000 : ℝ))
    (a := (11084622041 / 10000000000 : ℝ)) (b := (5542311021 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_047 :
    (111767 / 2500000 : ℝ) ≤ Real.exp (-(15538139 / 5000000 : ℝ)) ∧
    Real.exp (-(15538139 / 5000000 : ℝ)) ≤ (447069 / 10000000 : ℝ) := by
  have hsmall : (2754963243 / 2500000000 : ℝ) ≤ Real.exp (15538139 / 160000000 : ℝ) ∧
      Real.exp (15538139 / 160000000 : ℝ) ≤ (11019852973 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (15538139 / 160000000 : ℝ))
    (a := (2754963243 / 2500000000 : ℝ)) (b := (11019852973 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_048 :
    (3978319 / 1000000 : ℝ) ≤ Real.exp (707 / 512 : ℝ) ∧
    Real.exp (707 / 512 : ℝ) ≤ (39783191 / 10000000 : ℝ) := by
  have hsmall : (104409643456623 / 100000000000000 : ℝ) ≤ Real.exp (707 / 16384 : ℝ) ∧
      Real.exp (707 / 16384 : ℝ) ≤ (6525602716039 / 6250000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (707 / 16384 : ℝ))
    (a := (104409643456623 / 100000000000000 : ℝ)) (b := (6525602716039 / 6250000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_049 :
    (407063 / 2000000 : ℝ) ≤ Real.exp (-(104329 / 65536 : ℝ)) ∧
    Real.exp (-(104329 / 65536 : ℝ)) ≤ (508829 / 2500000 : ℝ) := by
  have hsmall : (164219711 / 156250000 : ℝ) ≤ Real.exp (104329 / 2097152 : ℝ) ∧
      Real.exp (104329 / 2097152 : ℝ) ≤ (2102012301 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (104329 / 2097152 : ℝ))
    (a := (164219711 / 156250000 : ℝ)) (b := (2102012301 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_050 :
    (5115611 / 10000000 : ℝ) ≤ Real.exp (-(5491 / 8192 : ℝ)) ∧
    Real.exp (-(5491 / 8192 : ℝ)) ≤ (1278903 / 2500000 : ℝ) := by
  have hsmall : (2552918551 / 2500000000 : ℝ) ≤ Real.exp (5491 / 262144 : ℝ) ∧
      Real.exp (5491 / 262144 : ℝ) ≤ (2042334841 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5491 / 262144 : ℝ))
    (a := (2552918551 / 2500000000 : ℝ)) (b := (2042334841 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_051 :
    (37315759 / 2500000 : ℝ) ≤ Real.exp (173 / 64 : ℝ) ∧
    Real.exp (173 / 64 : ℝ) ≤ (149263037 / 10000000 : ℝ) := by
  have hsmall : (108814308991259 / 100000000000000 : ℝ) ≤ Real.exp (173 / 2048 : ℝ) ∧
      Real.exp (173 / 2048 : ℝ) ≤ (5440715449563 / 5000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (173 / 2048 : ℝ))
    (a := (108814308991259 / 100000000000000 : ℝ)) (b := (5440715449563 / 5000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_052 :
    (111767 / 2500000 : ℝ) ≤ Real.exp (-(3107629 / 1000000 : ℝ)) ∧
    Real.exp (-(3107629 / 1000000 : ℝ)) ≤ (447069 / 10000000 : ℝ) := by
  have hsmall : (2203970677 / 2000000000 : ℝ) ≤ Real.exp (3107629 / 32000000 : ℝ) ∧
      Real.exp (3107629 / 32000000 : ℝ) ≤ (5509926693 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3107629 / 32000000 : ℝ))
    (a := (2203970677 / 2000000000 : ℝ)) (b := (5509926693 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_053 :
    (266779 / 5000000 : ℝ) ≤ Real.exp (-(14653861 / 5000000 : ℝ)) ∧
    Real.exp (-(14653861 / 5000000 : ℝ)) ≤ (533559 / 10000000 : ℝ) := by
  have hsmall : (10959117127 / 10000000000 : ℝ) ≤ Real.exp (14653861 / 160000000 : ℝ) ∧
      Real.exp (14653861 / 160000000 : ℝ) ≤ (1369889641 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (14653861 / 160000000 : ℝ))
    (a := (10959117127 / 10000000000 : ℝ)) (b := (1369889641 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_054 :
    (19317287 / 5000000 : ℝ) ≤ Real.exp (173 / 128 : ℝ) ∧
    Real.exp (173 / 128 : ℝ) ≤ (1545383 / 400000 : ℝ) := by
  have hsmall : (104314097317313 / 100000000000000 : ℝ) ≤ Real.exp (173 / 4096 : ℝ) ∧
      Real.exp (173 / 4096 : ℝ) ≤ (52157048658657 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (173 / 4096 : ℝ))
    (a := (104314097317313 / 100000000000000 : ℝ)) (b := (52157048658657 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_055 :
    (2351551 / 10000000 : ℝ) ≤ Real.exp (-(5929 / 4096 : ℝ)) ∧
    Real.exp (-(5929 / 4096 : ℝ)) ≤ (36743 / 156250 : ℝ) := by
  have hsmall : (10462733707 / 10000000000 : ℝ) ≤ Real.exp (5929 / 131072 : ℝ) ∧
      Real.exp (5929 / 131072 : ℝ) ≤ (2615683427 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5929 / 131072 : ℝ))
    (a := (10462733707 / 10000000000 : ℝ)) (b := (2615683427 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_056 :
    (2638677 / 5000000 : ℝ) ≤ Real.exp (-(1309 / 2048 : ℝ)) ∧
    Real.exp (-(1309 / 2048 : ℝ)) ≤ (1055471 / 2000000 : ℝ) := by
  have hsmall : (204034913 / 200000000 : ℝ) ≤ Real.exp (1309 / 65536 : ℝ) ∧
      Real.exp (1309 / 65536 : ℝ) ≤ (10201745651 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1309 / 65536 : ℝ))
    (a := (204034913 / 200000000 : ℝ)) (b := (10201745651 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_057 :
    (2815369 / 200000 : ℝ) ≤ Real.exp (677 / 256 : ℝ) ∧
    Real.exp (677 / 256 : ℝ) ≤ (140768451 / 10000000 : ℝ) := by
  have hsmall : (27153811585907 / 25000000000000 : ℝ) ≤ Real.exp (677 / 8192 : ℝ) ∧
      Real.exp (677 / 8192 : ℝ) ≤ (108615246343629 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (677 / 8192 : ℝ))
    (a := (27153811585907 / 25000000000000 : ℝ)) (b := (108615246343629 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_058 :
    (533557 / 10000000 : ℝ) ≤ Real.exp (-(29307733 / 10000000 : ℝ)) ∧
    Real.exp (-(29307733 / 10000000 : ℝ)) ≤ (266779 / 5000000 : ℝ) := by
  have hsmall : (171236211 / 156250000 : ℝ) ≤ Real.exp (29307733 / 320000000 : ℝ) ∧
      Real.exp (29307733 / 320000000 : ℝ) ≤ (2191823501 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (29307733 / 320000000 : ℝ))
    (a := (171236211 / 156250000 : ℝ)) (b := (2191823501 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_059 :
    (315201 / 5000000 : ℝ) ≤ Real.exp (-(13819907 / 5000000 : ℝ)) ∧
    Real.exp (-(13819907 / 5000000 : ℝ)) ≤ (630403 / 10000000 : ℝ) := by
  have hsmall : (5451072243 / 5000000000 : ℝ) ≤ Real.exp (13819907 / 160000000 : ℝ) ∧
      Real.exp (13819907 / 160000000 : ℝ) ≤ (10902144487 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (13819907 / 160000000 : ℝ))
    (a := (5451072243 / 5000000000 : ℝ)) (b := (10902144487 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_060 :
    (37519121 / 10000000 : ℝ) ≤ Real.exp (677 / 512 : ℝ) ∧
    Real.exp (677 / 512 : ℝ) ≤ (18759561 / 5000000 : ℝ) := by
  have hsmall : (4168745544523 / 4000000000000 : ℝ) ≤ Real.exp (677 / 16384 : ℝ) ∧
      Real.exp (677 / 16384 : ℝ) ≤ (26054659653269 / 25000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (677 / 16384 : ℝ))
    (a := (4168745544523 / 4000000000000 : ℝ)) (b := (26054659653269 / 25000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_061 :
    (269833 / 1000000 : ℝ) ≤ Real.exp (-(85849 / 65536 : ℝ)) ∧
    Real.exp (-(85849 / 65536 : ℝ)) ≤ (2698331 / 10000000 : ℝ) := by
  have hsmall : (520892711 / 500000000 : ℝ) ≤ Real.exp (85849 / 2097152 : ℝ) ∧
      Real.exp (85849 / 2097152 : ℝ) ≤ (10417854221 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (85849 / 2097152 : ℝ))
    (a := (520892711 / 500000000 : ℝ)) (b := (10417854221 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_062 :
    (5444211 / 10000000 : ℝ) ≤ Real.exp (-(4981 / 8192 : ℝ)) ∧
    Real.exp (-(4981 / 8192 : ℝ)) ≤ (1361053 / 2500000 : ℝ) := by
  have hsmall : (40767307 / 40000000 : ℝ) ≤ Real.exp (4981 / 262144 : ℝ) ∧
      Real.exp (4981 / 262144 : ℝ) ≤ (10191826751 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (4981 / 262144 : ℝ))
    (a := (40767307 / 40000000 : ℝ)) (b := (10191826751 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_063 :
    (33189323 / 2500000 : ℝ) ≤ Real.exp (331 / 128 : ℝ) ∧
    Real.exp (331 / 128 : ℝ) ≤ (132757293 / 10000000 : ℝ) := by
  have hsmall : (10841654785709 / 10000000000000 : ℝ) ≤ Real.exp (331 / 4096 : ℝ) ∧
      Real.exp (331 / 4096 : ℝ) ≤ (108416547857091 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (331 / 4096 : ℝ))
    (a := (10841654785709 / 10000000000000 : ℝ)) (b := (108416547857091 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_064 :
    (315201 / 5000000 : ℝ) ≤ Real.exp (-(1727489 / 625000 : ℝ)) ∧
    Real.exp (-(1727489 / 625000 : ℝ)) ≤ (630403 / 10000000 : ℝ) := by
  have hsmall : (5451072413 / 5000000000 : ℝ) ≤ Real.exp (1727489 / 20000000 : ℝ) ∧
      Real.exp (1727489 / 20000000 : ℝ) ≤ (10902144827 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1727489 / 20000000 : ℝ))
    (a := (5451072413 / 5000000000 : ℝ)) (b := (10902144827 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_065 :
    (184447 / 2500000 : ℝ) ≤ Real.exp (-(26066827 / 10000000 : ℝ)) ∧
    Real.exp (-(26066827 / 10000000 : ℝ)) ≤ (737789 / 10000000 : ℝ) := by
  have hsmall : (10848685573 / 10000000000 : ℝ) ≤ Real.exp (26066827 / 320000000 : ℝ) ∧
      Real.exp (26066827 / 320000000 : ℝ) ≤ (5424342787 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (26066827 / 320000000 : ℝ))
    (a := (10848685573 / 10000000000 : ℝ)) (b := (5424342787 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_066 :
    (18217937 / 5000000 : ℝ) ≤ Real.exp (331 / 256 : ℝ) ∧
    Real.exp (331 / 256 : ℝ) ≤ (291487 / 80000 : ℝ) := by
  have hsmall : (104123267263897 / 100000000000000 : ℝ) ≤ Real.exp (331 / 8192 : ℝ) ∧
      Real.exp (331 / 8192 : ℝ) ≤ (52061633631949 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (331 / 8192 : ℝ))
    (a := (104123267263897 / 100000000000000 : ℝ)) (b := (52061633631949 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_067 :
    (3075061 / 10000000 : ℝ) ≤ Real.exp (-(19321 / 16384 : ℝ)) ∧
    Real.exp (-(19321 / 16384 : ℝ)) ≤ (1537531 / 5000000 : ℝ) := by
  have hsmall : (10375393321 / 10000000000 : ℝ) ≤ Real.exp (19321 / 524288 : ℝ) ∧
      Real.exp (19321 / 524288 : ℝ) ≤ (5187696661 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (19321 / 524288 : ℝ))
    (a := (10375393321 / 10000000000 : ℝ)) (b := (5187696661 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_068 :
    (5616343 / 10000000 : ℝ) ≤ Real.exp (-(2363 / 4096 : ℝ)) ∧
    Real.exp (-(2363 / 4096 : ℝ)) ≤ (702043 / 1250000 : ℝ) := by
  have hsmall : (10181917493 / 10000000000 : ℝ) ≤ Real.exp (2363 / 131072 : ℝ) ∧
      Real.exp (2363 / 131072 : ℝ) ≤ (5090958747 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2363 / 131072 : ℝ))
    (a := (10181917493 / 10000000000 : ℝ)) (b := (5090958747 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_069 :
    (125202051 / 10000000 : ℝ) ≤ Real.exp (647 / 256 : ℝ) ∧
    Real.exp (647 / 256 : ℝ) ≤ (31300513 / 2500000 : ℝ) := by
  have hsmall : (6763638304091 / 6250000000000 : ℝ) ≤ Real.exp (647 / 8192 : ℝ) ∧
      Real.exp (647 / 8192 : ℝ) ≤ (108218212865457 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (647 / 8192 : ℝ))
    (a := (6763638304091 / 6250000000000 : ℝ)) (b := (108218212865457 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_070 :
    (184447 / 2500000 : ℝ) ≤ Real.exp (-(26066837 / 10000000 : ℝ)) ∧
    Real.exp (-(26066837 / 10000000 : ℝ)) ≤ (737789 / 10000000 : ℝ) := by
  have hsmall : (1356085739 / 1250000000 : ℝ) ≤ Real.exp (26066837 / 320000000 : ℝ) ∧
      Real.exp (26066837 / 320000000 : ℝ) ≤ (10848685913 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (26066837 / 320000000 : ℝ))
    (a := (1356085739 / 1250000000 : ℝ)) (b := (10848685913 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_071 :
    (213943 / 2500000 : ℝ) ≤ Real.exp (-(76823 / 31250 : ℝ)) ∧
    Real.exp (-(76823 / 31250 : ℝ)) ≤ (855773 / 10000000 : ℝ) := by
  have hsmall : (5399254629 / 5000000000 : ℝ) ≤ Real.exp (76823 / 1000000 : ℝ) ∧
      Real.exp (76823 / 1000000 : ℝ) ≤ (10798509259 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (76823 / 1000000 : ℝ))
    (a := (5399254629 / 5000000000 : ℝ)) (b := (10798509259 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_072 :
    (35383901 / 10000000 : ℝ) ≤ Real.exp (647 / 512 : ℝ) ∧
    Real.exp (647 / 512 : ℝ) ≤ (17691951 / 5000000 : ℝ) := by
  have hsmall : (104027983189839 / 100000000000000 : ℝ) ≤ Real.exp (647 / 16384 : ℝ) ∧
      Real.exp (647 / 16384 : ℝ) ≤ (1300349789873 / 1250000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (647 / 16384 : ℝ))
    (a := (104027983189839 / 100000000000000 : ℝ)) (b := (1300349789873 / 1250000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_073 :
    (3480409 / 10000000 : ℝ) ≤ Real.exp (-(69169 / 65536 : ℝ)) ∧
    Real.exp (-(69169 / 65536 : ℝ)) ≤ (348041 / 1000000 : ℝ) := by
  have hsmall : (5167661483 / 5000000000 : ℝ) ≤ Real.exp (69169 / 2097152 : ℝ) ∧
      Real.exp (69169 / 2097152 : ℝ) ≤ (10335322967 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (69169 / 2097152 : ℝ))
    (a := (5167661483 / 5000000000 : ℝ)) (b := (10335322967 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_074 :
    (5793917 / 10000000 : ℝ) ≤ Real.exp (-(4471 / 8192 : ℝ)) ∧
    Real.exp (-(4471 / 8192 : ℝ)) ≤ (2896959 / 5000000 : ℝ) := by
  have hsmall : (10172017871 / 10000000000 : ℝ) ≤ Real.exp (4471 / 262144 : ℝ) ∧
      Real.exp (4471 / 262144 : ℝ) ≤ (635751117 / 625000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (4471 / 262144 : ℝ))
    (a := (10172017871 / 10000000000 : ℝ)) (b := (635751117 / 625000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_075 :
    (5903839 / 500000 : ℝ) ≤ Real.exp (79 / 32 : ℝ) ∧
    Real.exp (79 / 32 : ℝ) ≤ (118076781 / 10000000 : ℝ) := by
  have hsmall : (27005060175939 / 25000000000000 : ℝ) ≤ Real.exp (79 / 1024 : ℝ) ∧
      Real.exp (79 / 1024 : ℝ) ≤ (108020240703757 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (79 / 1024 : ℝ))
    (a := (27005060175939 / 25000000000000 : ℝ)) (b := (108020240703757 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_076 :
    (855771 / 10000000 : ℝ) ≤ Real.exp (-(24583369 / 10000000 : ℝ)) ∧
    Real.exp (-(24583369 / 10000000 : ℝ)) ≤ (213943 / 2500000 : ℝ) := by
  have hsmall : (5399254781 / 5000000000 : ℝ) ≤ Real.exp (24583369 / 320000000 : ℝ) ∧
      Real.exp (24583369 / 320000000 : ℝ) ≤ (10798509563 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (24583369 / 320000000 : ℝ))
    (a := (5399254781 / 5000000000 : ℝ)) (b := (10798509563 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_077 :
    (492139 / 5000000 : ℝ) ≤ Real.exp (-(5796079 / 2500000 : ℝ)) ∧
    Real.exp (-(5796079 / 2500000 : ℝ)) ≤ (984279 / 10000000 : ℝ) := by
  have hsmall : (5375700547 / 5000000000 : ℝ) ≤ Real.exp (5796079 / 80000000 : ℝ) ∧
      Real.exp (5796079 / 80000000 : ℝ) ≤ (2150280219 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5796079 / 80000000 : ℝ))
    (a := (5375700547 / 5000000000 : ℝ)) (b := (2150280219 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_078 :
    (17181151 / 5000000 : ℝ) ≤ Real.exp (79 / 64 : ℝ) ∧
    Real.exp (79 / 64 : ℝ) ≤ (34362303 / 10000000 : ℝ) := by
  have hsmall : (25983196577759 / 25000000000000 : ℝ) ≤ Real.exp (79 / 2048 : ℝ) ∧
      Real.exp (79 / 2048 : ℝ) ≤ (103932786311037 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (79 / 2048 : ℝ))
    (a := (25983196577759 / 25000000000000 : ℝ)) (b := (103932786311037 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_079 :
    (3912233 / 10000000 : ℝ) ≤ Real.exp (-(961 / 1024 : ℝ)) ∧
    Real.exp (-(961 / 1024 : ℝ)) ≤ (1956117 / 5000000 : ℝ) := by
  have hsmall : (2574404189 / 2500000000 : ℝ) ≤ Real.exp (961 / 32768 : ℝ) ∧
      Real.exp (961 / 32768 : ℝ) ≤ (10297616757 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (961 / 32768 : ℝ))
    (a := (2574404189 / 2500000000 : ℝ)) (b := (10297616757 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_080 :
    (2988553 / 5000000 : ℝ) ≤ Real.exp (-(527 / 1024 : ℝ)) ∧
    Real.exp (-(527 / 1024 : ℝ)) ≤ (5977107 / 10000000 : ℝ) := by
  have hsmall : (5081063937 / 5000000000 : ℝ) ≤ Real.exp (527 / 32768 : ℝ) ∧
      Real.exp (527 / 32768 : ℝ) ≤ (81297023 / 80000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (527 / 32768 : ℝ))
    (a := (5081063937 / 5000000000 : ℝ)) (b := (81297023 / 80000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_081 :
    (111357009 / 10000000 : ℝ) ≤ Real.exp (617 / 256 : ℝ) ∧
    Real.exp (617 / 256 : ℝ) ≤ (11135701 / 1000000 : ℝ) := by
  have hsmall : (26955657677059 / 25000000000000 : ℝ) ≤ Real.exp (617 / 8192 : ℝ) ∧
      Real.exp (617 / 8192 : ℝ) ≤ (107822630708237 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (617 / 8192 : ℝ))
    (a := (26955657677059 / 25000000000000 : ℝ)) (b := (107822630708237 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_082 :
    (984277 / 10000000 : ℝ) ≤ Real.exp (-(927373 / 400000 : ℝ)) ∧
    Real.exp (-(927373 / 400000 : ℝ)) ≤ (492139 / 5000000 : ℝ) := by
  have hsmall : (10751401397 / 10000000000 : ℝ) ≤ Real.exp (927373 / 12800000 : ℝ) ∧
      Real.exp (927373 / 12800000 : ℝ) ≤ (5375700699 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (927373 / 12800000 : ℝ))
    (a := (10751401397 / 10000000000 : ℝ)) (b := (5375700699 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_083 :
    (1123103 / 10000000 : ℝ) ≤ Real.exp (-(21864893 / 10000000 : ℝ)) ∧
    Real.exp (-(21864893 / 10000000 : ℝ)) ≤ (35097 / 312500 : ℝ) := by
  have hsmall : (10707162217 / 10000000000 : ℝ) ≤ Real.exp (21864893 / 320000000 : ℝ) ∧
      Real.exp (21864893 / 320000000 : ℝ) ≤ (5353581109 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (21864893 / 320000000 : ℝ))
    (a := (10707162217 / 10000000000 : ℝ)) (b := (5353581109 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_084 :
    (33370197 / 10000000 : ℝ) ≤ Real.exp (617 / 512 : ℝ) ∧
    Real.exp (617 / 512 : ℝ) ≤ (16685099 / 5000000 : ℝ) := by
  have hsmall : (51918838273847 / 50000000000000 : ℝ) ≤ Real.exp (617 / 16384 : ℝ) ∧
      Real.exp (617 / 16384 : ℝ) ≤ (20767535309539 / 20000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (617 / 16384 : ℝ))
    (a := (51918838273847 / 50000000000000 : ℝ)) (b := (20767535309539 / 20000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_085 :
    (4367543 / 10000000 : ℝ) ≤ Real.exp (-(54289 / 65536 : ℝ)) ∧
    Real.exp (-(54289 / 65536 : ℝ)) ≤ (545943 / 1250000 : ℝ) := by
  have hsmall : (10262249913 / 10000000000 : ℝ) ≤ Real.exp (54289 / 2097152 : ℝ) ∧
      Real.exp (54289 / 2097152 : ℝ) ≤ (5131124957 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (54289 / 2097152 : ℝ))
    (a := (10262249913 / 10000000000 : ℝ)) (b := (5131124957 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_086 :
    (6166087 / 10000000 : ℝ) ≤ Real.exp (-(3961 / 8192 : ℝ)) ∧
    Real.exp (-(3961 / 8192 : ℝ)) ≤ (770761 / 1250000 : ℝ) := by
  have hsmall : (10152247493 / 10000000000 : ℝ) ≤ Real.exp (3961 / 262144 : ℝ) ∧
      Real.exp (3961 / 262144 : ℝ) ≤ (5076123747 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3961 / 262144 : ℝ))
    (a := (10152247493 / 10000000000 : ℝ)) (b := (5076123747 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_087 :
    (52509831 / 5000000 : ℝ) ≤ Real.exp (301 / 128 : ℝ) ∧
    Real.exp (301 / 128 : ℝ) ≤ (105019663 / 10000000 : ℝ) := by
  have hsmall : (107625382216357 / 100000000000000 : ℝ) ≤ Real.exp (301 / 4096 : ℝ) ∧
      Real.exp (301 / 4096 : ℝ) ≤ (53812691108179 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (301 / 4096 : ℝ))
    (a := (107625382216357 / 100000000000000 : ℝ)) (b := (53812691108179 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_088 :
    (561551 / 5000000 : ℝ) ≤ Real.exp (-(21864901 / 10000000 : ℝ)) ∧
    Real.exp (-(21864901 / 10000000 : ℝ)) ≤ (1123103 / 10000000 : ℝ) := by
  have hsmall : (2676790621 / 2500000000 : ℝ) ≤ Real.exp (21864901 / 320000000 : ℝ) ∧
      Real.exp (21864901 / 320000000 : ℝ) ≤ (2141432497 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (21864901 / 320000000 : ℝ))
    (a := (2676790621 / 2500000000 : ℝ)) (b := (2141432497 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_089 :
    (635961 / 5000000 : ℝ) ≤ Real.exp (-(10310279 / 5000000 : ℝ)) ∧
    Real.exp (-(10310279 / 5000000 : ℝ)) ≤ (1271923 / 10000000 : ℝ) := by
  have hsmall : (133320097 / 125000000 : ℝ) ≤ Real.exp (10310279 / 160000000 : ℝ) ∧
      Real.exp (10310279 / 160000000 : ℝ) ≤ (10665607761 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (10310279 / 160000000 : ℝ))
    (a := (133320097 / 125000000 : ℝ)) (b := (10665607761 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_090 :
    (32406737 / 10000000 : ℝ) ≤ Real.exp (301 / 256 : ℝ) ∧
    Real.exp (301 / 256 : ℝ) ≤ (16203369 / 5000000 : ℝ) := by
  have hsmall : (103742653820093 / 100000000000000 : ℝ) ≤ Real.exp (301 / 8192 : ℝ) ∧
      Real.exp (301 / 8192 : ℝ) ≤ (51871326910047 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (301 / 8192 : ℝ))
    (a := (103742653820093 / 100000000000000 : ℝ)) (b := (51871326910047 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_091 :
    (4842477 / 10000000 : ℝ) ≤ Real.exp (-(11881 / 16384 : ℝ)) ∧
    Real.exp (-(11881 / 16384 : ℝ)) ≤ (2421239 / 5000000 : ℝ) := by
  have hsmall : (639324953 / 625000000 : ℝ) ≤ Real.exp (11881 / 524288 : ℝ) ∧
      Real.exp (11881 / 524288 : ℝ) ≤ (10229199249 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (11881 / 524288 : ℝ))
    (a := (639324953 / 625000000 : ℝ)) (b := (10229199249 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_092 :
    (6361043 / 10000000 : ℝ) ≤ Real.exp (-(1853 / 4096 : ℝ)) ∧
    Real.exp (-(1853 / 4096 : ℝ)) ≤ (1272209 / 2000000 : ℝ) := by
  have hsmall : (5071188359 / 5000000000 : ℝ) ≤ Real.exp (1853 / 131072 : ℝ) ∧
      Real.exp (1853 / 131072 : ℝ) ≤ (10142376719 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1853 / 131072 : ℝ))
    (a := (5071188359 / 5000000000 : ℝ)) (b := (10142376719 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_093 :
    (49521487 / 5000000 : ℝ) ≤ Real.exp (587 / 256 : ℝ) ∧
    Real.exp (587 / 256 : ℝ) ≤ (3961719 / 400000 : ℝ) := by
  have hsmall : (107428494566793 / 100000000000000 : ℝ) ≤ Real.exp (587 / 8192 : ℝ) ∧
      Real.exp (587 / 8192 : ℝ) ≤ (53714247283397 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (587 / 8192 : ℝ))
    (a := (107428494566793 / 100000000000000 : ℝ)) (b := (53714247283397 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_094 :
    (1271921 / 10000000 : ℝ) ≤ Real.exp (-(4124113 / 2000000 : ℝ)) ∧
    Real.exp (-(4124113 / 2000000 : ℝ)) ≤ (635961 / 5000000 : ℝ) := by
  have hsmall : (10665607993 / 10000000000 : ℝ) ≤ Real.exp (4124113 / 64000000 : ℝ) ∧
      Real.exp (4124113 / 64000000 : ℝ) ≤ (5332803997 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (4124113 / 64000000 : ℝ))
    (a := (10665607993 / 10000000000 : ℝ)) (b := (5332803997 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_095 :
    (286059 / 2000000 : ℝ) ≤ Real.exp (-(9723519 / 5000000 : ℝ)) ∧
    Real.exp (-(9723519 / 5000000 : ℝ)) ≤ (178787 / 1250000 : ℝ) := by
  have hsmall : (5313282971 / 5000000000 : ℝ) ≤ Real.exp (9723519 / 160000000 : ℝ) ∧
      Real.exp (9723519 / 160000000 : ℝ) ≤ (10626565943 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (9723519 / 160000000 : ℝ))
    (a := (5313282971 / 5000000000 : ℝ)) (b := (10626565943 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_096 :
    (31471093 / 10000000 : ℝ) ≤ Real.exp (587 / 512 : ℝ) ∧
    Real.exp (587 / 512 : ℝ) ≤ (15735547 / 5000000 : ℝ) := by
  have hsmall : (51823859024293 / 50000000000000 : ℝ) ≤ Real.exp (587 / 16384 : ℝ) ∧
      Real.exp (587 / 16384 : ℝ) ≤ (103647718048587 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (587 / 16384 : ℝ))
    (a := (51823859024293 / 50000000000000 : ℝ)) (b := (103647718048587 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_097 :
    (1066463 / 2000000 : ℝ) ≤ Real.exp (-(41209 / 65536 : ℝ)) ∧
    Real.exp (-(41209 / 65536 : ℝ)) ≤ (1333079 / 2500000 : ℝ) := by
  have hsmall : (10198443141 / 10000000000 : ℝ) ≤ Real.exp (41209 / 2097152 : ℝ) ∧
      Real.exp (41209 / 2097152 : ℝ) ≤ (5099221571 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (41209 / 2097152 : ℝ))
    (a := (10198443141 / 10000000000 : ℝ)) (b := (5099221571 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_098 :
    (1640541 / 2500000 : ℝ) ≤ Real.exp (-(3451 / 8192 : ℝ)) ∧
    Real.exp (-(3451 / 8192 : ℝ)) ≤ (1312433 / 2000000 : ℝ) := by
  have hsmall : (506625777 / 500000000 : ℝ) ≤ Real.exp (3451 / 262144 : ℝ) ∧
      Real.exp (3451 / 262144 : ℝ) ≤ (10132515541 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3451 / 262144 : ℝ))
    (a := (506625777 / 500000000 : ℝ)) (b := (10132515541 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_099 :
    (96183417 / 10000000 : ℝ) ≤ Real.exp (1159 / 512 : ℝ) ∧
    Real.exp (1159 / 512 : ℝ) ≤ (48091709 / 5000000 : ℝ) := by
  have hsmall : (13416273231443 / 12500000000000 : ℝ) ≤ Real.exp (1159 / 16384 : ℝ) ∧
      Real.exp (1159 / 16384 : ℝ) ≤ (21466037170309 / 20000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1159 / 16384 : ℝ))
    (a := (13416273231443 / 12500000000000 : ℝ)) (b := (21466037170309 / 20000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_100 :
    (715147 / 5000000 : ℝ) ≤ Real.exp (-(3889409 / 2000000 : ℝ)) ∧
    Real.exp (-(3889409 / 2000000 : ℝ)) ≤ (286059 / 2000000 : ℝ) := by
  have hsmall : (5313283087 / 5000000000 : ℝ) ≤ Real.exp (3889409 / 64000000 : ℝ) ∧
      Real.exp (3889409 / 64000000 : ℝ) ≤ (425062647 / 400000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3889409 / 64000000 : ℝ))
    (a := (5313283087 / 5000000000 : ℝ)) (b := (425062647 / 400000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_101 :
    (15129 / 100000 : ℝ) ≤ Real.exp (-(3777113 / 2000000 : ℝ)) ∧
    Real.exp (-(3777113 / 2000000 : ℝ)) ≤ (1512901 / 10000000 : ℝ) := by
  have hsmall : (2651984221 / 2500000000 : ℝ) ≤ Real.exp (3777113 / 64000000 : ℝ) ∧
      Real.exp (3777113 / 64000000 : ℝ) ≤ (2121587377 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3777113 / 64000000 : ℝ))
    (a := (2651984221 / 2500000000 : ℝ)) (b := (2121587377 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_102 :
    (31013451 / 10000000 : ℝ) ≤ Real.exp (1159 / 1024 : ℝ) ∧
    Real.exp (1159 / 1024 : ℝ) ≤ (7753363 / 2500000 : ℝ) := by
  have hsmall : (51800141373249 / 50000000000000 : ℝ) ≤ Real.exp (1159 / 32768 : ℝ) ∧
      Real.exp (1159 / 32768 : ℝ) ≤ (103600282746499 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1159 / 32768 : ℝ))
    (a := (51800141373249 / 50000000000000 : ℝ)) (b := (103600282746499 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_103 :
    (1395281 / 2500000 : ℝ) ≤ Real.exp (-(152881 / 262144 : ℝ)) ∧
    Real.exp (-(152881 / 262144 : ℝ)) ≤ (44649 / 80000 : ℝ) := by
  have hsmall : (2545979803 / 2500000000 : ℝ) ≤ Real.exp (152881 / 8388608 : ℝ) ∧
      Real.exp (152881 / 8388608 : ℝ) ≤ (10183919213 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (152881 / 8388608 : ℝ))
    (a := (2545979803 / 2500000000 : ℝ)) (b := (10183919213 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_104 :
    (833137 / 1250000 : ℝ) ≤ Real.exp (-(6647 / 16384 : ℝ)) ∧
    Real.exp (-(6647 / 16384 : ℝ)) ≤ (6665097 / 10000000 : ℝ) := by
  have hsmall : (10127588547 / 10000000000 : ℝ) ≤ Real.exp (6647 / 524288 : ℝ) ∧
      Real.exp (6647 / 524288 : ℝ) ≤ (2531897137 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (6647 / 524288 : ℝ))
    (a := (10127588547 / 10000000000 : ℝ)) (b := (2531897137 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_105 :
    (93406421 / 10000000 : ℝ) ≤ Real.exp (143 / 64 : ℝ) ∧
    Real.exp (143 / 64 : ℝ) ≤ (46703211 / 5000000 : ℝ) := by
  have hsmall : (4289278683977 / 4000000000000 : ℝ) ≤ Real.exp (143 / 2048 : ℝ) ∧
      Real.exp (143 / 2048 : ℝ) ≤ (53615983549713 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (143 / 2048 : ℝ))
    (a := (4289278683977 / 4000000000000 : ℝ)) (b := (53615983549713 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_106 :
    (1512899 / 10000000 : ℝ) ≤ Real.exp (-(18885573 / 10000000 : ℝ)) ∧
    Real.exp (-(18885573 / 10000000 : ℝ)) ≤ (15129 / 100000 : ℝ) := by
  have hsmall : (10607937149 / 10000000000 : ℝ) ≤ Real.exp (18885573 / 320000000 : ℝ) ∧
      Real.exp (18885573 / 320000000 : ℝ) ≤ (212158743 / 200000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (18885573 / 320000000 : ℝ))
    (a := (10607937149 / 10000000000 : ℝ)) (b := (212158743 / 200000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_107 :
    (1597683 / 10000000 : ℝ) ≤ Real.exp (-(1146269 / 625000 : ℝ)) ∧
    Real.exp (-(1146269 / 625000 : ℝ)) ≤ (399421 / 2500000 : ℝ) := by
  have hsmall : (529493849 / 500000000 : ℝ) ≤ Real.exp (1146269 / 20000000 : ℝ) ∧
      Real.exp (1146269 / 20000000 : ℝ) ≤ (10589876981 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1146269 / 20000000 : ℝ))
    (a := (529493849 / 500000000 : ℝ)) (b := (10589876981 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_108 :
    (955077 / 312500 : ℝ) ≤ Real.exp (143 / 128 : ℝ) ∧
    Real.exp (143 / 128 : ℝ) ≤ (6112493 / 2000000 : ℝ) := by
  have hsmall : (103552869153599 / 100000000000000 : ℝ) ≤ Real.exp (143 / 4096 : ℝ) ∧
      Real.exp (143 / 4096 : ℝ) ≤ (64720543221 / 62500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (143 / 4096 : ℝ))
    (a := (103552869153599 / 100000000000000 : ℝ)) (b := (64720543221 / 62500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_109 :
    (1457881 / 2500000 : ℝ) ≤ Real.exp (-(2209 / 4096 : ℝ)) ∧
    Real.exp (-(2209 / 4096 : ℝ)) ≤ (233261 / 400000 : ℝ) := by
  have hsmall : (10169961511 / 10000000000 : ℝ) ≤ Real.exp (2209 / 131072 : ℝ) ∧
      Real.exp (2209 / 131072 : ℝ) ≤ (1271245189 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2209 / 131072 : ℝ))
    (a := (10169961511 / 10000000000 : ℝ)) (b := (1271245189 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_110 :
    (6769643 / 10000000 : ℝ) ≤ Real.exp (-(799 / 2048 : ℝ)) ∧
    Real.exp (-(799 / 2048 : ℝ)) ≤ (1692411 / 2500000 : ℝ) := by
  have hsmall : (202453279 / 200000000 : ℝ) ≤ Real.exp (799 / 65536 : ℝ) ∧
      Real.exp (799 / 65536 : ℝ) ≤ (10122663951 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (799 / 65536 : ℝ))
    (a := (202453279 / 200000000 : ℝ)) (b := (10122663951 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_111 :
    (45354801 / 5000000 : ℝ) ≤ Real.exp (1129 / 512 : ℝ) ∧
    Real.exp (1129 / 512 : ℝ) ≤ (90709603 / 10000000 : ℝ) := by
  have hsmall : (26783459557027 / 25000000000000 : ℝ) ≤ Real.exp (1129 / 16384 : ℝ) ∧
      Real.exp (1129 / 16384 : ℝ) ≤ (107133838228109 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1129 / 16384 : ℝ))
    (a := (26783459557027 / 25000000000000 : ℝ)) (b := (107133838228109 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_112 :
    (798841 / 5000000 : ℝ) ≤ Real.exp (-(18340311 / 10000000 : ℝ)) ∧
    Real.exp (-(18340311 / 10000000 : ℝ)) ≤ (1597683 / 10000000 : ℝ) := by
  have hsmall : (2647469303 / 2500000000 : ℝ) ≤ Real.exp (18340311 / 320000000 : ℝ) ∧
      Real.exp (18340311 / 320000000 : ℝ) ≤ (10589877213 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (18340311 / 320000000 : ℝ))
    (a := (2647469303 / 2500000000 : ℝ)) (b := (10589877213 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_113 :
    (1684563 / 10000000 : ℝ) ≤ Real.exp (-(556587 / 312500 : ℝ)) ∧
    Real.exp (-(556587 / 312500 : ℝ)) ≤ (421141 / 2500000 : ℝ) := by
  have hsmall : (10324578 / 9765625 : ℝ) ≤ Real.exp (556587 / 10000000 : ℝ) ∧
      Real.exp (556587 / 10000000 : ℝ) ≤ (10572367873 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (556587 / 10000000 : ℝ))
    (a := (10324578 / 9765625 : ℝ)) (b := (10572367873 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_114 :
    (15059017 / 5000000 : ℝ) ≤ Real.exp (1129 / 1024 : ℝ) ∧
    Real.exp (1129 / 1024 : ℝ) ≤ (6023607 / 2000000 : ℝ) := by
  have hsmall : (103505477259953 / 100000000000000 : ℝ) ≤ Real.exp (1129 / 32768 : ℝ) ∧
      Real.exp (1129 / 32768 : ℝ) ≤ (51752738629977 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1129 / 32768 : ℝ))
    (a := (103505477259953 / 100000000000000 : ℝ)) (b := (51752738629977 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_115 :
    (6082707 / 10000000 : ℝ) ≤ Real.exp (-(130321 / 262144 : ℝ)) ∧
    Real.exp (-(130321 / 262144 : ℝ)) ≤ (1520677 / 2500000 : ℝ) := by
  have hsmall : (5078283883 / 5000000000 : ℝ) ≤ Real.exp (130321 / 8388608 : ℝ) ∧
      Real.exp (130321 / 8388608 : ℝ) ≤ (10156567767 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (130321 / 8388608 : ℝ))
    (a := (5078283883 / 5000000000 : ℝ)) (b := (10156567767 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_116 :
    (6875829 / 10000000 : ℝ) ≤ Real.exp (-(6137 / 16384 : ℝ)) ∧
    Real.exp (-(6137 / 16384 : ℝ)) ≤ (687583 / 1000000 : ℝ) := by
  have hsmall : (2529435437 / 2500000000 : ℝ) ≤ Real.exp (6137 / 524288 : ℝ) ∧
      Real.exp (6137 / 524288 : ℝ) ≤ (10117741749 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (6137 / 524288 : ℝ))
    (a := (2529435437 / 2500000000 : ℝ)) (b := (10117741749 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_117 :
    (17618129 / 2000000 : ℝ) ≤ Real.exp (557 / 256 : ℝ) ∧
    Real.exp (557 / 256 : ℝ) ≤ (44045323 / 5000000 : ℝ) := by
  have hsmall : (107035799155343 / 100000000000000 : ℝ) ≤ Real.exp (557 / 8192 : ℝ) ∧
      Real.exp (557 / 8192 : ℝ) ≤ (6689737447209 / 6250000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (557 / 8192 : ℝ))
    (a := (107035799155343 / 100000000000000 : ℝ)) (b := (6689737447209 / 6250000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_118 :
    (842281 / 5000000 : ℝ) ≤ Real.exp (-(17810791 / 10000000 : ℝ)) ∧
    Real.exp (-(17810791 / 10000000 : ℝ)) ≤ (1684563 / 10000000 : ℝ) := by
  have hsmall : (10572368103 / 10000000000 : ℝ) ≤ Real.exp (17810791 / 320000000 : ℝ) ∧
      Real.exp (17810791 / 320000000 : ℝ) ≤ (1321546013 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (17810791 / 320000000 : ℝ))
    (a := (10572368103 / 10000000000 : ℝ)) (b := (1321546013 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_119 :
    (354691 / 2000000 : ℝ) ≤ Real.exp (-(8648277 / 5000000 : ℝ)) ∧
    Real.exp (-(8648277 / 5000000 : ℝ)) ≤ (110841 / 625000 : ℝ) := by
  have hsmall : (10555392051 / 10000000000 : ℝ) ≤ Real.exp (8648277 / 160000000 : ℝ) ∧
      Real.exp (8648277 / 160000000 : ℝ) ≤ (2638848013 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (8648277 / 160000000 : ℝ))
    (a := (10555392051 / 10000000000 : ℝ)) (b := (2638848013 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_120 :
    (7420017 / 2500000 : ℝ) ≤ Real.exp (557 / 512 : ℝ) ∧
    Real.exp (557 / 512 : ℝ) ≤ (29680069 / 10000000 : ℝ) := by
  have hsmall : (10345810705563 / 10000000000000 : ℝ) ≤ Real.exp (557 / 16384 : ℝ) ∧
      Real.exp (557 / 16384 : ℝ) ≤ (103458107055631 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (557 / 16384 : ℝ))
    (a := (10345810705563 / 10000000000000 : ℝ)) (b := (103458107055631 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_121 :
    (1583457 / 2500000 : ℝ) ≤ Real.exp (-(29929 / 65536 : ℝ)) ∧
    Real.exp (-(29929 / 65536 : ℝ)) ≤ (6333829 / 10000000 : ℝ) := by
  have hsmall : (5071867899 / 5000000000 : ℝ) ≤ Real.exp (29929 / 2097152 : ℝ) ∧
      Real.exp (29929 / 2097152 : ℝ) ≤ (10143735799 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (29929 / 2097152 : ℝ))
    (a := (5071867899 / 5000000000 : ℝ)) (b := (10143735799 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_122 :
    (3491841 / 5000000 : ℝ) ≤ Real.exp (-(2941 / 8192 : ℝ)) ∧
    Real.exp (-(2941 / 8192 : ℝ)) ≤ (6983683 / 10000000 : ℝ) := by
  have hsmall : (10112821939 / 10000000000 : ℝ) ≤ Real.exp (2941 / 262144 : ℝ) ∧
      Real.exp (2941 / 262144 : ℝ) ≤ (505641097 / 500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2941 / 262144 : ℝ))
    (a := (10112821939 / 10000000000 : ℝ)) (b := (505641097 / 500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_123 :
    (42773651 / 5000000 : ℝ) ≤ Real.exp (1099 / 512 : ℝ) ∧
    Real.exp (1099 / 512 : ℝ) ≤ (85547303 / 10000000 : ℝ) := by
  have hsmall : (21387569959791 / 20000000000000 : ℝ) ≤ Real.exp (1099 / 16384 : ℝ) ∧
      Real.exp (1099 / 16384 : ℝ) ≤ (26734462449739 / 25000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1099 / 16384 : ℝ))
    (a := (21387569959791 / 20000000000000 : ℝ)) (b := (26734462449739 / 25000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_124 :
    (886727 / 5000000 : ℝ) ≤ Real.exp (-(216207 / 125000 : ℝ)) ∧
    Real.exp (-(216207 / 125000 : ℝ)) ≤ (354691 / 2000000 : ℝ) := by
  have hsmall : (1319424031 / 1250000000 : ℝ) ≤ Real.exp (216207 / 4000000 : ℝ) ∧
      Real.exp (216207 / 4000000 : ℝ) ≤ (10555392249 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (216207 / 4000000 : ℝ))
    (a := (1319424031 / 1250000000 : ℝ)) (b := (10555392249 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_125 :
    (1864267 / 10000000 : ℝ) ≤ Real.exp (-(16797169 / 10000000 : ℝ)) ∧
    Real.exp (-(16797169 / 10000000 : ℝ)) ≤ (466067 / 2500000 : ℝ) := by
  have hsmall : (10538932383 / 10000000000 : ℝ) ≤ Real.exp (16797169 / 320000000 : ℝ) ∧
      Real.exp (16797169 / 320000000 : ℝ) ≤ (329341637 / 312500000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (16797169 / 320000000 : ℝ))
    (a := (10538932383 / 10000000000 : ℝ)) (b := (329341637 / 312500000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_126 :
    (2924847 / 1000000 : ℝ) ≤ Real.exp (1099 / 1024 : ℝ) ∧
    Real.exp (1099 / 1024 : ℝ) ≤ (29248471 / 10000000 : ℝ) := by
  have hsmall : (103410758530703 / 100000000000000 : ℝ) ≤ Real.exp (1099 / 32768 : ℝ) ∧
      Real.exp (1099 / 32768 : ℝ) ≤ (6463172408169 / 6250000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1099 / 32768 : ℝ))
    (a := (103410758530703 / 100000000000000 : ℝ)) (b := (6463172408169 / 6250000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_127 :
    (6584003 / 10000000 : ℝ) ≤ Real.exp (-(109561 / 262144 : ℝ)) ∧
    Real.exp (-(109561 / 262144 : ℝ)) ≤ (1646001 / 2500000 : ℝ) := by
  have hsmall : (10131463523 / 10000000000 : ℝ) ≤ Real.exp (109561 / 8388608 : ℝ) ∧
      Real.exp (109561 / 8388608 : ℝ) ≤ (2532865881 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (109561 / 8388608 : ℝ))
    (a := (10131463523 / 10000000000 : ℝ)) (b := (2532865881 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_128 :
    (3546613 / 5000000 : ℝ) ≤ Real.exp (-(5627 / 16384 : ℝ)) ∧
    Real.exp (-(5627 / 16384 : ℝ)) ≤ (7093227 / 10000000 : ℝ) := by
  have hsmall : (5053952261 / 5000000000 : ℝ) ≤ Real.exp (5627 / 524288 : ℝ) ∧
      Real.exp (5627 / 524288 : ℝ) ≤ (10107904523 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5627 / 524288 : ℝ))
    (a := (5053952261 / 5000000000 : ℝ)) (b := (10107904523 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_129 :
    (8307739 / 1000000 : ℝ) ≤ Real.exp (271 / 128 : ℝ) ∧
    Real.exp (271 / 128 : ℝ) ≤ (83077391 / 10000000 : ℝ) := by
  have hsmall : (106839990076843 / 100000000000000 : ℝ) ≤ Real.exp (271 / 4096 : ℝ) ∧
      Real.exp (271 / 4096 : ℝ) ≤ (26709997519211 / 25000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (271 / 4096 : ℝ))
    (a := (106839990076843 / 100000000000000 : ℝ)) (b := (26709997519211 / 25000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_130 :
    (932133 / 5000000 : ℝ) ≤ Real.exp (-(2099647 / 1250000 : ℝ)) ∧
    Real.exp (-(2099647 / 1250000 : ℝ)) ≤ (1864267 / 10000000 : ℝ) := by
  have hsmall : (5269466307 / 5000000000 : ℝ) ≤ Real.exp (2099647 / 40000000 : ℝ) ∧
      Real.exp (2099647 / 40000000 : ℝ) ≤ (2107786523 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2099647 / 40000000 : ℝ))
    (a := (5269466307 / 5000000000 : ℝ)) (b := (2107786523 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_131 :
    (978453 / 5000000 : ℝ) ≤ Real.exp (-(16312203 / 10000000 : ℝ)) ∧
    Real.exp (-(16312203 / 10000000 : ℝ)) ≤ (1956907 / 10000000 : ℝ) := by
  have hsmall : (1052297253 / 1000000000 : ℝ) ≤ Real.exp (16312203 / 320000000 : ℝ) ∧
      Real.exp (16312203 / 320000000 : ℝ) ≤ (10522972531 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (16312203 / 320000000 : ℝ))
    (a := (1052297253 / 1000000000 : ℝ)) (b := (10522972531 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_132 :
    (7205787 / 2500000 : ℝ) ≤ Real.exp (271 / 256 : ℝ) ∧
    Real.exp (271 / 256 : ℝ) ≤ (28823149 / 10000000 : ℝ) := by
  have hsmall : (103363431675251 / 100000000000000 : ℝ) ≤ Real.exp (271 / 8192 : ℝ) ∧
      Real.exp (271 / 8192 : ℝ) ≤ (25840857918813 / 25000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (271 / 8192 : ℝ))
    (a := (103363431675251 / 100000000000000 : ℝ)) (b := (25840857918813 / 25000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_133 :
    (3416161 / 5000000 : ℝ) ≤ Real.exp (-(6241 / 16384 : ℝ)) ∧
    Real.exp (-(6241 / 16384 : ℝ)) ≤ (6832323 / 10000000 : ℝ) := by
  have hsmall : (2023949789 / 2000000000 : ℝ) ≤ Real.exp (6241 / 524288 : ℝ) ∧
      Real.exp (6241 / 524288 : ℝ) ≤ (5059874473 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (6241 / 524288 : ℝ))
    (a := (2023949789 / 2000000000 : ℝ)) (b := (5059874473 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_134 :
    (900561 / 1250000 : ℝ) ≤ Real.exp (-(1343 / 4096 : ℝ)) ∧
    Real.exp (-(1343 / 4096 : ℝ)) ≤ (7204489 / 10000000 : ℝ) := by
  have hsmall : (1262873687 / 1250000000 : ℝ) ≤ Real.exp (1343 / 131072 : ℝ) ∧
      Real.exp (1343 / 131072 : ℝ) ≤ (10102989497 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1343 / 131072 : ℝ))
    (a := (1262873687 / 1250000000 : ℝ)) (b := (10102989497 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_135 :
    (8067879 / 1000000 : ℝ) ≤ Real.exp (1069 / 512 : ℝ) ∧
    Real.exp (1069 / 512 : ℝ) ≤ (80678791 / 10000000 : ℝ) := by
  have hsmall : (106742219906983 / 100000000000000 : ℝ) ≤ Real.exp (1069 / 16384 : ℝ) ∧
      Real.exp (1069 / 16384 : ℝ) ≤ (13342777488373 / 12500000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1069 / 16384 : ℝ))
    (a := (106742219906983 / 100000000000000 : ℝ)) (b := (13342777488373 / 12500000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_136 :
    (244613 / 1250000 : ℝ) ≤ Real.exp (-(1631221 / 1000000 : ℝ)) ∧
    Real.exp (-(1631221 / 1000000 : ℝ)) ≤ (391381 / 2000000 : ℝ) := by
  have hsmall : (10522972761 / 10000000000 : ℝ) ≤ Real.exp (1631221 / 32000000 : ℝ) ∧
      Real.exp (1631221 / 32000000 : ℝ) ≤ (5261486381 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1631221 / 32000000 : ℝ))
    (a := (10522972761 / 10000000000 : ℝ)) (b := (5261486381 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_137 :
    (1025637 / 5000000 : ℝ) ≤ Real.exp (-(396031 / 250000 : ℝ)) ∧
    Real.exp (-(396031 / 250000 : ℝ)) ≤ (82051 / 400000 : ℝ) := by
  have hsmall : (5253748319 / 5000000000 : ℝ) ≤ Real.exp (396031 / 8000000 : ℝ) ∧
      Real.exp (396031 / 8000000 : ℝ) ≤ (10507496639 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (396031 / 8000000 : ℝ))
    (a := (5253748319 / 5000000000 : ℝ)) (b := (10507496639 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_138 :
    (7101003 / 2500000 : ℝ) ≤ Real.exp (1069 / 1024 : ℝ) ∧
    Real.exp (1069 / 1024 : ℝ) ≤ (28404013 / 10000000 : ℝ) := by
  have hsmall : (25829031619839 / 25000000000000 : ℝ) ≤ Real.exp (1069 / 32768 : ℝ) ∧
      Real.exp (1069 / 32768 : ℝ) ≤ (103316126479357 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1069 / 32768 : ℝ))
    (a := (25829031619839 / 25000000000000 : ℝ)) (b := (103316126479357 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_139 :
    (3538923 / 5000000 : ℝ) ≤ Real.exp (-(90601 / 262144 : ℝ)) ∧
    Real.exp (-(90601 / 262144 : ℝ)) ≤ (7077847 / 10000000 : ℝ) := by
  have hsmall : (2021718033 / 2000000000 : ℝ) ≤ Real.exp (90601 / 8388608 : ℝ) ∧
      Real.exp (90601 / 8388608 : ℝ) ≤ (5054295083 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (90601 / 8388608 : ℝ))
    (a := (2021718033 / 2000000000 : ℝ)) (b := (5054295083 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_140 :
    (914687 / 1250000 : ℝ) ≤ Real.exp (-(5117 / 16384 : ℝ)) ∧
    Real.exp (-(5117 / 16384 : ℝ)) ≤ (7317497 / 10000000 : ℝ) := by
  have hsmall : (10098076861 / 10000000000 : ℝ) ≤ Real.exp (5117 / 524288 : ℝ) ∧
      Real.exp (5117 / 524288 : ℝ) ≤ (5049038431 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5117 / 524288 : ℝ))
    (a := (10098076861 / 10000000000 : ℝ)) (b := (5049038431 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_141 :
    (78349441 / 10000000 : ℝ) ≤ Real.exp (527 / 256 : ℝ) ∧
    Real.exp (527 / 256 : ℝ) ≤ (39174721 / 5000000 : ℝ) := by
  have hsmall : (416580231279 / 390625000000 : ℝ) ≤ Real.exp (527 / 8192 : ℝ) ∧
      Real.exp (527 / 8192 : ℝ) ≤ (4265781568297 / 4000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (527 / 8192 : ℝ))
    (a := (416580231279 / 390625000000 : ℝ)) (b := (4265781568297 / 4000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_142 :
    (256409 / 1250000 : ℝ) ≤ Real.exp (-(7920623 / 5000000 : ℝ)) ∧
    Real.exp (-(7920623 / 5000000 : ℝ)) ≤ (2051273 / 10000000 : ℝ) := by
  have hsmall : (2101499367 / 2000000000 : ℝ) ≤ Real.exp (7920623 / 160000000 : ℝ) ∧
      Real.exp (7920623 / 160000000 : ℝ) ≤ (2626874209 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7920623 / 160000000 : ℝ))
    (a := (2101499367 / 2000000000 : ℝ)) (b := (2626874209 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_143 :
    (2147271 / 10000000 : ℝ) ≤ Real.exp (-(15383873 / 10000000 : ℝ)) ∧
    Real.exp (-(15383873 / 10000000 : ℝ)) ≤ (268409 / 1250000 : ℝ) := by
  have hsmall : (655780581 / 625000000 : ℝ) ≤ Real.exp (15383873 / 320000000 : ℝ) ∧
      Real.exp (15383873 / 320000000 : ℝ) ≤ (10492489297 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (15383873 / 320000000 : ℝ))
    (a := (655780581 / 625000000 : ℝ)) (b := (10492489297 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_144 :
    (2799097 / 1000000 : ℝ) ≤ Real.exp (527 / 512 : ℝ) ∧
    Real.exp (527 / 512 : ℝ) ≤ (27990971 / 10000000 : ℝ) := by
  have hsmall : (20653768586621 / 20000000000000 : ℝ) ≤ Real.exp (527 / 16384 : ℝ) ∧
      Real.exp (527 / 16384 : ℝ) ≤ (51634421466553 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (527 / 16384 : ℝ))
    (a := (20653768586621 / 20000000000000 : ℝ)) (b := (51634421466553 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_145 :
    (7319617 / 10000000 : ℝ) ≤ Real.exp (-(20449 / 65536 : ℝ)) ∧
    Real.exp (-(20449 / 65536 : ℝ)) ≤ (3659809 / 5000000 : ℝ) := by
  have hsmall : (5048992687 / 5000000000 : ℝ) ≤ Real.exp (20449 / 2097152 : ℝ) ∧
      Real.exp (20449 / 2097152 : ℝ) ≤ (80783883 / 80000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (20449 / 2097152 : ℝ))
    (a := (5048992687 / 5000000000 : ℝ)) (b := (80783883 / 80000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_146 :
    (1858069 / 2500000 : ℝ) ≤ Real.exp (-(2431 / 8192 : ℝ)) ∧
    Real.exp (-(2431 / 8192 : ℝ)) ≤ (7432277 / 10000000 : ℝ) := by
  have hsmall : (5046583307 / 5000000000 : ℝ) ≤ Real.exp (2431 / 262144 : ℝ) ∧
      Real.exp (2431 / 262144 : ℝ) ≤ (2018633323 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2431 / 262144 : ℝ))
    (a := (5046583307 / 5000000000 : ℝ)) (b := (2018633323 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_147 :
    (15217469 / 2000000 : ℝ) ≤ Real.exp (1039 / 512 : ℝ) ∧
    Real.exp (1039 / 512 : ℝ) ≤ (38043673 / 5000000 : ℝ) := by
  have hsmall : (26636736974073 / 25000000000000 : ℝ) ≤ Real.exp (1039 / 16384 : ℝ) ∧
      Real.exp (1039 / 16384 : ℝ) ≤ (106546947896293 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1039 / 16384 : ℝ))
    (a := (26636736974073 / 25000000000000 : ℝ)) (b := (106546947896293 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_148 :
    (2147269 / 10000000 : ℝ) ≤ Real.exp (-(15383879 / 10000000 : ℝ)) ∧
    Real.exp (-(15383879 / 10000000 : ℝ)) ≤ (214727 / 1000000 : ℝ) := by
  have hsmall : (10492489493 / 10000000000 : ℝ) ≤ Real.exp (15383879 / 320000000 : ℝ) ∧
      Real.exp (15383879 / 320000000 : ℝ) ≤ (5246244747 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (15383879 / 320000000 : ℝ))
    (a := (10492489493 / 10000000000 : ℝ)) (b := (5246244747 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_149 :
    (1122397 / 5000000 : ℝ) ≤ Real.exp (-(233433 / 156250 : ℝ)) ∧
    Real.exp (-(233433 / 156250 : ℝ)) ≤ (448959 / 2000000 : ℝ) := by
  have hsmall : (10477935791 / 10000000000 : ℝ) ≤ Real.exp (233433 / 5000000 : ℝ) ∧
      Real.exp (233433 / 5000000 : ℝ) ≤ (654870987 / 625000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (233433 / 5000000 : ℝ))
    (a := (10477935791 / 10000000000 : ℝ)) (b := (654870987 / 625000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_150 :
    (13791967 / 5000000 : ℝ) ≤ Real.exp (1039 / 1024 : ℝ) ∧
    Real.exp (1039 / 1024 : ℝ) ≤ (5516787 / 2000000 : ℝ) := by
  have hsmall : (103221581026591 / 100000000000000 : ℝ) ≤ Real.exp (1039 / 32768 : ℝ) ∧
      Real.exp (1039 / 32768 : ℝ) ≤ (3225674407081 / 3125000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1039 / 32768 : ℝ))
    (a := (103221581026591 / 100000000000000 : ℝ)) (b := (3225674407081 / 3125000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_151 :
    (944583 / 1250000 : ℝ) ≤ Real.exp (-(73441 / 262144 : ℝ)) ∧
    Real.exp (-(73441 / 262144 : ℝ)) ≤ (1511333 / 2000000 : ℝ) := by
  have hsmall : (2521983213 / 2500000000 : ℝ) ≤ Real.exp (73441 / 8388608 : ℝ) ∧
      Real.exp (73441 / 8388608 : ℝ) ≤ (10087932853 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (73441 / 8388608 : ℝ))
    (a := (2521983213 / 2500000000 : ℝ)) (b := (10087932853 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_152 :
    (943607 / 1250000 : ℝ) ≤ Real.exp (-(4607 / 16384 : ℝ)) ∧
    Real.exp (-(4607 / 16384 : ℝ)) ≤ (7548857 / 10000000 : ℝ) := by
  have hsmall : (2017651751 / 2000000000 : ℝ) ≤ Real.exp (4607 / 524288 : ℝ) ∧
      Real.exp (4607 / 524288 : ℝ) ≤ (2522064689 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (4607 / 524288 : ℝ))
    (a := (2017651751 / 2000000000 : ℝ)) (b := (2522064689 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_153 :
    (115454 / 15625 : ℝ) ≤ Real.exp (2 / 1 : ℝ) ∧
    Real.exp (2 / 1 : ℝ) ≤ (73890561 / 10000000 : ℝ) := by
  have hsmall : (21289889178357 / 20000000000000 : ℝ) ≤ Real.exp (1 / 16 : ℝ) ∧
      Real.exp (1 / 16 : ℝ) ≤ (53224722945893 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1 / 16 : ℝ))
    (a := (21289889178357 / 20000000000000 : ℝ)) (b := (53224722945893 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_154 :
    (280599 / 1250000 : ℝ) ≤ Real.exp (-(7469859 / 5000000 : ℝ)) ∧
    Real.exp (-(7469859 / 5000000 : ℝ)) ≤ (2244793 / 10000000 : ℝ) := by
  have hsmall : (10477935987 / 10000000000 : ℝ) ≤ Real.exp (7469859 / 160000000 : ℝ) ∧
      Real.exp (7469859 / 160000000 : ℝ) ≤ (2619483997 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7469859 / 160000000 : ℝ))
    (a := (10477935987 / 10000000000 : ℝ)) (b := (2619483997 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_155 :
    (2343739 / 10000000 : ℝ) ≤ Real.exp (-(7254187 / 5000000 : ℝ)) ∧
    Real.exp (-(7254187 / 5000000 : ℝ)) ≤ (117187 / 500000 : ℝ) := by
  have hsmall : (1307977721 / 1250000000 : ℝ) ≤ Real.exp (7254187 / 160000000 : ℝ) ∧
      Real.exp (7254187 / 160000000 : ℝ) ≤ (10463821769 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7254187 / 160000000 : ℝ))
    (a := (1307977721 / 1250000000 : ℝ)) (b := (10463821769 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

theorem n1_exp_156 :
    (13591409 / 5000000 : ℝ) ≤ Real.exp (1 / 1 : ℝ) ∧
    Real.exp (1 / 1 : ℝ) ≤ (27182819 / 10000000 : ℝ) := by
  have hsmall : (10317434074991 / 10000000000000 : ℝ) ≤ Real.exp (1 / 32 : ℝ) ∧
      Real.exp (1 / 32 : ℝ) ≤ (103174340749911 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1 / 32 : ℝ))
    (a := (10317434074991 / 10000000000000 : ℝ)) (b := (103174340749911 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)

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

theorem n1_exp_158 :
    (1533453 / 2000000 : ℝ) ≤ Real.exp (-(17 / 64 : ℝ)) ∧
    Real.exp (-(17 / 64 : ℝ)) ≤ (3833633 / 5000000 : ℝ) := by
  have hsmall : (5041676641 / 5000000000 : ℝ) ≤ Real.exp (17 / 2048 : ℝ) ∧
      Real.exp (17 / 2048 : ℝ) ≤ (10083353283 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (17 / 2048 : ℝ))
    (a := (5041676641 / 5000000000 : ℝ)) (b := (10083353283 / 10000000000 : ℝ))
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
theorem cell_000 (x : ℝ) (hx : x ∈ Set.Ioo (-4 / 1 : ℝ) (-17 / 8 : ℝ)) :
    density x ≤ (3 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (1570953301 / 5000000 : ℝ) ≤ Real.exp (-2 * (x - 3 / 4)) ∧
      Real.exp (-2 * (x - 3 / 4)) ≤ (133597268297 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_000.1 n1_exp_001.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1570953301 / 5000000 : ℝ)) pi_rational_enclosure hi
  have ha : (61691179 / 1000000 : ℝ) ≤ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ∧ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ≤ (13115882591 / 5000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (0 / 1 : ℝ) ≤ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (1 / 1048576 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_002.1 n1_exp_003.2
  have hpoly : (-1 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (3 / 3125000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (0 / 1 : ℝ))
      (by norm_num : (1 / 1048576 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have hpref : (177254241 / 10000000 : ℝ) ≤ Real.exp (-(x - 3 / 4)) ∧
      Real.exp (-(x - 3 / 4)) ≤ (577921423 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -(x - 3 / 4))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_004.1 n1_exp_005.2
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_reflected 6 (x - 3 / 4) (by linarith only [hx.2])
  have ht : (-29 / 25000000 : ℝ) ≤ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ∧ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ≤ (11097 / 100000000 : ℝ) := by
    exact nonneg_left_product_enclosure (by norm_num : (0 : ℝ) ≤ (177254241 / 10000000 : ℝ)) hpref hpoly
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-17 / 8 : ℝ))
    (show -(-17 / 8 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-4 / 1 : ℝ) by linarith only [hx.1]) 2
  have hpe : (0 / 1 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (1 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_006.1 n1_exp_007.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (0 / 1 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (0 / 1 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (3 / 25000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (1045791 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_008.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))))
    (0 / 1 : ℝ) (3 / 25000000 : ℝ) (-29 / 25000000 : ℝ) (11097 / 100000000 : ℝ)
    (8101 / 50000000 : ℝ) (1045791 / 10000000 : ℝ) (3 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_001 (x : ℝ) (hx : x ∈ Set.Ioo (-17 / 8 : ℝ) (-19 / 16 : ℝ)) :
    density x ≤ (131 / 25000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (240913491 / 5000000 : ℝ) ≤ Real.exp (-2 * (x - 3 / 4)) ∧
      Real.exp (-2 * (x - 3 / 4)) ≤ (3141906603 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_009.1 n1_exp_000.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (240913491 / 5000000 : ℝ)) pi_rational_enclosure hi
  have ha : (94606487 / 10000000 : ℝ) ≤ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ∧ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ≤ (616911987 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (0 / 1 : ℝ) ≤ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (779 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_010.1 n1_exp_011.2
  have hpoly : (-1 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (7791 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (0 / 1 : ℝ))
      (by norm_num : (779 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have hpref : (34706879 / 5000000 : ℝ) ≤ Real.exp (-(x - 3 / 4)) ∧
      Real.exp (-(x - 3 / 4)) ≤ (88627121 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -(x - 3 / 4))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_012.1 n1_exp_004.2
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_reflected 6 (x - 3 / 4) (by linarith only [hx.2])
  have ht : (-9 / 50000000 : ℝ) ≤ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ∧ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ≤ (138099 / 100000000 : ℝ) := by
    exact nonneg_left_product_enclosure (by norm_num : (0 : ℝ) ≤ (34706879 / 5000000 : ℝ)) hpref hpoly
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-19 / 16 : ℝ))
    (show -(-19 / 16 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-17 / 8 : ℝ) by linarith only [hx.1]) 2
  have hpe : (0 / 1 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (35507 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_007.1 n1_exp_013.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (0 / 1 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (0 / 1 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (200327 / 50000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (283167 / 1000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_014.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))))
    (0 / 1 : ℝ) (200327 / 50000000 : ℝ) (-9 / 50000000 : ℝ) (138099 / 100000000 : ℝ)
    (400681 / 100000000 : ℝ) (283167 / 1000000 : ℝ) (131 / 25000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_002 (x : ℝ) (hx : x ∈ Set.Ioo (-19 / 16 : ℝ) (-61 / 64 : ℝ)) :
    density x ≤ (31559 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (301519621 / 10000000 : ℝ) ≤ Real.exp (-2 * (x - 3 / 4)) ∧
      Real.exp (-2 * (x - 3 / 4)) ≤ (481826983 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_015.1 n1_exp_009.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (301519621 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (29601613 / 5000000 : ℝ) ≤ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ∧ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ≤ (47303259 / 5000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (389 / 5000000 : ℝ) ≤ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (6711 / 2500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_016.1 n1_exp_017.2
  have hpoly : (7779 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (6711 / 2500000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (389 / 5000000 : ℝ))
      (by norm_num : (6711 / 2500000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have hpref : (27455401 / 5000000 : ℝ) ≤ Real.exp (-(x - 3 / 4)) ∧
      Real.exp (-(x - 3 / 4)) ≤ (69413759 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -(x - 3 / 4))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_018.1 n1_exp_012.2
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_reflected 6 (x - 3 / 4) (by linarith only [hx.2])
  have ht : (8543 / 20000000 : ℝ) ≤ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ∧ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ≤ (1863343 / 100000000 : ℝ) := by
    exact nonneg_left_product_enclosure (by norm_num : (0 : ℝ) ≤ (27455401 / 5000000 : ℝ)) hpref hpoly
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-61 / 64 : ℝ))
    (show -(-61 / 64 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-19 / 16 : ℝ) by linarith only [hx.1]) 2
  have hpe : (17753 / 5000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (1651 / 62500 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_013.1 n1_exp_019.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (17753 / 5000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (200321 / 50000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (2980729 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (3632387 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_020.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))))
    (200321 / 50000000 : ℝ) (2980729 / 100000000 : ℝ) (8543 / 20000000 : ℝ) (1863343 / 100000000 : ℝ)
    (1459183 / 50000000 : ℝ) (3632387 / 10000000 : ℝ) (31559 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_003 (x : ℝ) (hx : x ∈ Set.Ioo (-61 / 64 : ℝ) (-107 / 128 : ℝ)) :
    density x ≤ (25817 / 25000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (59630413 / 2500000 : ℝ) ≤ Real.exp (-2 * (x - 3 / 4)) ∧
      Real.exp (-2 * (x - 3 / 4)) ≤ (150759811 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_021.1 n1_exp_015.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (59630413 / 2500000 : ℝ)) pi_rational_enclosure hi
  have ha : (46833607 / 10000000 : ℝ) ≤ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ∧ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ≤ (29601623 / 5000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (26843 / 10000000 : ℝ) ≤ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (92479 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_022.1 n1_exp_023.2
  have hpoly : (67107 / 25000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (92479 / 10000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (26843 / 10000000 : ℝ))
      (by norm_num : (92479 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have hpref : (24419339 / 5000000 : ℝ) ≤ Real.exp (-(x - 3 / 4)) ∧
      Real.exp (-(x - 3 / 4)) ≤ (54910803 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -(x - 3 / 4))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_024.1 n1_exp_018.2
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_reflected 6 (x - 3 / 4) (by linarith only [hx.2])
  have ht : (655483 / 50000000 : ℝ) ≤ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ∧ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ≤ (5078097 / 100000000 : ℝ) := by
    exact nonneg_left_product_enclosure (by norm_num : (0 : ℝ) ≤ (24419339 / 5000000 : ℝ)) hpref hpoly
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-107 / 128 : ℝ))
    (show -(-107 / 128 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-61 / 64 : ℝ) by linarith only [hx.1]) 2
  have hpe : (264159 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (76381 / 1250000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_019.1 n1_exp_025.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (264159 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (1490357 / 50000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (215467 / 3125000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (514253 / 1250000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_026.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))))
    (1490357 / 50000000 : ℝ) (215467 / 3125000 : ℝ) (655483 / 50000000 : ℝ) (5078097 / 100000000 : ℝ)
    (2490467 / 50000000 : ℝ) (514253 / 1250000 : ℝ) (25817 / 25000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_004 (x : ℝ) (hx : x ∈ Set.Ioo (-107 / 128 : ℝ) (-199 / 256 : ℝ)) :
    density x ≤ (38663 / 50000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (212145549 / 10000000 : ℝ) ≤ Real.exp (-2 * (x - 3 / 4)) ∧
      Real.exp (-2 * (x - 3 / 4)) ≤ (238521653 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_027.1 n1_exp_021.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (212145549 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (2603417 / 625000 : ℝ) ≤ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ∧ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ≤ (46833623 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (46239 / 5000000 : ℝ) ≤ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (6209 / 400000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_028.1 n1_exp_029.2
  have hpoly : (28899 / 3125000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (1552249 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (46239 / 5000000 : ℝ))
      (by norm_num : (6209 / 400000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have hpref : (2302963 / 500000 : ℝ) ≤ Real.exp (-(x - 3 / 4)) ∧
      Real.exp (-(x - 3 / 4)) ≤ (48838679 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -(x - 3 / 4))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_030.1 n1_exp_024.2
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_reflected 6 (x - 3 / 4) (by linarith only [hx.2])
  have ht : (1064853 / 25000000 : ℝ) ≤ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ∧ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ≤ (379049 / 5000000 : ℝ) := by
    exact nonneg_left_product_enclosure (by norm_num : (0 : ℝ) ≤ (2302963 / 500000 : ℝ)) hpref hpoly
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-199 / 256 : ℝ))
    (show -(-199 / 256 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-107 / 128 : ℝ) by linarith only [hx.1]) 2
  have hpe : (611047 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (891841 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_025.1 n1_exp_031.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (611047 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (3447463 / 50000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (2515839 / 25000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (4378287 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_032.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))))
    (3447463 / 50000000 : ℝ) (2515839 / 25000000 : ℝ) (1064853 / 25000000 : ℝ) (379049 / 5000000 : ℝ)
    (834661 / 20000000 : ℝ) (4378287 / 10000000 : ℝ) (38663 / 50000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_005 (x : ℝ) (hx : x ∈ Set.Ioo (-199 / 256 : ℝ) (-23 / 32 : ℝ)) :
    density x ≤ (24693 / 12500000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (188686157 / 10000000 : ℝ) ≤ Real.exp (-2 * (x - 3 / 4)) ∧
      Real.exp (-2 * (x - 3 / 4)) ≤ (4242911 / 200000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_033.1 n1_exp_027.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (188686157 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (2315527 / 625000 : ℝ) ≤ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ∧ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ≤ (20827343 / 5000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (19403 / 1250000 : ℝ) ≤ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (246041 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_034.1 n1_exp_035.2
  have hpoly : (776083 / 50000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (2460399 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (19403 / 1250000 : ℝ))
      (by norm_num : (246041 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have hpref : (43438019 / 10000000 : ℝ) ≤ Real.exp (-(x - 3 / 4)) ∧
      Real.exp (-(x - 3 / 4)) ≤ (46059261 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -(x - 3 / 4))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_036.1 n1_exp_030.2
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_reflected 6 (x - 3 / 4) (by linarith only [hx.2])
  have ht : (6742301 / 100000000 : ℝ) ≤ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ∧ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ≤ (177069 / 1562500 : ℝ) := by
    exact nonneg_left_product_enclosure (by norm_num : (0 : ℝ) ≤ (43438019 / 10000000 : ℝ)) hpref hpoly
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-23 / 32 : ℝ))
    (show -(-23 / 32 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-199 / 256 : ℝ) by linarith only [hx.1]) 2
  have hpe : (2787 / 31250 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (1266401 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_031.1 n1_exp_037.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (2787 / 31250 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (2012667 / 20000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (1786227 / 12500000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (1164881 / 2500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_038.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))))
    (2012667 / 20000000 : ℝ) (1786227 / 12500000 : ℝ) (6742301 / 100000000 : ℝ) (177069 / 1562500 : ℝ)
    (6481993 / 100000000 : ℝ) (1164881 / 2500000 : ℝ) (24693 / 12500000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_006 (x : ℝ) (hx : x ∈ Set.Ioo (-23 / 32 : ℝ) (-169 / 256 : ℝ)) :
    density x ≤ (42371 / 10000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (83910471 / 5000000 : ℝ) ≤ Real.exp (-2 * (x - 3 / 4)) ∧
      Real.exp (-2 * (x - 3 / 4)) ≤ (94343079 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_039.1 n1_exp_033.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (83910471 / 5000000 : ℝ)) pi_rational_enclosure hi
  have ha : (16475779 / 5000000 : ℝ) ≤ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ∧ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ≤ (7409689 / 2000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (6151 / 250000 : ℝ) ≤ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (370623 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_040.1 n1_exp_041.2
  have hpoly : (1230011 / 50000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (3706157 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (6151 / 250000 : ℝ))
      (by norm_num : (370623 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have hpref : (20482977 / 5000000 : ℝ) ≤ Real.exp (-(x - 3 / 4)) ∧
      Real.exp (-(x - 3 / 4)) ≤ (2171901 / 500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -(x - 3 / 4))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_042.1 n1_exp_036.2
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_reflected 6 (x - 3 / 4) (by linarith only [hx.2])
  have ht : (5038857 / 50000000 : ℝ) ≤ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ∧ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ≤ (16098813 / 100000000 : ℝ) := by
    exact nonneg_left_product_enclosure (by norm_num : (0 : ℝ) ≤ (20482977 / 5000000 : ℝ)) hpref hpoly
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-169 / 256 : ℝ))
    (show -(-169 / 256 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-23 / 32 : ℝ) by linarith only [hx.1]) 2
  have hpe : (1583 / 12500 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (1749553 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_037.1 n1_exp_043.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1583 / 12500 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (14289791 / 100000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (19741607 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (4958827 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_044.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))))
    (14289791 / 100000000 : ℝ) (19741607 / 100000000 : ℝ) (5038857 / 50000000 : ℝ) (16098813 / 100000000 : ℝ)
    (2303619 / 25000000 : ℝ) (4958827 / 10000000 : ℝ) (42371 / 10000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_007 (x : ℝ) (hx : x ∈ Set.Ioo (-169 / 256 : ℝ) (-323 / 512 : ℝ)) :
    density x ≤ (252437 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (79135111 / 5000000 : ℝ) ≤ Real.exp (-2 * (x - 3 / 4)) ∧
      Real.exp (-2 * (x - 3 / 4)) ≤ (167820943 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_045.1 n1_exp_039.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (79135111 / 5000000 : ℝ)) pi_rational_enclosure hi
  have ha : (15538139 / 5000000 : ℝ) ≤ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ∧ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ≤ (32951569 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (185311 / 5000000 : ℝ) ≤ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (447069 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_046.1 n1_exp_047.2
  have hpoly : (3705421 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (4470313 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (185311 / 5000000 : ℝ))
      (by norm_num : (447069 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have hpref : (3978319 / 1000000 : ℝ) ≤ Real.exp (-(x - 3 / 4)) ∧
      Real.exp (-(x - 3 / 4)) ≤ (8193191 / 2000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -(x - 3 / 4))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_048.1 n1_exp_042.2
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_reflected 6 (x - 3 / 4) (by linarith only [hx.2])
  have ht : (7370673 / 50000000 : ℝ) ≤ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ∧ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ≤ (3662613 / 20000000 : ℝ) := by
    exact nonneg_left_product_enclosure (by norm_num : (0 : ℝ) ≤ (3978319 / 1000000 : ℝ)) hpref hpoly
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-323 / 512 : ℝ))
    (show -(-323 / 512 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-169 / 256 : ℝ) by linarith only [hx.1]) 2
  have hpe : (109347 / 625000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (508829 / 2500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_043.1 n1_exp_049.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (109347 / 625000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (19741577 / 100000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (22966099 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (1278903 / 2500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_050.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))))
    (19741577 / 100000000 : ℝ) (22966099 / 100000000 : ℝ) (7370673 / 50000000 : ℝ) (3662613 / 20000000 : ℝ)
    (3497749 / 50000000 : ℝ) (1278903 / 2500000 : ℝ) (252437 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_008 (x : ℝ) (hx : x ∈ Set.Ioo (-323 / 512 : ℝ) (-77 / 128 : ℝ)) :
    density x ≤ (17097 / 5000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (37315759 / 2500000 : ℝ) ≤ Real.exp (-2 * (x - 3 / 4)) ∧
      Real.exp (-2 * (x - 3 / 4)) ≤ (158270223 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_051.1 n1_exp_045.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (37315759 / 2500000 : ℝ)) pi_rational_enclosure hi
  have ha : (14653861 / 5000000 : ℝ) ≤ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ∧ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ≤ (3107629 / 1000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (111767 / 2500000 : ℝ) ≤ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (533559 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_052.1 n1_exp_053.2
  have hpoly : (4469059 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (666849 / 12500000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (111767 / 2500000 : ℝ))
      (by norm_num : (533559 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have hpref : (19317287 / 5000000 : ℝ) ≤ Real.exp (-(x - 3 / 4)) ∧
      Real.exp (-(x - 3 / 4)) ≤ (39783191 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -(x - 3 / 4))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_054.1 n1_exp_048.2
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_reflected 6 (x - 3 / 4) (by linarith only [hx.2])
  have ht : (17266019 / 100000000 : ℝ) ≤ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ∧ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ≤ (4244701 / 20000000 : ℝ) := by
    exact nonneg_left_product_enclosure (by norm_num : (0 : ℝ) ≤ (19317287 / 5000000 : ℝ)) hpref hpoly
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-77 / 128 : ℝ))
    (show -(-77 / 128 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-323 / 512 : ℝ) by linarith only [hx.1]) 2
  have hpe : (407063 / 2000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (36743 / 156250 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_049.1 n1_exp_055.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (407063 / 2000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (22966067 / 100000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (26534443 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (1055471 / 2000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_056.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))))
    (22966067 / 100000000 : ℝ) (26534443 / 100000000 : ℝ) (17266019 / 100000000 : ℝ) (4244701 / 20000000 : ℝ)
    (8020251 / 100000000 : ℝ) (1055471 / 2000000 : ℝ) (17097 / 5000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_009 (x : ℝ) (hx : x ∈ Set.Ioo (-77 / 128 : ℝ) (-293 / 512 : ℝ)) :
    density x ≤ (8907 / 2000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (2815369 / 200000 : ℝ) ≤ Real.exp (-2 * (x - 3 / 4)) ∧
      Real.exp (-2 * (x - 3 / 4)) ≤ (149263037 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_057.1 n1_exp_051.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (2815369 / 200000 : ℝ)) pi_rational_enclosure hi
  have ha : (13819907 / 5000000 : ℝ) ≤ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ∧ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ≤ (29307733 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (533557 / 10000000 : ℝ) ≤ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (630403 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_058.1 n1_exp_059.2
  have hpoly : (5332411 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (630241 / 10000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (533557 / 10000000 : ℝ))
      (by norm_num : (630403 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have hpref : (37519121 / 10000000 : ℝ) ≤ Real.exp (-(x - 3 / 4)) ∧
      Real.exp (-(x - 3 / 4)) ≤ (1545383 / 400000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -(x - 3 / 4))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_060.1 n1_exp_054.2
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_reflected 6 (x - 3 / 4) (by linarith only [hx.2])
  have ht : (20006737 / 100000000 : ℝ) ≤ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ∧ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ≤ (12174547 / 50000000 : ℝ) := by
    exact nonneg_left_product_enclosure (by norm_num : (0 : ℝ) ≤ (37519121 / 10000000 : ℝ)) hpref hpoly
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-293 / 512 : ℝ))
    (show -(-293 / 512 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-77 / 128 : ℝ) by linarith only [hx.1]) 2
  have hpe : (2351551 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (2698331 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_055.1 n1_exp_061.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (2351551 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (26534407 / 100000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (7611857 / 25000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (1361053 / 2500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_062.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))))
    (26534407 / 100000000 : ℝ) (7611857 / 25000000 : ℝ) (20006737 / 100000000 : ℝ) (12174547 / 50000000 : ℝ)
    (9015271 / 100000000 : ℝ) (1361053 / 2500000 : ℝ) (8907 / 2000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_010 (x : ℝ) (hx : x ∈ Set.Ioo (-293 / 512 : ℝ) (-139 / 256 : ℝ)) :
    density x ≤ (111857 / 20000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (33189323 / 2500000 : ℝ) ≤ Real.exp (-2 * (x - 3 / 4)) ∧
      Real.exp (-2 * (x - 3 / 4)) ≤ (140768451 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_063.1 n1_exp_057.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (33189323 / 2500000 : ℝ)) pi_rational_enclosure hi
  have ha : (26066827 / 10000000 : ℝ) ≤ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ∧ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ≤ (1727489 / 625000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (315201 / 5000000 : ℝ) ≤ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (737789 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_064.1 n1_exp_065.2
  have hpoly : (3149047 / 50000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (1843683 / 25000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (315201 / 5000000 : ℝ))
      (by norm_num : (737789 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have hpref : (18217937 / 5000000 : ℝ) ≤ Real.exp (-(x - 3 / 4)) ∧
      Real.exp (-(x - 3 / 4)) ≤ (18759561 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -(x - 3 / 4))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_066.1 n1_exp_060.2
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_reflected 6 (x - 3 / 4) (by linarith only [hx.2])
  have ht : (4589531 / 20000000 : ℝ) ≤ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ∧ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ≤ (27669347 / 100000000 : ℝ) := by
    exact nonneg_left_product_enclosure (by norm_num : (0 : ℝ) ≤ (18217937 / 5000000 : ℝ)) hpref hpoly
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-139 / 256 : ℝ))
    (show -(-139 / 256 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-293 / 512 : ℝ) by linarith only [hx.1]) 2
  have hpe : (269833 / 1000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (1537531 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_061.1 n1_exp_067.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (269833 / 1000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (30447389 / 100000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (6939677 / 20000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (702043 / 1250000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_068.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))))
    (30447389 / 100000000 : ℝ) (6939677 / 20000000 : ℝ) (4589531 / 20000000 : ℝ) (27669347 / 100000000 : ℝ)
    (4974929 / 50000000 : ℝ) (702043 / 1250000 : ℝ) (111857 / 20000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_011 (x : ℝ) (hx : x ∈ Set.Ioo (-139 / 256 : ℝ) (-263 / 512 : ℝ)) :
    density x ≤ (67873 / 10000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (125202051 / 10000000 : ℝ) ≤ Real.exp (-2 * (x - 3 / 4)) ∧
      Real.exp (-2 * (x - 3 / 4)) ≤ (132757293 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_069.1 n1_exp_063.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (125202051 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (76823 / 31250 : ℝ) ≤ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ∧ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ≤ (26066837 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (184447 / 2500000 : ℝ) ≤ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (855773 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_070.1 n1_exp_071.2
  have hpoly : (7367153 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (1710361 / 20000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (184447 / 2500000 : ℝ))
      (by norm_num : (855773 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have hpref : (35383901 / 10000000 : ℝ) ≤ Real.exp (-(x - 3 / 4)) ∧
      Real.exp (-(x - 3 / 4)) ≤ (291487 / 80000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -(x - 3 / 4))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_072.1 n1_exp_066.2
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_reflected 6 (x - 3 / 4) (by linarith only [hx.2])
  have ht : (26067861 / 100000000 : ℝ) ≤ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ∧ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ≤ (124637 / 400000 : ℝ) := by
    exact nonneg_left_product_enclosure (by norm_num : (0 : ℝ) ≤ (35383901 / 10000000 : ℝ)) hpref hpoly
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-263 / 512 : ℝ))
    (show -(-263 / 512 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-139 / 256 : ℝ) by linarith only [hx.1]) 2
  have hpe : (3075061 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (348041 / 1000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_067.1 n1_exp_073.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (3075061 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (17349171 / 50000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (39272251 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (2896959 / 5000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_074.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))))
    (17349171 / 50000000 : ℝ) (39272251 / 100000000 : ℝ) (26067861 / 100000000 : ℝ) (124637 / 400000 : ℝ)
    (10794163 / 100000000 : ℝ) (2896959 / 5000000 : ℝ) (67873 / 10000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_012 (x : ℝ) (hx : x ∈ Set.Ioo (-263 / 512 : ℝ) (-31 / 64 : ℝ)) :
    density x ≤ (99669 / 12500000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (5903839 / 500000 : ℝ) ≤ Real.exp (-2 * (x - 3 / 4)) ∧
      Real.exp (-2 * (x - 3 / 4)) ≤ (31300513 / 2500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_075.1 n1_exp_069.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (5903839 / 500000 : ℝ)) pi_rational_enclosure hi
  have ha : (5796079 / 2500000 : ℝ) ≤ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ∧ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ≤ (24583369 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (855771 / 10000000 : ℝ) ≤ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (984279 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_076.1 n1_exp_077.2
  have hpoly : (4269469 / 50000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (76813 / 781250 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (855771 / 10000000 : ℝ))
      (by norm_num : (984279 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have hpref : (17181151 / 5000000 : ℝ) ≤ Real.exp (-(x - 3 / 4)) ∧
      Real.exp (-(x - 3 / 4)) ≤ (17691951 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -(x - 3 / 4))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_078.1 n1_exp_072.2
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_reflected 6 (x - 3 / 4) (by linarith only [hx.2])
  have ht : (7335439 / 25000000 : ℝ) ≤ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ∧ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ≤ (34789679 / 100000000 : ℝ) := by
    exact nonneg_left_product_enclosure (by norm_num : (0 : ℝ) ≤ (17181151 / 5000000 : ℝ)) hpref hpoly
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-31 / 64 : ℝ))
    (show -(-31 / 64 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-263 / 512 : ℝ) by linarith only [hx.1]) 2
  have hpe : (3480409 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (1956117 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_073.1 n1_exp_079.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (3480409 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (9818051 / 25000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (44144867 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (5977107 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_080.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))))
    (9818051 / 25000000 : ℝ) (44144867 / 100000000 : ℝ) (7335439 / 25000000 : ℝ) (34789679 / 100000000 : ℝ)
    (1440091 / 12500000 : ℝ) (5977107 / 10000000 : ℝ) (99669 / 12500000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_013 (x : ℝ) (hx : x ∈ Set.Ioo (-31 / 64 : ℝ) (-233 / 512 : ℝ)) :
    density x ≤ (454017 / 50000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (111357009 / 10000000 : ℝ) ≤ Real.exp (-2 * (x - 3 / 4)) ∧
      Real.exp (-2 * (x - 3 / 4)) ≤ (118076781 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_081.1 n1_exp_075.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (111357009 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (21864893 / 10000000 : ℝ) ≤ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ∧ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ≤ (927373 / 400000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (984277 / 10000000 : ℝ) ≤ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (35097 / 312500 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_082.1 n1_exp_083.2
  have hpoly : (9810949 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (11212269 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (984277 / 10000000 : ℝ))
      (by norm_num : (35097 / 312500 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have hpref : (33370197 / 10000000 : ℝ) ≤ Real.exp (-(x - 3 / 4)) ∧
      Real.exp (-(x - 3 / 4)) ≤ (34362303 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -(x - 3 / 4))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_084.1 n1_exp_078.2
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_reflected 6 (x - 3 / 4) (by linarith only [hx.2])
  have ht : (3273933 / 10000000 : ℝ) ≤ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ∧ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ≤ (38527939 / 100000000 : ℝ) := by
    exact nonneg_left_product_enclosure (by norm_num : (0 : ℝ) ≤ (33370197 / 10000000 : ℝ)) hpref hpoly
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-233 / 512 : ℝ))
    (show -(-233 / 512 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-31 / 64 : ℝ) by linarith only [hx.1]) 2
  have hpe : (3912233 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (545943 / 1250000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_079.1 n1_exp_085.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (3912233 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (8828963 / 20000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (49282493 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (770761 / 1250000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_086.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))))
    (8828963 / 20000000 : ℝ) (49282493 / 100000000 : ℝ) (3273933 / 10000000 : ℝ) (38527939 / 100000000 : ℝ)
    (1513247 / 12500000 : ℝ) (770761 / 1250000 : ℝ) (454017 / 50000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_014 (x : ℝ) (hx : x ∈ Set.Ioo (-233 / 512 : ℝ) (-109 / 256 : ℝ)) :
    density x ≤ (20071 / 2000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (52509831 / 5000000 : ℝ) ≤ Real.exp (-2 * (x - 3 / 4)) ∧
      Real.exp (-2 * (x - 3 / 4)) ≤ (11135701 / 1000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_087.1 n1_exp_081.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (52509831 / 5000000 : ℝ)) pi_rational_enclosure hi
  have ha : (10310279 / 5000000 : ℝ) ≤ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ∧ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ≤ (21864901 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (561551 / 5000000 : ℝ) ≤ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (1271923 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_088.1 n1_exp_089.2
  have hpoly : (447147 / 4000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (12687411 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (561551 / 5000000 : ℝ))
      (by norm_num : (1271923 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have hpref : (32406737 / 10000000 : ℝ) ≤ Real.exp (-(x - 3 / 4)) ∧
      Real.exp (-(x - 3 / 4)) ≤ (16685099 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -(x - 3 / 4))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_090.1 n1_exp_084.2
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_reflected 6 (x - 3 / 4) (by linarith only [hx.2])
  have ht : (18113219 / 50000000 : ℝ) ≤ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ∧ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ≤ (21169071 / 50000000 : ℝ) := by
    exact nonneg_left_product_enclosure (by norm_num : (0 : ℝ) ≤ (32406737 / 10000000 : ℝ)) hpref hpoly
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-109 / 256 : ℝ))
    (show -(-109 / 256 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-233 / 512 : ℝ) by linarith only [hx.1]) 2
  have hpe : (4367543 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (2421239 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_085.1 n1_exp_091.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (4367543 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (24641219 / 50000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (27320777 / 50000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (1272209 / 2000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_092.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))))
    (24641219 / 50000000 : ℝ) (27320777 / 50000000 : ℝ) (18113219 / 50000000 : ℝ) (21169071 / 50000000 : ℝ)
    (401 / 3200 : ℝ) (1272209 / 2000000 : ℝ) (20071 / 2000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_015 (x : ℝ) (hx : x ∈ Set.Ioo (-109 / 256 : ℝ) (-203 / 512 : ℝ)) :
    density x ≤ (538653 / 50000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (49521487 / 5000000 : ℝ) ≤ Real.exp (-2 * (x - 3 / 4)) ∧
      Real.exp (-2 * (x - 3 / 4)) ≤ (105019663 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_093.1 n1_exp_087.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (49521487 / 5000000 : ℝ)) pi_rational_enclosure hi
  have ha : (9723519 / 5000000 : ℝ) ≤ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ∧ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ≤ (4124113 / 2000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (1271921 / 10000000 : ℝ) ≤ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (178787 / 1250000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_094.1 n1_exp_095.2
  have hpoly : (12635509 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (14250619 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (1271921 / 10000000 : ℝ))
      (by norm_num : (178787 / 1250000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have hpref : (31471093 / 10000000 : ℝ) ≤ Real.exp (-(x - 3 / 4)) ∧
      Real.exp (-(x - 3 / 4)) ≤ (16203369 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -(x - 3 / 4))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_096.1 n1_exp_090.2
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_reflected 6 (x - 3 / 4) (by linarith only [hx.2])
  have ht : (39765327 / 100000000 : ℝ) ≤ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ∧ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ≤ (5772701 / 12500000 : ℝ) := by
    exact nonneg_left_product_enclosure (by norm_num : (0 : ℝ) ≤ (31471093 / 10000000 : ℝ)) hpref hpoly
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-203 / 512 : ℝ))
    (show -(-203 / 512 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-109 / 256 : ℝ) by linarith only [hx.1]) 2
  have hpe : (4842477 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (1333079 / 2500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_091.1 n1_exp_097.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (4842477 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (54641493 / 100000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (15042197 / 25000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (1312433 / 2000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_098.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))))
    (54641493 / 100000000 : ℝ) (15042197 / 25000000 : ℝ) (39765327 / 100000000 : ℝ) (5772701 / 12500000 : ℝ)
    (2556731 / 20000000 : ℝ) (1312433 / 2000000 : ℝ) (538653 / 50000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_016 (x : ℝ) (hx : x ∈ Set.Ioo (-203 / 512 : ℝ) (-391 / 1024 : ℝ)) :
    density x ≤ (3367 / 625000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (96183417 / 10000000 : ℝ) ≤ Real.exp (-2 * (x - 3 / 4)) ∧
      Real.exp (-2 * (x - 3 / 4)) ≤ (3961719 / 400000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_099.1 n1_exp_093.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (96183417 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (3777113 / 2000000 : ℝ) ≤ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ∧ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ≤ (3889409 / 2000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (715147 / 5000000 : ℝ) ≤ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (1512901 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_100.1 n1_exp_101.2
  have hpoly : (3549541 / 25000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (7522657 / 50000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (715147 / 5000000 : ℝ))
      (by norm_num : (1512901 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have hpref : (31013451 / 10000000 : ℝ) ≤ Real.exp (-(x - 3 / 4)) ∧
      Real.exp (-(x - 3 / 4)) ≤ (15735547 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -(x - 3 / 4))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_102.1 n1_exp_096.2
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_reflected 6 (x - 3 / 4) (by linarith only [hx.2])
  have ht : (22016703 / 50000000 : ℝ) ≤ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ∧ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ≤ (189397 / 400000 : ℝ) := by
    exact nonneg_left_product_enclosure (by norm_num : (0 : ℝ) ≤ (31013451 / 10000000 : ℝ)) hpref hpoly
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-391 / 1024 : ℝ))
    (show -(-391 / 1024 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-203 / 512 : ℝ) by linarith only [hx.1]) 2
  have hpe : (1066463 / 2000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (44649 / 80000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_097.1 n1_exp_103.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1066463 / 2000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (30084361 / 50000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (62976299 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (6665097 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_104.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))))
    (30084361 / 50000000 : ℝ) (62976299 / 100000000 : ℝ) (22016703 / 50000000 : ℝ) (189397 / 400000 : ℝ)
    (8961183 / 100000000 : ℝ) (6665097 / 10000000 : ℝ) (3367 / 625000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_017 (x : ℝ) (hx : x ∈ Set.Ioo (-391 / 1024 : ℝ) (-47 / 128 : ℝ)) :
    density x ≤ (538773 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (93406421 / 10000000 : ℝ) ≤ Real.exp (-2 * (x - 3 / 4)) ∧
      Real.exp (-2 * (x - 3 / 4)) ≤ (48091709 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_105.1 n1_exp_099.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (93406421 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (1146269 / 625000 : ℝ) ≤ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ∧ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ≤ (18885573 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (1512899 / 10000000 : ℝ) ≤ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (399421 / 2500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_106.1 n1_exp_107.2
  have hpoly : (14998679 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (15872069 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (1512899 / 10000000 : ℝ))
      (by norm_num : (399421 / 2500000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have hpref : (955077 / 312500 : ℝ) ≤ Real.exp (-(x - 3 / 4)) ∧
      Real.exp (-(x - 3 / 4)) ≤ (7753363 / 2500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -(x - 3 / 4))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_108.1 n1_exp_102.2
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_reflected 6 (x - 3 / 4) (by linarith only [hx.2])
  have ht : (22919829 / 50000000 : ℝ) ≤ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ∧ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ≤ (24612383 / 50000000 : ℝ) := by
    exact nonneg_left_product_enclosure (by norm_num : (0 : ℝ) ≤ (955077 / 312500 : ℝ)) hpref hpoly
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-47 / 128 : ℝ))
    (show -(-47 / 128 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-391 / 1024 : ℝ) by linarith only [hx.1]) 2
  have hpe : (1395281 / 2500000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (233261 / 400000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_103.1 n1_exp_109.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1395281 / 2500000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (62976231 / 100000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (32900881 / 50000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (1692411 / 2500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_110.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))))
    (62976231 / 100000000 : ℝ) (32900881 / 50000000 : ℝ) (22919829 / 50000000 : ℝ) (24612383 / 50000000 : ℝ)
    (1111491 / 12500000 : ℝ) (1692411 / 2500000 : ℝ) (538773 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_018 (x : ℝ) (hx : x ∈ Set.Ioo (-47 / 128 : ℝ) (-361 / 1024 : ℝ)) :
    density x ≤ (534081 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (45354801 / 5000000 : ℝ) ≤ Real.exp (-2 * (x - 3 / 4)) ∧
      Real.exp (-2 * (x - 3 / 4)) ≤ (46703211 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_111.1 n1_exp_105.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (45354801 / 5000000 : ℝ)) pi_rational_enclosure hi
  have ha : (556587 / 312500 : ℝ) ≤ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ∧ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ≤ (18340311 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (798841 / 5000000 : ℝ) ≤ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (421141 / 2500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_112.1 n1_exp_113.2
  have hpoly : (15815769 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (16715337 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (798841 / 5000000 : ℝ))
      (by norm_num : (421141 / 2500000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have hpref : (15059017 / 5000000 : ℝ) ≤ Real.exp (-(x - 3 / 4)) ∧
      Real.exp (-(x - 3 / 4)) ≤ (6112493 / 2000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -(x - 3 / 4))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_114.1 n1_exp_108.2
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_reflected 6 (x - 3 / 4) (by linarith only [hx.2])
  have ht : (23816993 / 50000000 : ℝ) ≤ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ∧ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ≤ (51086191 / 100000000 : ℝ) := by
    exact nonneg_left_product_enclosure (by norm_num : (0 : ℝ) ≤ (15059017 / 5000000 : ℝ)) hpref hpoly
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-361 / 1024 : ℝ))
    (show -(-361 / 1024 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-47 / 128 : ℝ) by linarith only [hx.1]) 2
  have hpe : (1457881 / 2500000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (1520677 / 2500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_109.1 n1_exp_115.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1457881 / 2500000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (16450423 / 25000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (68636061 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (687583 / 1000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_116.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))))
    (16450423 / 25000000 : ℝ) (68636061 / 100000000 : ℝ) (23816993 / 50000000 : ℝ) (51086191 / 100000000 : ℝ)
    (8784147 / 100000000 : ℝ) (687583 / 1000000 : ℝ) (534081 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_019 (x : ℝ) (hx : x ∈ Set.Ioo (-361 / 1024 : ℝ) (-173 / 512 : ℝ)) :
    density x ≤ (131181 / 25000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (17618129 / 2000000 : ℝ) ≤ Real.exp (-2 * (x - 3 / 4)) ∧
      Real.exp (-2 * (x - 3 / 4)) ≤ (90709603 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_117.1 n1_exp_111.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (17618129 / 2000000 : ℝ)) pi_rational_enclosure hi
  have ha : (8648277 / 5000000 : ℝ) ≤ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ∧ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ≤ (17810791 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (842281 / 5000000 : ℝ) ≤ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (110841 / 625000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_118.1 n1_exp_119.2
  have hpoly : (1040487 / 6250000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (17573521 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (842281 / 5000000 : ℝ))
      (by norm_num : (110841 / 625000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have hpref : (7420017 / 2500000 : ℝ) ≤ Real.exp (-(x - 3 / 4)) ∧
      Real.exp (-(x - 3 / 4)) ≤ (6023607 / 2000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -(x - 3 / 4))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_120.1 n1_exp_114.2
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_reflected 6 (x - 3 / 4) (by linarith only [hx.2])
  have ht : (49410759 / 100000000 : ℝ) ≤ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ∧ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ≤ (52927993 / 100000000 : ℝ) := by
    exact nonneg_left_product_enclosure (by norm_num : (0 : ℝ) ≤ (7420017 / 2500000 : ℝ)) hpref hpoly
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-173 / 512 : ℝ))
    (show -(-173 / 512 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-361 / 1024 : ℝ) by linarith only [hx.1]) 2
  have hpe : (6082707 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (6333829 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_115.1 n1_exp_121.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (6082707 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (17158997 / 25000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (3573483 / 5000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (6983683 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_122.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))))
    (17158997 / 25000000 : ℝ) (3573483 / 5000000 : ℝ) (49410759 / 100000000 : ℝ) (52927993 / 100000000 : ℝ)
    (4319441 / 50000000 : ℝ) (6983683 / 10000000 : ℝ) (131181 / 25000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_020 (x : ℝ) (hx : x ∈ Set.Ioo (-173 / 512 : ℝ) (-331 / 1024 : ℝ)) :
    density x ≤ (51087 / 10000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (42773651 / 5000000 : ℝ) ≤ Real.exp (-2 * (x - 3 / 4)) ∧
      Real.exp (-2 * (x - 3 / 4)) ≤ (44045323 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_123.1 n1_exp_117.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (42773651 / 5000000 : ℝ)) pi_rational_enclosure hi
  have ha : (16797169 / 10000000 : ℝ) ≤ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ∧ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ≤ (216207 / 125000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (886727 / 5000000 : ℝ) ≤ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (466067 / 2500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_124.1 n1_exp_125.2
  have hpoly : (1093311 / 6250000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (1844487 / 10000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (886727 / 5000000 : ℝ))
      (by norm_num : (466067 / 2500000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have hpref : (2924847 / 1000000 : ℝ) ≤ Real.exp (-(x - 3 / 4)) ∧
      Real.exp (-(x - 3 / 4)) ≤ (29680069 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -(x - 3 / 4))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_126.1 n1_exp_120.2
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_reflected 6 (x - 3 / 4) (by linarith only [hx.2])
  have ht : (25582139 / 50000000 : ℝ) ≤ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ∧ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ≤ (27372251 / 50000000 : ℝ) := by
    exact nonneg_left_product_enclosure (by norm_num : (0 : ℝ) ≤ (2924847 / 1000000 : ℝ)) hpref hpoly
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-331 / 1024 : ℝ))
    (show -(-331 / 1024 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-173 / 512 : ℝ) by linarith only [hx.1]) 2
  have hpe : (1583457 / 2500000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (1646001 / 2500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_121.1 n1_exp_127.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1583457 / 2500000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (14293917 / 20000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (14858517 / 20000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (7093227 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_128.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))))
    (14293917 / 20000000 : ℝ) (14858517 / 20000000 : ℝ) (25582139 / 50000000 : ℝ) (27372251 / 50000000 : ℝ)
    (2114347 / 25000000 : ℝ) (7093227 / 10000000 : ℝ) (51087 / 10000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_021 (x : ℝ) (hx : x ∈ Set.Ioo (-331 / 1024 : ℝ) (-79 / 256 : ℝ)) :
    density x ≤ (61601 / 12500000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (8307739 / 1000000 : ℝ) ≤ Real.exp (-2 * (x - 3 / 4)) ∧
      Real.exp (-2 * (x - 3 / 4)) ≤ (85547303 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_129.1 n1_exp_123.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (8307739 / 1000000 : ℝ)) pi_rational_enclosure hi
  have ha : (16312203 / 10000000 : ℝ) ≤ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ∧ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ≤ (2099647 / 1250000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (932133 / 5000000 : ℝ) ≤ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (1956907 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_130.1 n1_exp_131.2
  have hpoly : (4587347 / 25000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (4831883 / 25000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (932133 / 5000000 : ℝ))
      (by norm_num : (1956907 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have hpref : (7205787 / 2500000 : ℝ) ≤ Real.exp (-(x - 3 / 4)) ∧
      Real.exp (-(x - 3 / 4)) ≤ (29248471 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -(x - 3 / 4))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_132.1 n1_exp_126.2
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_reflected 6 (x - 3 / 4) (by linarith only [hx.2])
  have ht : (6611089 / 12500000 : ℝ) ≤ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ∧ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ≤ (14132519 / 25000000 : ℝ) := by
    exact nonneg_left_product_enclosure (by norm_num : (0 : ℝ) ≤ (7205787 / 2500000 : ℝ)) hpref hpoly
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-79 / 256 : ℝ))
    (show -(-79 / 256 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-331 / 1024 : ℝ) by linarith only [hx.1]) 2
  have hpe : (6584003 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (6832323 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_127.1 n1_exp_133.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (6584003 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (74292507 / 100000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (77094567 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (7204489 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_134.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))))
    (74292507 / 100000000 : ℝ) (77094567 / 100000000 : ℝ) (6611089 / 12500000 : ℝ) (14132519 / 25000000 : ℝ)
    (2060351 / 25000000 : ℝ) (7204489 / 10000000 : ℝ) (61601 / 12500000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_022 (x : ℝ) (hx : x ∈ Set.Ioo (-79 / 256 : ℝ) (-301 / 1024 : ℝ)) :
    density x ≤ (470909 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (8067879 / 1000000 : ℝ) ≤ Real.exp (-2 * (x - 3 / 4)) ∧
      Real.exp (-2 * (x - 3 / 4)) ≤ (83077391 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_135.1 n1_exp_129.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (8067879 / 1000000 : ℝ)) pi_rational_enclosure hi
  have ha : (396031 / 250000 : ℝ) ≤ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ∧ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ≤ (1631221 / 1000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (244613 / 1250000 : ℝ) ≤ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (82051 / 400000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_136.1 n1_exp_137.2
  have hpoly : (9607491 / 50000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (20219517 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (244613 / 1250000 : ℝ))
      (by norm_num : (82051 / 400000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have hpref : (7101003 / 2500000 : ℝ) ≤ Real.exp (-(x - 3 / 4)) ∧
      Real.exp (-(x - 3 / 4)) ≤ (28823149 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -(x - 3 / 4))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_138.1 n1_exp_132.2
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_reflected 6 (x - 3 / 4) (by linarith only [hx.2])
  have ht : (54578257 / 100000000 : ℝ) ≤ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ∧ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ≤ (7284877 / 12500000 : ℝ) := by
    exact nonneg_left_product_enclosure (by norm_num : (0 : ℝ) ≤ (7101003 / 2500000 : ℝ)) hpref hpoly
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-301 / 1024 : ℝ))
    (show -(-301 / 1024 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-79 / 256 : ℝ) by linarith only [hx.1]) 2
  have hpe : (3416161 / 5000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (7077847 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_133.1 n1_exp_139.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (3416161 / 5000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (38547243 / 50000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (7986501 / 10000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (7317497 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_140.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))))
    (38547243 / 50000000 : ℝ) (7986501 / 10000000 : ℝ) (54578257 / 100000000 : ℝ) (7284877 / 12500000 : ℝ)
    (3996439 / 50000000 : ℝ) (7317497 / 10000000 : ℝ) (470909 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_023 (x : ℝ) (hx : x ∈ Set.Ioo (-301 / 1024 : ℝ) (-143 / 512 : ℝ)) :
    density x ≤ (445631 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (78349441 / 10000000 : ℝ) ≤ Real.exp (-2 * (x - 3 / 4)) ∧
      Real.exp (-2 * (x - 3 / 4)) ≤ (80678791 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_141.1 n1_exp_135.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (78349441 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (15383873 / 10000000 : ℝ) ≤ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ∧ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ≤ (7920623 / 5000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (256409 / 1250000 : ℝ) ≤ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (268409 / 1250000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_142.1 n1_exp_143.2
  have hpoly : (20087599 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (16499 / 78125 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (256409 / 1250000 : ℝ))
      (by norm_num : (268409 / 1250000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have hpref : (2799097 / 1000000 : ℝ) ≤ Real.exp (-(x - 3 / 4)) ∧
      Real.exp (-(x - 3 / 4)) ≤ (28404013 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -(x - 3 / 4))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_144.1 n1_exp_138.2
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_reflected 6 (x - 3 / 4) (by linarith only [hx.2])
  have ht : (28113569 / 50000000 : ℝ) ≤ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ∧ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ≤ (1499641 / 2500000 : ℝ) := by
    exact nonneg_left_product_enclosure (by norm_num : (0 : ℝ) ≤ (2799097 / 1000000 : ℝ)) hpref hpoly
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-143 / 512 : ℝ))
    (show -(-143 / 512 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-301 / 1024 : ℝ) by linarith only [hx.1]) 2
  have hpe : (3538923 / 5000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (3659809 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_139.1 n1_exp_145.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (3538923 / 5000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (79864927 / 100000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (41296553 / 50000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (7432277 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_146.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))))
    (79864927 / 100000000 : ℝ) (41296553 / 50000000 : ℝ) (28113569 / 50000000 : ℝ) (1499641 / 2500000 : ℝ)
    (1928527 / 25000000 : ℝ) (7432277 / 10000000 : ℝ) (445631 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_024 (x : ℝ) (hx : x ∈ Set.Ioo (-143 / 512 : ℝ) (-271 / 1024 : ℝ)) :
    density x ≤ (417499 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (15217469 / 2000000 : ℝ) ≤ Real.exp (-2 * (x - 3 / 4)) ∧
      Real.exp (-2 * (x - 3 / 4)) ≤ (39174721 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_147.1 n1_exp_141.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (15217469 / 2000000 : ℝ)) pi_rational_enclosure hi
  have ha : (233433 / 156250 : ℝ) ≤ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ∧ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ≤ (15383879 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (2147269 / 10000000 : ℝ) ≤ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (448959 / 2000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_148.1 n1_exp_149.2
  have hpoly : (4192987 / 20000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (86027 / 390625 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (2147269 / 10000000 : ℝ))
      (by norm_num : (448959 / 2000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have hpref : (13791967 / 5000000 : ℝ) ≤ Real.exp (-(x - 3 / 4)) ∧
      Real.exp (-(x - 3 / 4)) ≤ (27990971 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -(x - 3 / 4))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_150.1 n1_exp_144.2
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_reflected 6 (x - 3 / 4) (by linarith only [hx.2])
  have ht : (28914769 / 50000000 : ℝ) ≤ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ∧ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ≤ (6164427 / 10000000 : ℝ) := by
    exact nonneg_left_product_enclosure (by norm_num : (0 : ℝ) ≤ (13791967 / 5000000 : ℝ)) hpref hpoly
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-271 / 1024 : ℝ))
    (show -(-271 / 1024 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-143 / 512 : ℝ) by linarith only [hx.1]) 2
  have hpe : (7319617 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (1511333 / 2000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_145.1 n1_exp_151.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (7319617 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (82593021 / 100000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (85267897 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (7548857 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_152.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))))
    (82593021 / 100000000 : ℝ) (85267897 / 100000000 : ℝ) (28914769 / 50000000 : ℝ) (6164427 / 10000000 : ℝ)
    (3703807 / 50000000 : ℝ) (7548857 / 10000000 : ℝ) (417499 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_025 (x : ℝ) (hx : x ∈ Set.Ioo (-271 / 1024 : ℝ) (-1 / 4 : ℝ)) :
    density x ≤ (77419 / 20000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (115454 / 15625 : ℝ) ≤ Real.exp (-2 * (x - 3 / 4)) ∧
      Real.exp (-2 * (x - 3 / 4)) ≤ (38043673 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_153.1 n1_exp_147.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (115454 / 15625 : ℝ)) pi_rational_enclosure hi
  have ha : (7254187 / 5000000 : ℝ) ≤ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ∧ (Real.pi / 16 * Real.exp (-2 * (x - 3 / 4))) ≤ (7469859 / 5000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (280599 / 1250000 : ℝ) ≤ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧ (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (117187 / 500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_154.1 n1_exp_155.2
  have hpoly : (10922289 / 50000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))) ≤ (4585953 / 20000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (280599 / 1250000 : ℝ))
      (by norm_num : (117187 / 500000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have hpref : (13591409 / 5000000 : ℝ) ≤ Real.exp (-(x - 3 / 4)) ∧
      Real.exp (-(x - 3 / 4)) ≤ (5516787 / 2000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -(x - 3 / 4))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_156.1 n1_exp_150.2
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_reflected 6 (x - 3 / 4) (by linarith only [hx.2])
  have ht : (29689859 / 50000000 : ℝ) ≤ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ∧ (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4))))) ≤ (12649863 / 20000000 : ℝ) := by
    exact nonneg_left_product_enclosure (by norm_num : (0 : ℝ) ≤ (13591409 / 5000000 : ℝ)) hpref hpoly
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hxsign : x ≤ 0 := by linarith only [hx.2]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ -(-1 / 4 : ℝ))
    (show -(-1 / 4 : ℝ) ≤ -x by linarith only [hx.2]) 2
  have hsU := pow_le_pow_left₀ (neg_nonneg.mpr hxsign)
    (show -x ≤ -(-271 / 1024 : ℝ) by linarith only [hx.1]) 2
  have hpe : (944583 / 1250000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (973501 / 1250000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_151.1 n1_exp_157.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (944583 / 1250000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (85267809 / 100000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (3515133 / 4000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (3833633 / 5000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_158.2
    rw [abs_of_nonpos hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (Real.exp (-(x - 3 / 4)) * thetaPolynomial 6 (Real.exp (-(Real.pi / 16) * Real.exp (-2 * (x - 3 / 4)))))
    (85267809 / 100000000 : ℝ) (3515133 / 4000000 : ℝ) (29689859 / 50000000 : ℝ) (12649863 / 20000000 : ℝ)
    (7076191 / 100000000 : ℝ) (3833633 / 5000000 : ℝ) (77419 / 20000000 : ℝ)
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

noncomputable def endpoints : Fin 27 → ℝ :=
  ![(-4 / 1 : ℝ), (-17 / 8 : ℝ), (-19 / 16 : ℝ), (-61 / 64 : ℝ), (-107 / 128 : ℝ), (-199 / 256 : ℝ), (-23 / 32 : ℝ), (-169 / 256 : ℝ), (-323 / 512 : ℝ), (-77 / 128 : ℝ), (-293 / 512 : ℝ), (-139 / 256 : ℝ), (-263 / 512 : ℝ), (-31 / 64 : ℝ), (-233 / 512 : ℝ), (-109 / 256 : ℝ), (-203 / 512 : ℝ), (-391 / 1024 : ℝ), (-47 / 128 : ℝ), (-361 / 1024 : ℝ), (-173 / 512 : ℝ), (-331 / 1024 : ℝ), (-79 / 256 : ℝ), (-301 / 1024 : ℝ), (-143 / 512 : ℝ), (-271 / 1024 : ℝ), (-1 / 4 : ℝ)]

noncomputable def cellBounds : Fin 26 → ℝ :=
  ![(3 / 100000000 : ℝ), (131 / 25000000 : ℝ), (31559 / 100000000 : ℝ), (25817 / 25000000 : ℝ), (38663 / 50000000 : ℝ), (24693 / 12500000 : ℝ), (42371 / 10000000 : ℝ), (252437 / 100000000 : ℝ), (17097 / 5000000 : ℝ), (8907 / 2000000 : ℝ), (111857 / 20000000 : ℝ), (67873 / 10000000 : ℝ), (99669 / 12500000 : ℝ), (454017 / 50000000 : ℝ), (20071 / 2000000 : ℝ), (538653 / 50000000 : ℝ), (3367 / 625000 : ℝ), (538773 / 100000000 : ℝ), (534081 / 100000000 : ℝ), (131181 / 25000000 : ℝ), (51087 / 10000000 : ℝ), (61601 / 12500000 : ℝ), (470909 / 100000000 : ℝ), (445631 / 100000000 : ℝ), (417499 / 100000000 : ℝ), (77419 / 20000000 : ℝ)]

theorem endpoint_first : endpoints 0 = (-4 : ℝ) := by norm_num [endpoints]
theorem endpoint_last : endpoints (Fin.last 26) = (-1 / 4 : ℝ) := by norm_num [endpoints, Fin.last]

theorem endpoints_step (k : Fin 26) : endpoints k.castSucc ≤ endpoints k.succ := by
  fin_cases k
  · change (-4 / 1 : ℝ) ≤ (-17 / 8 : ℝ)
    norm_num
  · change (-17 / 8 : ℝ) ≤ (-19 / 16 : ℝ)
    norm_num
  · change (-19 / 16 : ℝ) ≤ (-61 / 64 : ℝ)
    norm_num
  · change (-61 / 64 : ℝ) ≤ (-107 / 128 : ℝ)
    norm_num
  · change (-107 / 128 : ℝ) ≤ (-199 / 256 : ℝ)
    norm_num
  · change (-199 / 256 : ℝ) ≤ (-23 / 32 : ℝ)
    norm_num
  · change (-23 / 32 : ℝ) ≤ (-169 / 256 : ℝ)
    norm_num
  · change (-169 / 256 : ℝ) ≤ (-323 / 512 : ℝ)
    norm_num
  · change (-323 / 512 : ℝ) ≤ (-77 / 128 : ℝ)
    norm_num
  · change (-77 / 128 : ℝ) ≤ (-293 / 512 : ℝ)
    norm_num
  · change (-293 / 512 : ℝ) ≤ (-139 / 256 : ℝ)
    norm_num
  · change (-139 / 256 : ℝ) ≤ (-263 / 512 : ℝ)
    norm_num
  · change (-263 / 512 : ℝ) ≤ (-31 / 64 : ℝ)
    norm_num
  · change (-31 / 64 : ℝ) ≤ (-233 / 512 : ℝ)
    norm_num
  · change (-233 / 512 : ℝ) ≤ (-109 / 256 : ℝ)
    norm_num
  · change (-109 / 256 : ℝ) ≤ (-203 / 512 : ℝ)
    norm_num
  · change (-203 / 512 : ℝ) ≤ (-391 / 1024 : ℝ)
    norm_num
  · change (-391 / 1024 : ℝ) ≤ (-47 / 128 : ℝ)
    norm_num
  · change (-47 / 128 : ℝ) ≤ (-361 / 1024 : ℝ)
    norm_num
  · change (-361 / 1024 : ℝ) ≤ (-173 / 512 : ℝ)
    norm_num
  · change (-173 / 512 : ℝ) ≤ (-331 / 1024 : ℝ)
    norm_num
  · change (-331 / 1024 : ℝ) ≤ (-79 / 256 : ℝ)
    norm_num
  · change (-79 / 256 : ℝ) ≤ (-301 / 1024 : ℝ)
    norm_num
  · change (-301 / 1024 : ℝ) ≤ (-143 / 512 : ℝ)
    norm_num
  · change (-143 / 512 : ℝ) ≤ (-271 / 1024 : ℝ)
    norm_num
  · change (-271 / 1024 : ℝ) ≤ (-1 / 4 : ℝ)
    norm_num

 theorem cell_bound_sum_le :
    (∑ k : Fin 26, cellBounds k * (endpoints k.succ - endpoints k.castSucc)) ≤
      (1 / 320 : ℝ) := by
  norm_num [endpoints, cellBounds, Fin.sum_univ_succ]

theorem cell_bounds (k : Fin 26) (x : ℝ)
    (hx : x ∈ Ioo (endpoints k.castSucc) (endpoints k.succ)) :
    density x ≤ cellBounds k := by
  fin_cases k
  · change density x ≤ (3 / 100000000 : ℝ)
    change x ∈ Ioo (-4 / 1 : ℝ) (-17 / 8 : ℝ) at hx
    exact cell_000 x hx
  · change density x ≤ (131 / 25000000 : ℝ)
    change x ∈ Ioo (-17 / 8 : ℝ) (-19 / 16 : ℝ) at hx
    exact cell_001 x hx
  · change density x ≤ (31559 / 100000000 : ℝ)
    change x ∈ Ioo (-19 / 16 : ℝ) (-61 / 64 : ℝ) at hx
    exact cell_002 x hx
  · change density x ≤ (25817 / 25000000 : ℝ)
    change x ∈ Ioo (-61 / 64 : ℝ) (-107 / 128 : ℝ) at hx
    exact cell_003 x hx
  · change density x ≤ (38663 / 50000000 : ℝ)
    change x ∈ Ioo (-107 / 128 : ℝ) (-199 / 256 : ℝ) at hx
    exact cell_004 x hx
  · change density x ≤ (24693 / 12500000 : ℝ)
    change x ∈ Ioo (-199 / 256 : ℝ) (-23 / 32 : ℝ) at hx
    exact cell_005 x hx
  · change density x ≤ (42371 / 10000000 : ℝ)
    change x ∈ Ioo (-23 / 32 : ℝ) (-169 / 256 : ℝ) at hx
    exact cell_006 x hx
  · change density x ≤ (252437 / 100000000 : ℝ)
    change x ∈ Ioo (-169 / 256 : ℝ) (-323 / 512 : ℝ) at hx
    exact cell_007 x hx
  · change density x ≤ (17097 / 5000000 : ℝ)
    change x ∈ Ioo (-323 / 512 : ℝ) (-77 / 128 : ℝ) at hx
    exact cell_008 x hx
  · change density x ≤ (8907 / 2000000 : ℝ)
    change x ∈ Ioo (-77 / 128 : ℝ) (-293 / 512 : ℝ) at hx
    exact cell_009 x hx
  · change density x ≤ (111857 / 20000000 : ℝ)
    change x ∈ Ioo (-293 / 512 : ℝ) (-139 / 256 : ℝ) at hx
    exact cell_010 x hx
  · change density x ≤ (67873 / 10000000 : ℝ)
    change x ∈ Ioo (-139 / 256 : ℝ) (-263 / 512 : ℝ) at hx
    exact cell_011 x hx
  · change density x ≤ (99669 / 12500000 : ℝ)
    change x ∈ Ioo (-263 / 512 : ℝ) (-31 / 64 : ℝ) at hx
    exact cell_012 x hx
  · change density x ≤ (454017 / 50000000 : ℝ)
    change x ∈ Ioo (-31 / 64 : ℝ) (-233 / 512 : ℝ) at hx
    exact cell_013 x hx
  · change density x ≤ (20071 / 2000000 : ℝ)
    change x ∈ Ioo (-233 / 512 : ℝ) (-109 / 256 : ℝ) at hx
    exact cell_014 x hx
  · change density x ≤ (538653 / 50000000 : ℝ)
    change x ∈ Ioo (-109 / 256 : ℝ) (-203 / 512 : ℝ) at hx
    exact cell_015 x hx
  · change density x ≤ (3367 / 625000 : ℝ)
    change x ∈ Ioo (-203 / 512 : ℝ) (-391 / 1024 : ℝ) at hx
    exact cell_016 x hx
  · change density x ≤ (538773 / 100000000 : ℝ)
    change x ∈ Ioo (-391 / 1024 : ℝ) (-47 / 128 : ℝ) at hx
    exact cell_017 x hx
  · change density x ≤ (534081 / 100000000 : ℝ)
    change x ∈ Ioo (-47 / 128 : ℝ) (-361 / 1024 : ℝ) at hx
    exact cell_018 x hx
  · change density x ≤ (131181 / 25000000 : ℝ)
    change x ∈ Ioo (-361 / 1024 : ℝ) (-173 / 512 : ℝ) at hx
    exact cell_019 x hx
  · change density x ≤ (51087 / 10000000 : ℝ)
    change x ∈ Ioo (-173 / 512 : ℝ) (-331 / 1024 : ℝ) at hx
    exact cell_020 x hx
  · change density x ≤ (61601 / 12500000 : ℝ)
    change x ∈ Ioo (-331 / 1024 : ℝ) (-79 / 256 : ℝ) at hx
    exact cell_021 x hx
  · change density x ≤ (470909 / 100000000 : ℝ)
    change x ∈ Ioo (-79 / 256 : ℝ) (-301 / 1024 : ℝ) at hx
    exact cell_022 x hx
  · change density x ≤ (445631 / 100000000 : ℝ)
    change x ∈ Ioo (-301 / 1024 : ℝ) (-143 / 512 : ℝ) at hx
    exact cell_023 x hx
  · change density x ≤ (417499 / 100000000 : ℝ)
    change x ∈ Ioo (-143 / 512 : ℝ) (-271 / 1024 : ℝ) at hx
    exact cell_024 x hx
  · change density x ≤ (77419 / 20000000 : ℝ)
    change x ∈ Ioo (-271 / 1024 : ℝ) (-1 / 4 : ℝ) at hx
    exact cell_025 x hx

theorem compact_certificate :
    IntegrableOn density (Icc (-4 : ℝ) (-1 / 4 : ℝ)) ∧
      (∫ x : ℝ in Icc (-4 : ℝ) (-1 / 4 : ℝ), density x) ≤ (1 / 320 : ℝ) := by
  have hI : Integrable density :=
    MasulloRH.DirectIntegrability.height_one_density_integrable
  refine ⟨hI.integrableOn, ?_⟩
  have h := MasulloRH.EnergyCertificate.integral_le_fin_partition_sum
    density 26 endpoints cellBounds hI endpoints_step cell_bounds
  rw [endpoint_first, endpoint_last,
    intervalIntegral.integral_of_le (show (-4 : ℝ) ≤ (-1 / 4 : ℝ) by norm_num),
    ← integral_Icc_eq_integral_Ioc] at h
  exact h.trans cell_bound_sum_le

end MasulloRH.HeightOne
end

end N1LeftOuterProof

open MeasureTheory MasulloRH.GaussianApproximation

theorem solution :
    IntegrableOn (fun x : ℝ =>
      Real.exp (2*(3/4)*x + 2*(7/32)*|x|) *
        ‖residual 1 (fun _ : Fin 1 => (73/50 : ℂ))
          (fun _ : Fin 1 => (3/4 : ℝ)) x‖^2) (Set.Icc (-4 : ℝ) (-1 / 4 : ℝ)) ∧
    (∫ x : ℝ in Set.Icc (-4 : ℝ) (-1 / 4 : ℝ),
      Real.exp (2*(3/4)*x + 2*(7/32)*|x|) *
        ‖residual 1 (fun _ : Fin 1 => (73/50 : ℂ))
          (fun _ : Fin 1 => (3/4 : ℝ)) x‖^2) ≤ (1 / 320 : ℝ) := by
  have hF : (fun x : ℝ =>
      Real.exp (2*(3/4)*x + 2*(7/32)*|x|) *
        ‖residual 1 (fun _ : Fin 1 => (73/50 : ℂ))
          (fun _ : Fin 1 => (3/4 : ℝ)) x‖^2) =
      N1LeftOuterProof.MasulloRH.HeightOne.density := by
    funext x
    simp only [N1LeftOuterProof.MasulloRH.HeightOne.density,
      MasulloRH.GaussianApproximation.residual, Fin.sum_univ_one,
      show (2 : ℝ)*(3/4)=3/2 by norm_num,
      show (2 : ℝ)*(7/32)=7/16 by norm_num]
  rw [hF]
  exact N1LeftOuterProof.MasulloRH.HeightOne.compact_certificate

#print axioms solution
