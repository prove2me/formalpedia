-- Prove2me | solution 1 for MasulloRH.height_one_half_to_four_energy_certificate
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T17:45:44.493594+00:00
-- url     : https://prove2.me/submissions/77c90381-344a-4e4d-aa1f-7ad7831eebae

/- Actual height-one residual energy on [1/2,4].
Copied helper proofs are isolated so left and right certificates can coexist. -/
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
set_option maxRecDepth 16384

namespace N1HalfFourProof

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

/- Source: Accepted public reflection and Gaussian-tail norm consequences. -/
section
set_option autoImplicit false
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

/- Source: Compact-window monotonicity of accepted reflected-error theorem. -/
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
  linarith [hx.1]

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

/- Direct proofs of only the scalar inequalities used below. -/
section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
namespace MasulloRH.CertifiedExp
theorem n1_exp_006 :
    (0 : ℝ) ≤ Real.exp (-(64 / 1 : ℝ)) ∧
    Real.exp (-(64 / 1 : ℝ)) ≤ (1 / 1048576 : ℝ) :=
  neg_enclosure_of_twenty_le (by norm_num)

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


theorem n1_exp_299 :
    (1839397 / 5000000 : ℝ) ≤ Real.exp (-(1 / 1 : ℝ)) ∧
    Real.exp (-(1 / 1 : ℝ)) ≤ (735759 / 2000000 : ℝ) := by
  have hsmall : (5158717037 / 5000000000 : ℝ) ≤ Real.exp (1 / 32 : ℝ) ∧
      Real.exp (1 / 32 : ℝ) ≤ (412697363 / 400000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1 / 32 : ℝ))
    (a := (5158717037 / 5000000000 : ℝ)) (b := (412697363 / 400000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_376 :
    (3032653 / 5000000 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) ∧
    Real.exp (-(1 / 2 : ℝ)) ≤ (6065307 / 10000000 : ℝ) := by
  have hsmall : (2031495417 / 2000000000 : ℝ) ≤ Real.exp (1 / 64 : ℝ) ∧
      Real.exp (1 / 64 : ℝ) ≤ (5078738543 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1 / 64 : ℝ))
    (a := (2031495417 / 2000000000 : ℝ)) (b := (5078738543 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_380 :
    (78223 / 125000 : ℝ) ≤ Real.exp (-(15 / 32 : ℝ)) ∧
    Real.exp (-(15 / 32 : ℝ)) ≤ (6257841 / 10000000 : ℝ) := by
  have hsmall : (2536890629 / 2500000000 : ℝ) ≤ Real.exp (15 / 1024 : ℝ) ∧
      Real.exp (15 / 1024 : ℝ) ≤ (10147562517 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (15 / 1024 : ℝ))
    (a := (2536890629 / 2500000000 : ℝ)) (b := (10147562517 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_381 :
    (280043 / 2000000 : ℝ) ≤ Real.exp (-(1965959 / 1000000 : ℝ)) ∧
    Real.exp (-(1965959 / 1000000 : ℝ)) ≤ (175027 / 1250000 : ℝ) := by
  have hsmall : (10633626717 / 10000000000 : ℝ) ≤ Real.exp (1965959 / 32000000 : ℝ) ∧
      Real.exp (1965959 / 32000000 : ℝ) ≤ (5316813359 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1965959 / 32000000 : ℝ))
    (a := (10633626717 / 10000000000 : ℝ)) (b := (5316813359 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_382 :
    (371881 / 2500000 : ℝ) ≤ Real.exp (-(4763679 / 2500000 : ℝ)) ∧
    Real.exp (-(4763679 / 2500000 : ℝ)) ≤ (59501 / 400000 : ℝ) := by
  have hsmall : (10613545689 / 10000000000 : ℝ) ≤ Real.exp (4763679 / 80000000 : ℝ) ∧
      Real.exp (4763679 / 80000000 : ℝ) ≤ (1061354569 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (4763679 / 80000000 : ℝ))
    (a := (10613545689 / 10000000000 : ℝ)) (b := (1061354569 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_383 :
    (1726267 / 5000000 : ℝ) ≤ Real.exp (-(1089 / 1024 : ℝ)) ∧
    Real.exp (-(1089 / 1024 : ℝ)) ≤ (690507 / 2000000 : ℝ) := by
  have hsmall : (1292240061 / 1250000000 : ℝ) ≤ Real.exp (1089 / 32768 : ℝ) ∧
      Real.exp (1089 / 32768 : ℝ) ≤ (10337920489 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1089 / 32768 : ℝ))
    (a := (1292240061 / 1250000000 : ℝ)) (b := (10337920489 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_384 :
    (5431257 / 2000000 : ℝ) ≤ Real.exp (1023 / 1024 : ℝ) ∧
    Real.exp (1023 / 1024 : ℝ) ≤ (13578143 / 5000000 : ℝ) := by
  have hsmall : (103171192166949 / 100000000000000 : ℝ) ≤ Real.exp (1023 / 32768 : ℝ) ∧
      Real.exp (1023 / 32768 : ℝ) ≤ (2063423843339 / 2000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1023 / 32768 : ℝ))
    (a := (103171192166949 / 100000000000000 : ℝ)) (b := (2063423843339 / 2000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_385 :
    (1291297 / 2000000 : ℝ) ≤ Real.exp (-(7 / 16 : ℝ)) ∧
    Real.exp (-(7 / 16 : ℝ)) ≤ (3228243 / 5000000 : ℝ) := by
  have hsmall : (1267207203 / 1250000000 : ℝ) ≤ Real.exp (7 / 512 : ℝ) ∧
      Real.exp (7 / 512 : ℝ) ≤ (81101261 / 80000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7 / 512 : ℝ))
    (a := (1267207203 / 1250000000 : ℝ)) (b := (81101261 / 80000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_386 :
    (82219 / 625000 : ℝ) ≤ Real.exp (-(5070913 / 2500000 : ℝ)) ∧
    Real.exp (-(5070913 / 2500000 : ℝ)) ≤ (263101 / 2000000 : ℝ) := by
  have hsmall : (1331798073 / 1250000000 : ℝ) ≤ Real.exp (5070913 / 80000000 : ℝ) ∧
      Real.exp (5070913 / 80000000 : ℝ) ≤ (2130876917 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5070913 / 80000000 : ℝ))
    (a := (1331798073 / 1250000000 : ℝ)) (b := (2130876917 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_387 :
    (175027 / 1250000 : ℝ) ≤ Real.exp (-(982979 / 500000 : ℝ)) ∧
    Real.exp (-(982979 / 500000 : ℝ)) ≤ (1400217 / 10000000 : ℝ) := by
  have hsmall : (2126725277 / 2000000000 : ℝ) ≤ Real.exp (982979 / 16000000 : ℝ) ∧
      Real.exp (982979 / 16000000 : ℝ) ≤ (5316813193 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (982979 / 16000000 : ℝ))
    (a := (2126725277 / 2000000000 : ℝ)) (b := (5316813193 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_388 :
    (3233867 / 10000000 : ℝ) ≤ Real.exp (-(289 / 256 : ℝ)) ∧
    Real.exp (-(289 / 256 : ℝ)) ≤ (808467 / 2500000 : ℝ) := by
  have hsmall : (10359079829 / 10000000000 : ℝ) ≤ Real.exp (289 / 8192 : ℝ) ∧
      Real.exp (289 / 8192 : ℝ) ≤ (1035907983 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (289 / 8192 : ℝ))
    (a := (10359079829 / 10000000000 : ℝ)) (b := (1035907983 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_389 :
    (1665359 / 2500000 : ℝ) ≤ Real.exp (-(13 / 32 : ℝ)) ∧
    Real.exp (-(13 / 32 : ℝ)) ≤ (6661437 / 10000000 : ℝ) := by
  have hsmall : (12659703 / 12500000 : ℝ) ≤ Real.exp (13 / 1024 : ℝ) ∧
      Real.exp (13 / 1024 : ℝ) ≤ (10127762401 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (13 / 1024 : ℝ))
    (a := (12659703 / 12500000 : ℝ)) (b := (10127762401 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_390 :
    (1233471 / 10000000 : ℝ) ≤ Real.exp (-(5231881 / 2500000 : ℝ)) ∧
    Real.exp (-(5231881 / 2500000 : ℝ)) ≤ (19273 / 156250 : ℝ) := by
  have hsmall : (10675843853 / 10000000000 : ℝ) ≤ Real.exp (5231881 / 80000000 : ℝ) ∧
      Real.exp (5231881 / 80000000 : ℝ) ≤ (5337921927 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5231881 / 80000000 : ℝ))
    (a := (10675843853 / 10000000000 : ℝ)) (b := (5337921927 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_391 :
    (263101 / 2000000 : ℝ) ≤ Real.exp (-(20283641 / 10000000 : ℝ)) ∧
    Real.exp (-(20283641 / 10000000 : ℝ)) ≤ (657753 / 5000000 : ℝ) := by
  have hsmall : (5327192109 / 5000000000 : ℝ) ≤ Real.exp (20283641 / 320000000 : ℝ) ∧
      Real.exp (20283641 / 320000000 : ℝ) ≤ (10654384219 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (20283641 / 320000000 : ℝ))
    (a := (5327192109 / 5000000000 : ℝ)) (b := (10654384219 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_392 :
    (151157 / 500000 : ℝ) ≤ Real.exp (-(1225 / 1024 : ℝ)) ∧
    Real.exp (-(1225 / 1024 : ℝ)) ≤ (3023141 / 10000000 : ℝ) := by
  have hsmall : (10380916059 / 10000000000 : ℝ) ≤ Real.exp (1225 / 32768 : ℝ) ∧
      Real.exp (1225 / 32768 : ℝ) ≤ (519045803 / 500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1225 / 32768 : ℝ))
    (a := (10380916059 / 10000000000 : ℝ)) (b := (519045803 / 500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_393 :
    (2885131 / 1000000 : ℝ) ≤ Real.exp (1085 / 1024 : ℝ) ∧
    Real.exp (1085 / 1024 : ℝ) ≤ (28851311 / 10000000 : ℝ) := by
  have hsmall : (20673317224997 / 20000000000000 : ℝ) ≤ Real.exp (1085 / 32768 : ℝ) ∧
      Real.exp (1085 / 32768 : ℝ) ≤ (51683293062493 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1085 / 32768 : ℝ))
    (a := (20673317224997 / 20000000000000 : ℝ)) (b := (51683293062493 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_394 :
    (1718223 / 2500000 : ℝ) ≤ Real.exp (-(3 / 8 : ℝ)) ∧
    Real.exp (-(3 / 8 : ℝ)) ≤ (6872893 / 10000000 : ℝ) := by
  have hsmall : (2023575367 / 2000000000 : ℝ) ≤ Real.exp (3 / 256 : ℝ) ∧
      Real.exp (3 / 256 : ℝ) ≤ (2529469209 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3 / 256 : ℝ))
    (a := (2023575367 / 2000000000 : ℝ)) (b := (2529469209 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_395 :
    (1154193 / 10000000 : ℝ) ≤ Real.exp (-(21591833 / 10000000 : ℝ)) ∧
    Real.exp (-(21591833 / 10000000 : ℝ)) ≤ (577097 / 5000000 : ℝ) := by
  have hsmall : (5349014779 / 5000000000 : ℝ) ≤ Real.exp (21591833 / 320000000 : ℝ) ∧
      Real.exp (21591833 / 320000000 : ℝ) ≤ (10698029559 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (21591833 / 320000000 : ℝ))
    (a := (5349014779 / 5000000000 : ℝ)) (b := (10698029559 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_396 :
    (19273 / 156250 : ℝ) ≤ Real.exp (-(10463757 / 5000000 : ℝ)) ∧
    Real.exp (-(10463757 / 5000000 : ℝ)) ≤ (1233473 / 10000000 : ℝ) := by
  have hsmall : (10675843519 / 10000000000 : ℝ) ≤ Real.exp (10463757 / 160000000 : ℝ) ∧
      Real.exp (10463757 / 160000000 : ℝ) ≤ (33362011 / 31250000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (10463757 / 160000000 : ℝ))
    (a := (10675843519 / 10000000000 : ℝ)) (b := (33362011 / 31250000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_397 :
    (2820629 / 10000000 : ℝ) ≤ Real.exp (-(81 / 64 : ℝ)) ∧
    Real.exp (-(81 / 64 : ℝ)) ≤ (282063 / 1000000 : ℝ) := by
  have hsmall : (5201716637 / 5000000000 : ℝ) ≤ Real.exp (81 / 2048 : ℝ) ∧
      Real.exp (81 / 2048 : ℝ) ≤ (416137331 / 400000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (81 / 2048 : ℝ))
    (a := (5201716637 / 5000000000 : ℝ)) (b := (416137331 / 400000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_398 :
    (29738093 / 10000000 : ℝ) ≤ Real.exp (279 / 256 : ℝ) ∧
    Real.exp (279 / 256 : ℝ) ≤ (14869047 / 5000000 : ℝ) := by
  have hsmall : (103464421830069 / 100000000000000 : ℝ) ≤ Real.exp (279 / 8192 : ℝ) ∧
      Real.exp (279 / 8192 : ℝ) ≤ (10346442183007 / 10000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (279 / 8192 : ℝ))
    (a := (103464421830069 / 100000000000000 : ℝ)) (b := (10346442183007 / 10000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_399 :
    (7091061 / 10000000 : ℝ) ≤ Real.exp (-(11 / 32 : ℝ)) ∧
    Real.exp (-(11 / 32 : ℝ)) ≤ (3545531 / 5000000 : ℝ) := by
  have hsmall : (10108000919 / 10000000000 : ℝ) ≤ Real.exp (11 / 1024 : ℝ) ∧
      Real.exp (11 / 1024 : ℝ) ≤ (252700023 / 250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (11 / 1024 : ℝ))
    (a := (10108000919 / 10000000000 : ℝ)) (b := (252700023 / 250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_400 :
    (215547 / 2000000 : ℝ) ≤ Real.exp (-(22277231 / 10000000 : ℝ)) ∧
    Real.exp (-(22277231 / 10000000 : ℝ)) ≤ (134717 / 1250000 : ℝ) := by
  have hsmall : (1072096789 / 1000000000 : ℝ) ≤ Real.exp (22277231 / 320000000 : ℝ) ∧
      Real.exp (22277231 / 320000000 : ℝ) ≤ (10720967891 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (22277231 / 320000000 : ℝ))
    (a := (1072096789 / 1000000000 : ℝ)) (b := (10720967891 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_401 :
    (577097 / 5000000 : ℝ) ≤ Real.exp (-(10795911 / 5000000 : ℝ)) ∧
    Real.exp (-(10795911 / 5000000 : ℝ)) ≤ (230839 / 2000000 : ℝ) := by
  have hsmall : (1069802919 / 1000000000 : ℝ) ≤ Real.exp (10795911 / 160000000 : ℝ) ∧
      Real.exp (10795911 / 160000000 : ℝ) ≤ (10698029191 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (10795911 / 160000000 : ℝ))
    (a := (1069802919 / 1000000000 : ℝ)) (b := (10698029191 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_402 :
    (2626549 / 10000000 : ℝ) ≤ Real.exp (-(1369 / 1024 : ℝ)) ∧
    Real.exp (-(1369 / 1024 : ℝ)) ≤ (52531 / 200000 : ℝ) := by
  have hsmall : (1303329463 / 1250000000 : ℝ) ≤ Real.exp (1369 / 32768 : ℝ) ∧
      Real.exp (1369 / 32768 : ℝ) ≤ (2085327141 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1369 / 32768 : ℝ))
    (a := (1303329463 / 1250000000 : ℝ)) (b := (2085327141 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_403 :
    (30652133 / 10000000 : ℝ) ≤ Real.exp (1147 / 1024 : ℝ) ∧
    Real.exp (1147 / 1024 : ℝ) ≤ (15326067 / 5000000 : ℝ) := by
  have hsmall : (103562350135921 / 100000000000000 : ℝ) ≤ Real.exp (1147 / 32768 : ℝ) ∧
      Real.exp (1147 / 32768 : ℝ) ≤ (51781175067961 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1147 / 32768 : ℝ))
    (a := (103562350135921 / 100000000000000 : ℝ)) (b := (51781175067961 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_404 :
    (1829039 / 2500000 : ℝ) ≤ Real.exp (-(5 / 16 : ℝ)) ∧
    Real.exp (-(5 / 16 : ℝ)) ≤ (7316157 / 10000000 : ℝ) := by
  have hsmall : (10098134643 / 10000000000 : ℝ) ≤ Real.exp (5 / 512 : ℝ) ∧
      Real.exp (5 / 512 : ℝ) ≤ (2524533661 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5 / 512 : ℝ))
    (a := (10098134643 / 10000000000 : ℝ)) (b := (2524533661 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_405 :
    (502077 / 5000000 : ℝ) ≤ Real.exp (-(5746097 / 2500000 : ℝ)) ∧
    Real.exp (-(5746097 / 2500000 : ℝ)) ≤ (200831 / 2000000 : ℝ) := by
  have hsmall : (5372342993 / 5000000000 : ℝ) ≤ Real.exp (5746097 / 80000000 : ℝ) ∧
      Real.exp (5746097 / 80000000 : ℝ) ≤ (10744685987 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5746097 / 80000000 : ℝ))
    (a := (5372342993 / 5000000000 : ℝ)) (b := (10744685987 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_406 :
    (134717 / 1250000 : ℝ) ≤ Real.exp (-(1113861 / 500000 : ℝ)) ∧
    Real.exp (-(1113861 / 500000 : ℝ)) ≤ (1077737 / 10000000 : ℝ) := by
  have hsmall : (5360483761 / 5000000000 : ℝ) ≤ Real.exp (1113861 / 16000000 : ℝ) ∧
      Real.exp (1113861 / 16000000 : ℝ) ≤ (10720967523 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1113861 / 16000000 : ℝ))
    (a := (5360483761 / 5000000000 : ℝ)) (b := (10720967523 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_407 :
    (2441051 / 10000000 : ℝ) ≤ Real.exp (-(361 / 256 : ℝ)) ∧
    Real.exp (-(361 / 256 : ℝ)) ≤ (610263 / 2500000 : ℝ) := by
  have hsmall : (10450527711 / 10000000000 : ℝ) ≤ Real.exp (361 / 8192 : ℝ) ∧
      Real.exp (361 / 8192 : ℝ) ≤ (326578991 / 312500000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (361 / 8192 : ℝ))
    (a := (10450527711 / 10000000000 : ℝ)) (b := (326578991 / 312500000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_408 :
    (7898567 / 2500000 : ℝ) ≤ Real.exp (589 / 512 : ℝ) ∧
    Real.exp (589 / 512 : ℝ) ≤ (31594269 / 10000000 : ℝ) := by
  have hsmall : (20732074226037 / 20000000000000 : ℝ) ≤ Real.exp (589 / 16384 : ℝ) ∧
      Real.exp (589 / 16384 : ℝ) ≤ (51830185565093 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (589 / 16384 : ℝ))
    (a := (20732074226037 / 20000000000000 : ℝ)) (b := (51830185565093 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_409 :
    (1509679 / 2000000 : ℝ) ≤ Real.exp (-(9 / 32 : ℝ)) ∧
    Real.exp (-(9 / 32 : ℝ)) ≤ (7548397 / 10000000 : ℝ) := by
  have hsmall : (10088277997 / 10000000000 : ℝ) ≤ Real.exp (9 / 1024 : ℝ) ∧
      Real.exp (9 / 1024 : ℝ) ≤ (5044138999 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (9 / 1024 : ℝ))
    (a := (10088277997 / 10000000000 : ℝ)) (b := (5044138999 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_410 :
    (1867 / 20000 : ℝ) ≤ Real.exp (-(2964249 / 1250000 : ℝ)) ∧
    Real.exp (-(2964249 / 1250000 : ℝ)) ≤ (933501 / 10000000 : ℝ) := by
  have hsmall : (10769211953 / 10000000000 : ℝ) ≤ Real.exp (2964249 / 40000000 : ℝ) ∧
      Real.exp (2964249 / 40000000 : ℝ) ≤ (5384605977 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2964249 / 40000000 : ℝ))
    (a := (10769211953 / 10000000000 : ℝ)) (b := (5384605977 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_411 :
    (251039 / 2500000 : ℝ) ≤ Real.exp (-(22984377 / 10000000 : ℝ)) ∧
    Real.exp (-(22984377 / 10000000 : ℝ)) ≤ (1004157 / 10000000 : ℝ) := by
  have hsmall : (671542851 / 625000000 : ℝ) ≤ Real.exp (22984377 / 320000000 : ℝ) ∧
      Real.exp (22984377 / 320000000 : ℝ) ≤ (10744685617 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (22984377 / 320000000 : ℝ))
    (a := (671542851 / 625000000 : ℝ)) (b := (10744685617 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_412 :
    (2264227 / 10000000 : ℝ) ≤ Real.exp (-(1521 / 1024 : ℝ)) ∧
    Real.exp (-(1521 / 1024 : ℝ)) ≤ (566057 / 2500000 : ℝ) := by
  have hsmall : (2095022759 / 2000000000 : ℝ) ≤ Real.exp (1521 / 32768 : ℝ) ∧
      Real.exp (1521 / 32768 : ℝ) ≤ (2618778449 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1521 / 32768 : ℝ))
    (a := (2095022759 / 2000000000 : ℝ)) (b := (2618778449 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_413 :
    (407067 / 125000 : ℝ) ≤ Real.exp (1209 / 1024 : ℝ) ∧
    Real.exp (1209 / 1024 : ℝ) ≤ (32565361 / 10000000 : ℝ) := by
  have hsmall : (6484905306287 / 6250000000000 : ℝ) ≤ Real.exp (1209 / 32768 : ℝ) ∧
      Real.exp (1209 / 32768 : ℝ) ≤ (103758484900593 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1209 / 32768 : ℝ))
    (a := (6484905306287 / 6250000000000 : ℝ)) (b := (103758484900593 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_414 :
    (865809 / 10000000 : ℝ) ≤ Real.exp (-(382293 / 156250 : ℝ)) ∧
    Real.exp (-(382293 / 156250 : ℝ)) ≤ (86581 / 1000000 : ℝ) := by
  have hsmall : (5397287499 / 5000000000 : ℝ) ≤ Real.exp (382293 / 5000000 : ℝ) ∧
      Real.exp (382293 / 5000000 : ℝ) ≤ (10794574999 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (382293 / 5000000 : ℝ))
    (a := (5397287499 / 5000000000 : ℝ)) (b := (10794574999 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_415 :
    (933501 / 10000000 : ℝ) ≤ Real.exp (-(23713977 / 10000000 : ℝ)) ∧
    Real.exp (-(23713977 / 10000000 : ℝ)) ≤ (466751 / 5000000 : ℝ) := by
  have hsmall : (1346151431 / 1250000000 : ℝ) ≤ Real.exp (23713977 / 320000000 : ℝ) ∧
      Real.exp (23713977 / 320000000 : ℝ) ≤ (10769211449 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (23713977 / 320000000 : ℝ))
    (a := (1346151431 / 1250000000 : ℝ)) (b := (10769211449 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_416 :
    (335663 / 100000 : ℝ) ≤ Real.exp (155 / 128 : ℝ) ∧
    Real.exp (155 / 128 : ℝ) ≤ (33566301 / 10000000 : ℝ) := by
  have hsmall : (103856691534953 / 100000000000000 : ℝ) ≤ Real.exp (155 / 4096 : ℝ) ∧
      Real.exp (155 / 4096 : ℝ) ≤ (51928345767477 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (155 / 4096 : ℝ))
    (a := (103856691534953 / 100000000000000 : ℝ)) (b := (51928345767477 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_417 :
    (8290291 / 10000000 : ℝ) ≤ Real.exp (-(3 / 16 : ℝ)) ∧
    Real.exp (-(3 / 16 : ℝ)) ≤ (2072573 / 2500000 : ℝ) := by
  have hsmall : (10058765747 / 10000000000 : ℝ) ≤ Real.exp (3 / 512 : ℝ) ∧
      Real.exp (3 / 512 : ℝ) ≤ (2514691437 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3 / 512 : ℝ))
    (a := (10058765747 / 10000000000 : ℝ)) (b := (2514691437 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_418 :
    (739421 / 10000000 : ℝ) ≤ Real.exp (-(6511181 / 2500000 : ℝ)) ∧
    Real.exp (-(6511181 / 2500000 : ℝ)) ≤ (369711 / 5000000 : ℝ) := by
  have hsmall : (542396813 / 500000000 : ℝ) ≤ Real.exp (6511181 / 80000000 : ℝ) ∧
      Real.exp (6511181 / 80000000 : ℝ) ≤ (10847936261 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (6511181 / 80000000 : ℝ))
    (a := (542396813 / 500000000 : ℝ)) (b := (10847936261 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_419 :
    (86581 / 1000000 : ℝ) ≤ Real.exp (-(1223337 / 500000 : ℝ)) ∧
    Real.exp (-(1223337 / 500000 : ℝ)) ≤ (865811 / 10000000 : ℝ) := by
  have hsmall : (10794574593 / 10000000000 : ℝ) ≤ Real.exp (1223337 / 16000000 : ℝ) ∧
      Real.exp (1223337 / 16000000 : ℝ) ≤ (5397287297 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1223337 / 16000000 : ℝ))
    (a := (10794574593 / 10000000000 : ℝ)) (b := (5397287297 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_420 :
    (1785911 / 10000000 : ℝ) ≤ Real.exp (-(441 / 256 : ℝ)) ∧
    Real.exp (-(441 / 256 : ℝ)) ≤ (223239 / 1250000 : ℝ) := by
  have hsmall : (10553083591 / 10000000000 : ℝ) ≤ Real.exp (441 / 8192 : ℝ) ∧
      Real.exp (441 / 8192 : ℝ) ≤ (1319135449 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (441 / 8192 : ℝ))
    (a := (10553083591 / 10000000000 : ℝ)) (b := (1319135449 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_421 :
    (35661421 / 10000000 : ℝ) ≤ Real.exp (651 / 512 : ℝ) ∧
    Real.exp (651 / 512 : ℝ) ≤ (17830711 / 5000000 : ℝ) := by
  have hsmall : (104053383747201 / 100000000000000 : ℝ) ≤ Real.exp (651 / 16384 : ℝ) ∧
      Real.exp (651 / 16384 : ℝ) ≤ (52026691873601 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (651 / 16384 : ℝ))
    (a := (104053383747201 / 100000000000000 : ℝ)) (b := (52026691873601 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_422 :
    (8824969 / 10000000 : ℝ) ≤ Real.exp (-(1 / 8 : ℝ)) ∧
    Real.exp (-(1 / 8 : ℝ)) ≤ (882497 / 1000000 : ℝ) := by
  have hsmall : (10039138893 / 10000000000 : ℝ) ≤ Real.exp (1 / 256 : ℝ) ∧
      Real.exp (1 / 256 : ℝ) ≤ (5019569447 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1 / 256 : ℝ))
    (a := (10039138893 / 10000000000 : ℝ)) (b := (5019569447 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_423 :
    (9767 / 156250 : ℝ) ≤ Real.exp (-(1732779 / 625000 : ℝ)) ∧
    Real.exp (-(1732779 / 625000 : ℝ)) ≤ (625089 / 10000000 : ℝ) := by
  have hsmall : (436201153 / 400000000 : ℝ) ≤ Real.exp (1732779 / 20000000 : ℝ) ∧
      Real.exp (1732779 / 20000000 : ℝ) ≤ (5452514413 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1732779 / 20000000 : ℝ))
    (a := (436201153 / 400000000 : ℝ)) (b := (5452514413 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_424 :
    (369711 / 5000000 : ℝ) ≤ Real.exp (-(26044711 / 10000000 : ℝ)) ∧
    Real.exp (-(26044711 / 10000000 : ℝ)) ≤ (739423 / 10000000 : ℝ) := by
  have hsmall : (10847935819 / 10000000000 : ℝ) ≤ Real.exp (26044711 / 320000000 : ℝ) ∧
      Real.exp (26044711 / 320000000 : ℝ) ≤ (542396791 / 500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (26044711 / 320000000 : ℝ))
    (a := (10847935819 / 10000000000 : ℝ)) (b := (542396791 / 500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_425 :
    (754887 / 5000000 : ℝ) ≤ Real.exp (-(121 / 64 : ℝ)) ∧
    Real.exp (-(121 / 64 : ℝ)) ≤ (60391 / 400000 : ℝ) := by
  have hsmall : (1060862261 / 1000000000 : ℝ) ≤ Real.exp (121 / 2048 : ℝ) ∧
      Real.exp (121 / 2048 : ℝ) ≤ (10608622611 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (121 / 2048 : ℝ))
    (a := (1060862261 / 1000000000 : ℝ)) (b := (10608622611 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_426 :
    (18943657 / 5000000 : ℝ) ≤ Real.exp (341 / 256 : ℝ) ∧
    Real.exp (341 / 256 : ℝ) ≤ (7577463 / 2000000 : ℝ) := by
  have hsmall : (104250448471087 / 100000000000000 : ℝ) ≤ Real.exp (341 / 8192 : ℝ) ∧
      Real.exp (341 / 8192 : ℝ) ≤ (6515653029443 / 6250000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (341 / 8192 : ℝ))
    (a := (104250448471087 / 100000000000000 : ℝ)) (b := (6515653029443 / 6250000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_427 :
    (522741 / 10000000 : ℝ) ≤ Real.exp (-(29512537 / 10000000 : ℝ)) ∧
    Real.exp (-(29512537 / 10000000 : ℝ)) ≤ (261371 / 5000000 : ℝ) := by
  have hsmall : (10966133721 / 10000000000 : ℝ) ≤ Real.exp (29512537 / 320000000 : ℝ) ∧
      Real.exp (29512537 / 320000000 : ℝ) ≤ (5483066861 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (29512537 / 320000000 : ℝ))
    (a := (10966133721 / 10000000000 : ℝ)) (b := (5483066861 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_428 :
    (625089 / 10000000 : ℝ) ≤ Real.exp (-(6931113 / 2500000 : ℝ)) ∧
    Real.exp (-(6931113 / 2500000 : ℝ)) ≤ (62509 / 1000000 : ℝ) := by
  have hsmall : (170391069 / 156250000 : ℝ) ≤ Real.exp (6931113 / 80000000 : ℝ) ∧
      Real.exp (6931113 / 80000000 : ℝ) ≤ (10905028417 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (6931113 / 80000000 : ℝ))
    (a := (170391069 / 156250000 : ℝ)) (b := (10905028417 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_429 :
    (40252141 / 10000000 : ℝ) ≤ Real.exp (713 / 512 : ℝ) ∧
    Real.exp (713 / 512 : ℝ) ≤ (20126071 / 5000000 : ℝ) := by
  have hsmall : (13055985801513 / 12500000000000 : ℝ) ≤ Real.exp (713 / 16384 : ℝ) ∧
      Real.exp (713 / 16384 : ℝ) ≤ (20889577282421 / 20000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (713 / 16384 : ℝ))
    (a := (13055985801513 / 12500000000000 : ℝ)) (b := (20889577282421 / 20000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_430 :
    (432139 / 10000000 : ℝ) ≤ Real.exp (-(3141593 / 1000000 : ℝ)) ∧
    Real.exp (-(3141593 / 1000000 : ℝ)) ≤ (21607 / 500000 : ℝ) := by
  have hsmall : (11031555791 / 10000000000 : ℝ) ≤ Real.exp (3141593 / 32000000 : ℝ) ∧
      Real.exp (3141593 / 32000000 : ℝ) ≤ (689472237 / 625000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3141593 / 32000000 : ℝ))
    (a := (11031555791 / 10000000000 : ℝ)) (b := (689472237 / 625000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_431 :
    (261371 / 5000000 : ℝ) ≤ Real.exp (-(29512523 / 10000000 : ℝ)) ∧
    Real.exp (-(29512523 / 10000000 : ℝ)) ≤ (522743 / 10000000 : ℝ) := by
  have hsmall : (10966133241 / 10000000000 : ℝ) ≤ Real.exp (29512523 / 320000000 : ℝ) ∧
      Real.exp (29512523 / 320000000 : ℝ) ≤ (5483066621 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (29512523 / 320000000 : ℝ))
    (a := (10966133241 / 10000000000 : ℝ)) (b := (5483066621 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_432 :
    (131749 / 1250000 : ℝ) ≤ Real.exp (-(9 / 4 : ℝ)) ∧
    Real.exp (-(9 / 4 : ℝ)) ≤ (1053993 / 10000000 : ℝ) := by
  have hsmall : (2682108481 / 2500000000 : ℝ) ≤ Real.exp (9 / 128 : ℝ) ∧
      Real.exp (9 / 128 : ℝ) ≤ (429137357 / 400000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (9 / 128 : ℝ))
    (a := (2682108481 / 2500000000 : ℝ)) (b := (429137357 / 400000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_433 :
    (1710583 / 400000 : ℝ) ≤ Real.exp (93 / 64 : ℝ) ∧
    Real.exp (93 / 64 : ℝ) ≤ (1336393 / 312500 : ℝ) := by
  have hsmall : (52322849138541 / 50000000000000 : ℝ) ≤ Real.exp (93 / 2048 : ℝ) ∧
      Real.exp (93 / 2048 : ℝ) ≤ (104645698277083 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (93 / 2048 : ℝ))
    (a := (52322849138541 / 50000000000000 : ℝ)) (b := (104645698277083 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_434 :
    (665309 / 625000 : ℝ) ≤ Real.exp (1 / 16 : ℝ) ∧
    Real.exp (1 / 16 : ℝ) ≤ (2128989 / 2000000 : ℝ) := by
  have hsmall : (1001955033591 / 1000000000000 : ℝ) ≤ Real.exp (1 / 512 : ℝ) ∧
      Real.exp (1 / 512 : ℝ) ≤ (100195503359101 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1 / 512 : ℝ))
    (a := (1001955033591 / 1000000000000 : ℝ)) (b := (100195503359101 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_435 :
    (352881 / 10000000 : ℝ) ≤ Real.exp (-(6688417 / 2000000 : ℝ)) ∧
    Real.exp (-(6688417 / 2000000 : ℝ)) ≤ (176441 / 5000000 : ℝ) := by
  have hsmall : (346925821 / 312500000 : ℝ) ≤ Real.exp (6688417 / 64000000 : ℝ) ∧
      Real.exp (6688417 / 64000000 : ℝ) ≤ (11101626273 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (6688417 / 64000000 : ℝ))
    (a := (346925821 / 312500000 : ℝ)) (b := (11101626273 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_436 :
    (432139 / 10000000 : ℝ) ≤ Real.exp (-(392699 / 125000 : ℝ)) ∧
    Real.exp (-(392699 / 125000 : ℝ)) ≤ (21607 / 500000 : ℝ) := by
  have hsmall : (5515777723 / 5000000000 : ℝ) ≤ Real.exp (392699 / 4000000 : ℝ) ∧
      Real.exp (392699 / 4000000 : ℝ) ≤ (11031555447 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (392699 / 4000000 : ℝ))
    (a := (5515777723 / 5000000000 : ℝ)) (b := (11031555447 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_437 :
    (870383 / 10000000 : ℝ) ≤ Real.exp (-(625 / 256 : ℝ)) ∧
    Real.exp (-(625 / 256 : ℝ)) ≤ (54399 / 625000 : ℝ) := by
  have hsmall : (10792797767 / 10000000000 : ℝ) ≤ Real.exp (625 / 8192 : ℝ) ∧
      Real.exp (625 / 8192 : ℝ) ≤ (1349099721 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (625 / 8192 : ℝ))
    (a := (10792797767 / 10000000000 : ℝ)) (b := (1349099721 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_438 :
    (45433829 / 10000000 : ℝ) ≤ Real.exp (775 / 512 : ℝ) ∧
    Real.exp (775 / 512 : ℝ) ≤ (4543383 / 1000000 : ℝ) := by
  have hsmall : (26210971193547 / 25000000000000 : ℝ) ≤ Real.exp (775 / 16384 : ℝ) ∧
      Real.exp (775 / 16384 : ℝ) ≤ (104843884774189 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (775 / 16384 : ℝ))
    (a := (26210971193547 / 25000000000000 : ℝ)) (b := (104843884774189 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_439 :
    (2832871 / 2500000 : ℝ) ≤ Real.exp (1 / 8 : ℝ) ∧
    Real.exp (1 / 8 : ℝ) ≤ (2266297 / 2000000 : ℝ) := by
  have hsmall : (50195694466917 / 50000000000000 : ℝ) ≤ Real.exp (1 / 256 : ℝ) ∧
      Real.exp (1 / 256 : ℝ) ≤ (20078277786767 / 20000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1 / 256 : ℝ))
    (a := (50195694466917 / 50000000000000 : ℝ)) (b := (20078277786767 / 20000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_440 :
    (284419 / 10000000 : ℝ) ≤ Real.exp (-(17799457 / 5000000 : ℝ)) ∧
    Real.exp (-(17799457 / 5000000 : ℝ)) ≤ (14221 / 500000 : ℝ) := by
  have hsmall : (5588352487 / 5000000000 : ℝ) ≤ Real.exp (17799457 / 160000000 : ℝ) ∧
      Real.exp (17799457 / 160000000 : ℝ) ≤ (447068199 / 400000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (17799457 / 160000000 : ℝ))
    (a := (5588352487 / 5000000000 : ℝ)) (b := (447068199 / 400000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_441 :
    (352881 / 10000000 : ℝ) ≤ Real.exp (-(3344207 / 1000000 : ℝ)) ∧
    Real.exp (-(3344207 / 1000000 : ℝ)) ≤ (176441 / 5000000 : ℝ) := by
  have hsmall : (1387703219 / 1250000000 : ℝ) ≤ Real.exp (3344207 / 32000000 : ℝ) ∧
      Real.exp (3344207 / 32000000 : ℝ) ≤ (11101625753 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3344207 / 32000000 : ℝ))
    (a := (1387703219 / 1250000000 : ℝ)) (b := (11101625753 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_442 :
    (356583 / 5000000 : ℝ) ≤ Real.exp (-(169 / 64 : ℝ)) ∧
    Real.exp (-(169 / 64 : ℝ)) ≤ (713167 / 10000000 : ℝ) := by
  have hsmall : (2172039769 / 2000000000 : ℝ) ≤ Real.exp (169 / 2048 : ℝ) ∧
      Real.exp (169 / 2048 : ℝ) ≤ (5430099423 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (169 / 2048 : ℝ))
    (a := (2172039769 / 2000000000 : ℝ)) (b := (5430099423 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_443 :
    (4826969 / 1000000 : ℝ) ≤ Real.exp (403 / 256 : ℝ) ∧
    Real.exp (403 / 256 : ℝ) ≤ (48269691 / 10000000 : ℝ) := by
  have hsmall : (10504244661293 / 10000000000000 : ℝ) ≤ Real.exp (403 / 8192 : ℝ) ∧
      Real.exp (403 / 8192 : ℝ) ≤ (105042446612931 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (403 / 8192 : ℝ))
    (a := (10504244661293 / 10000000000000 : ℝ)) (b := (105042446612931 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_444 :
    (6031151 / 5000000 : ℝ) ≤ Real.exp (3 / 16 : ℝ) ∧
    Real.exp (3 / 16 : ℝ) ≤ (12062303 / 10000000 : ℝ) := by
  have hsmall : (100587657471447 / 100000000000000 : ℝ) ≤ Real.exp (3 / 512 : ℝ) ∧
      Real.exp (3 / 512 : ℝ) ≤ (12573457183931 / 12500000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (3 / 512 : ℝ))
    (a := (100587657471447 / 100000000000000 : ℝ)) (b := (12573457183931 / 12500000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_445 :
    (28259 / 1250000 : ℝ) ≤ Real.exp (-(37894847 / 10000000 : ℝ)) ∧
    Real.exp (-(37894847 / 10000000 : ℝ)) ≤ (226073 / 10000000 : ℝ) := by
  have hsmall : (703573991 / 625000000 : ℝ) ≤ Real.exp (37894847 / 320000000 : ℝ) ∧
      Real.exp (37894847 / 320000000 : ℝ) ≤ (11257183857 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (37894847 / 320000000 : ℝ))
    (a := (703573991 / 625000000 : ℝ)) (b := (11257183857 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_446 :
    (284419 / 10000000 : ℝ) ≤ Real.exp (-(35598899 / 10000000 : ℝ)) ∧
    Real.exp (-(35598899 / 10000000 : ℝ)) ≤ (14221 / 500000 : ℝ) := by
  have hsmall : (223534089 / 200000000 : ℝ) ≤ Real.exp (35598899 / 320000000 : ℝ) ∧
      Real.exp (35598899 / 320000000 : ℝ) ≤ (11176704451 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (35598899 / 320000000 : ℝ))
    (a := (223534089 / 200000000 : ℝ)) (b := (11176704451 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_447 :
    (2899 / 50000 : ℝ) ≤ Real.exp (-(729 / 256 : ℝ)) ∧
    Real.exp (-(729 / 256 : ℝ)) ≤ (579801 / 10000000 : ℝ) := by
  have hsmall : (10930689143 / 10000000000 : ℝ) ≤ Real.exp (729 / 8192 : ℝ) ∧
      Real.exp (729 / 8192 : ℝ) ≤ (1366336143 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (729 / 8192 : ℝ))
    (a := (10930689143 / 10000000000 : ℝ)) (b := (1366336143 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_448 :
    (51282559 / 10000000 : ℝ) ≤ Real.exp (837 / 512 : ℝ) ∧
    Real.exp (837 / 512 : ℝ) ≤ (80129 / 15625 : ℝ) := by
  have hsmall : (105241384504161 / 100000000000000 : ℝ) ≤ Real.exp (837 / 16384 : ℝ) ∧
      Real.exp (837 / 16384 : ℝ) ≤ (52620692252081 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (837 / 16384 : ℝ))
    (a := (105241384504161 / 100000000000000 : ℝ)) (b := (52620692252081 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_449 :
    (6420127 / 5000000 : ℝ) ≤ Real.exp (1 / 4 : ℝ) ∧
    Real.exp (1 / 4 : ℝ) ≤ (2568051 / 2000000 : ℝ) := by
  have hsmall : (25196077430161 / 25000000000000 : ℝ) ≤ Real.exp (1 / 128 : ℝ) ∧
      Real.exp (1 / 128 : ℝ) ≤ (20156861944129 / 20000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1 / 128 : ℝ))
    (a := (25196077430161 / 25000000000000 : ℝ)) (b := (20156861944129 / 20000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_450 :
    (177053 / 10000000 : ℝ) ≤ Real.exp (-(5042357 / 1250000 : ℝ)) ∧
    Real.exp (-(5042357 / 1250000 : ℝ)) ≤ (35411 / 2000000 : ℝ) := by
  have hsmall : (5671745039 / 5000000000 : ℝ) ≤ Real.exp (5042357 / 40000000 : ℝ) ∧
      Real.exp (5042357 / 40000000 : ℝ) ≤ (11343490079 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5042357 / 40000000 : ℝ))
    (a := (5671745039 / 5000000000 : ℝ)) (b := (11343490079 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_451 :
    (28259 / 1250000 : ℝ) ≤ Real.exp (-(37894831 / 10000000 : ℝ)) ∧
    Real.exp (-(37894831 / 10000000 : ℝ)) ≤ (226073 / 10000000 : ℝ) := by
  have hsmall : (11257183293 / 10000000000 : ℝ) ≤ Real.exp (37894831 / 320000000 : ℝ) ∧
      Real.exp (37894831 / 320000000 : ℝ) ≤ (5628591647 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (37894831 / 320000000 : ℝ))
    (a := (11257183293 / 10000000000 : ℝ)) (b := (5628591647 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_452 :
    (233853 / 5000000 : ℝ) ≤ Real.exp (-(49 / 16 : ℝ)) ∧
    Real.exp (-(49 / 16 : ℝ)) ≤ (467707 / 10000000 : ℝ) := by
  have hsmall : (5502161623 / 5000000000 : ℝ) ≤ Real.exp (49 / 512 : ℝ) ∧
      Real.exp (49 / 512 : ℝ) ≤ (11004323247 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (49 / 512 : ℝ))
    (a := (5502161623 / 5000000000 : ℝ)) (b := (11004323247 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_453 :
    (54483483 / 10000000 : ℝ) ≤ Real.exp (217 / 128 : ℝ) ∧
    Real.exp (217 / 128 : ℝ) ≤ (13620871 / 2500000 : ℝ) := by
  have hsmall : (105440699160079 / 100000000000000 : ℝ) ≤ Real.exp (217 / 4096 : ℝ) ∧
      Real.exp (217 / 4096 : ℝ) ≤ (1318008739501 / 1250000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (217 / 4096 : ℝ))
    (a := (105440699160079 / 100000000000000 : ℝ)) (b := (1318008739501 / 1250000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_454 :
    (7274957 / 5000000 : ℝ) ≤ Real.exp (3 / 8 : ℝ) ∧
    Real.exp (3 / 8 : ℝ) ≤ (2909983 / 2000000 : ℝ) := by
  have hsmall : (101178768355933 / 100000000000000 : ℝ) ≤ Real.exp (3 / 256 : ℝ) ∧
      Real.exp (3 / 256 : ℝ) ≤ (50589384177967 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (3 / 256 : ℝ))
    (a := (101178768355933 / 100000000000000 : ℝ)) (b := (50589384177967 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_455 :
    (25869 / 2500000 : ℝ) ≤ Real.exp (-(5713739 / 1250000 : ℝ)) ∧
    Real.exp (-(5713739 / 1250000 : ℝ)) ≤ (103477 / 10000000 : ℝ) := by
  have hsmall : (5767746141 / 5000000000 : ℝ) ≤ Real.exp (5713739 / 40000000 : ℝ) ∧
      Real.exp (5713739 / 40000000 : ℝ) ≤ (11535492283 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5713739 / 40000000 : ℝ))
    (a := (5767746141 / 5000000000 : ℝ)) (b := (11535492283 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_456 :
    (88527 / 5000000 : ℝ) ≤ Real.exp (-(40338839 / 10000000 : ℝ)) ∧
    Real.exp (-(40338839 / 10000000 : ℝ)) ≤ (35411 / 2000000 : ℝ) := by
  have hsmall : (453739579 / 400000000 : ℝ) ≤ Real.exp (40338839 / 320000000 : ℝ) ∧
      Real.exp (40338839 / 320000000 : ℝ) ≤ (2835872369 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (40338839 / 320000000 : ℝ))
    (a := (453739579 / 400000000 : ℝ)) (b := (2835872369 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_457 :
    (74323 / 2500000 : ℝ) ≤ Real.exp (-(225 / 64 : ℝ)) ∧
    Real.exp (-(225 / 64 : ℝ)) ≤ (297293 / 10000000 : ℝ) := by
  have hsmall : (11161254647 / 10000000000 : ℝ) ≤ Real.exp (225 / 2048 : ℝ) ∧
      Real.exp (225 / 2048 : ℝ) ≤ (1395156831 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (225 / 2048 : ℝ))
    (a := (11161254647 / 10000000000 : ℝ)) (b := (1395156831 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_458 :
    (61497181 / 10000000 : ℝ) ≤ Real.exp (465 / 256 : ℝ) ∧
    Real.exp (465 / 256 : ℝ) ≤ (30748591 / 5000000 : ℝ) := by
  have hsmall : (1323005770269 / 1250000000000 : ℝ) ≤ Real.exp (465 / 8192 : ℝ) ∧
      Real.exp (465 / 8192 : ℝ) ≤ (105840461621521 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (465 / 8192 : ℝ))
    (a := (1323005770269 / 1250000000000 : ℝ)) (b := (105840461621521 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_459 :
    (4121803 / 2500000 : ℝ) ≤ Real.exp (1 / 2 : ℝ) ∧
    Real.exp (1 / 2 : ℝ) ≤ (16487213 / 10000000 : ℝ) := by
  have hsmall : (25393692714667 / 25000000000000 : ℝ) ≤ Real.exp (1 / 64 : ℝ) ∧
      Real.exp (1 / 64 : ℝ) ≤ (101574770858669 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (1 / 64 : ℝ))
    (a := (25393692714667 / 25000000000000 : ℝ)) (b := (101574770858669 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_460 :
    (56301 / 10000000 : ℝ) ≤ Real.exp (-(51796113 / 10000000 : ℝ)) ∧
    Real.exp (-(51796113 / 10000000 : ℝ)) ≤ (28151 / 5000000 : ℝ) := by
  have hsmall : (2939247467 / 2500000000 : ℝ) ≤ Real.exp (51796113 / 320000000 : ℝ) ∧
      Real.exp (51796113 / 320000000 : ℝ) ≤ (11756989869 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (51796113 / 320000000 : ℝ))
    (a := (2939247467 / 2500000000 : ℝ)) (b := (11756989869 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_461 :
    (103477 / 10000000 : ℝ) ≤ Real.exp (-(45709893 / 10000000 : ℝ)) ∧
    Real.exp (-(45709893 / 10000000 : ℝ)) ≤ (51739 / 5000000 : ℝ) := by
  have hsmall : (11535491597 / 10000000000 : ℝ) ≤ Real.exp (45709893 / 320000000 : ℝ) ∧
      Real.exp (45709893 / 320000000 : ℝ) ≤ (5767745799 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (45709893 / 320000000 : ℝ))
    (a := (11535491597 / 10000000000 : ℝ)) (b := (5767745799 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_462 :
    (45789 / 2500000 : ℝ) ≤ Real.exp (-(4 / 1 : ℝ)) ∧
    Real.exp (-(4 / 1 : ℝ)) ≤ (183157 / 10000000 : ℝ) := by
  have hsmall : (1133148453 / 1000000000 : ℝ) ≤ Real.exp (1 / 8 : ℝ) ∧
      Real.exp (1 / 8 : ℝ) ≤ (11331484531 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1 / 8 : ℝ))
    (a := (1133148453 / 1000000000 : ℝ)) (b := (11331484531 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_463 :
    (18682459 / 10000000 : ℝ) ≤ Real.exp (5 / 8 : ℝ) ∧
    Real.exp (5 / 8 : ℝ) ≤ (934123 / 500000 : ℝ) := by
  have hsmall : (101972323271377 / 100000000000000 : ℝ) ≤ Real.exp (5 / 256 : ℝ) ∧
      Real.exp (5 / 256 : ℝ) ≤ (50986161635689 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (5 / 256 : ℝ))
    (a := (101972323271377 / 100000000000000 : ℝ)) (b := (50986161635689 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_464 :
    (28249 / 10000000 : ℝ) ≤ Real.exp (-(29346343 / 5000000 : ℝ)) ∧
    Real.exp (-(29346343 / 5000000 : ℝ)) ≤ (113 / 40000 : ℝ) := by
  have hsmall : (2402624843 / 2000000000 : ℝ) ≤ Real.exp (29346343 / 160000000 : ℝ) ∧
      Real.exp (29346343 / 160000000 : ℝ) ≤ (1501640527 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (29346343 / 160000000 : ℝ))
    (a := (2402624843 / 2000000000 : ℝ)) (b := (1501640527 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_465 :
    (28151 / 5000000 : ℝ) ≤ Real.exp (-(51796093 / 10000000 : ℝ)) ∧
    Real.exp (-(51796093 / 10000000 : ℝ)) ≤ (56303 / 10000000 : ℝ) := by
  have hsmall : (11756989133 / 10000000000 : ℝ) ≤ Real.exp (51796093 / 320000000 : ℝ) ∧
      Real.exp (51796093 / 320000000 : ℝ) ≤ (5878494567 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (51796093 / 320000000 : ℝ))
    (a := (11756989133 / 10000000000 : ℝ)) (b := (5878494567 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_466 :
    (109367 / 10000000 : ℝ) ≤ Real.exp (-(289 / 64 : ℝ)) ∧
    Real.exp (-(289 / 64 : ℝ)) ≤ (13671 / 1250000 : ℝ) := by
  have hsmall : (11515550901 / 10000000000 : ℝ) ≤ Real.exp (289 / 2048 : ℝ) ∧
      Real.exp (289 / 2048 : ℝ) ≤ (5757775451 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (289 / 2048 : ℝ))
    (a := (11515550901 / 10000000000 : ℝ)) (b := (5757775451 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_467 :
    (2117 / 1000 : ℝ) ≤ Real.exp (3 / 4 : ℝ) ∧
    Real.exp (3 / 4 : ℝ) ≤ (21170001 / 10000000 : ℝ) := by
  have hsmall : (20474286332047 / 20000000000000 : ℝ) ≤ Real.exp (3 / 128 : ℝ) ∧
      Real.exp (3 / 128 : ℝ) ≤ (25592857915059 / 25000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (3 / 128 : ℝ))
    (a := (20474286332047 / 20000000000000 : ℝ)) (b := (25592857915059 / 25000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_468 :
    (1293 / 1000000 : ℝ) ≤ Real.exp (-(66507527 / 10000000 : ℝ)) ∧
    Real.exp (-(66507527 / 10000000 : ℝ)) ≤ (12931 / 10000000 : ℝ) := by
  have hsmall : (615505647 / 500000000 : ℝ) ≤ Real.exp (66507527 / 320000000 : ℝ) ∧
      Real.exp (66507527 / 320000000 : ℝ) ≤ (12310112941 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (66507527 / 320000000 : ℝ))
    (a := (615505647 / 500000000 : ℝ)) (b := (12310112941 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_469 :
    (28249 / 10000000 : ℝ) ≤ Real.exp (-(58692663 / 10000000 : ℝ)) ∧
    Real.exp (-(58692663 / 10000000 : ℝ)) ≤ (113 / 40000 : ℝ) := by
  have hsmall : (12013123351 / 10000000000 : ℝ) ≤ Real.exp (58692663 / 320000000 : ℝ) ∧
      Real.exp (58692663 / 320000000 : ℝ) ≤ (1501640419 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (58692663 / 320000000 : ℝ))
    (a := (12013123351 / 10000000000 : ℝ)) (b := (1501640419 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_470 :
    (63297 / 10000000 : ℝ) ≤ Real.exp (-(81 / 16 : ℝ)) ∧
    Real.exp (-(81 / 16 : ℝ)) ≤ (31649 / 5000000 : ℝ) := by
  have hsmall : (73212757 / 62500000 : ℝ) ≤ Real.exp (81 / 512 : ℝ) ∧
      Real.exp (81 / 512 : ℝ) ≤ (11714041121 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (81 / 512 : ℝ))
    (a := (73212757 / 62500000 : ℝ)) (b := (11714041121 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_471 :
    (44217711 / 5000000 : ℝ) ≤ Real.exp (279 / 128 : ℝ) ∧
    Real.exp (279 / 128 : ℝ) ≤ (88435423 / 10000000 : ℝ) := by
  have hsmall : (53524432923153 / 50000000000000 : ℝ) ≤ Real.exp (279 / 4096 : ℝ) ∧
      Real.exp (279 / 4096 : ℝ) ≤ (107048865846307 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (279 / 4096 : ℝ))
    (a := (53524432923153 / 50000000000000 : ℝ)) (b := (107048865846307 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_472 :
    (391 / 2000000 : ℝ) ≤ Real.exp (-(42698677 / 5000000 : ℝ)) ∧
    Real.exp (-(42698677 / 5000000 : ℝ)) ≤ (489 / 2500000 : ℝ) := by
  have hsmall : (2611732807 / 2000000000 : ℝ) ≤ Real.exp (42698677 / 160000000 : ℝ) ∧
      Real.exp (42698677 / 160000000 : ℝ) ≤ (3264666009 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (42698677 / 160000000 : ℝ))
    (a := (2611732807 / 2000000000 : ℝ)) (b := (3264666009 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_473 :
    (1293 / 1000000 : ℝ) ≤ Real.exp (-(33253751 / 5000000 : ℝ)) ∧
    Real.exp (-(33253751 / 5000000 : ℝ)) ≤ (12931 / 10000000 : ℝ) := by
  have hsmall : (12310111979 / 10000000000 : ℝ) ≤ Real.exp (33253751 / 160000000 : ℝ) ∧
      Real.exp (33253751 / 160000000 : ℝ) ≤ (615505599 / 500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (33253751 / 160000000 : ℝ))
    (a := (12310111979 / 10000000000 : ℝ)) (b := (615505599 / 500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_474 :
    (2413 / 1250000 : ℝ) ≤ Real.exp (-(25 / 4 : ℝ)) ∧
    Real.exp (-(25 / 4 : ℝ)) ≤ (3861 / 2000000 : ℝ) := by
  have hsmall : (2431381661 / 2000000000 : ℝ) ≤ Real.exp (25 / 128 : ℝ) ∧
      Real.exp (25 / 128 : ℝ) ≤ (6078454153 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (25 / 128 : ℝ))
    (a := (2431381661 / 2000000000 : ℝ)) (b := (6078454153 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_475 :
    (2253393 / 200000 : ℝ) ≤ Real.exp (155 / 64 : ℝ) ∧
    Real.exp (155 / 64 : ℝ) ≤ (112669651 / 10000000 : ℝ) := by
  have hsmall : (21572424753173 / 20000000000000 : ℝ) ≤ Real.exp (155 / 2048 : ℝ) ∧
      Real.exp (155 / 2048 : ℝ) ≤ (53931061882933 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (155 / 2048 : ℝ))
    (a := (21572424753173 / 20000000000000 : ℝ)) (b := (53931061882933 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_476 :
    (4481689 / 1000000 : ℝ) ≤ Real.exp (3 / 2 : ℝ) ∧
    Real.exp (3 / 2 : ℝ) ≤ (44816891 / 10000000 : ℝ) := by
  have hsmall : (104799100201663 / 100000000000000 : ℝ) ≤ Real.exp (3 / 64 : ℝ) ∧
      Real.exp (3 / 64 : ℝ) ≤ (1637485940651 / 1562500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (3 / 64 : ℝ))
    (a := (104799100201663 / 100000000000000 : ℝ)) (b := (1637485940651 / 1562500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_477 :
    (7 / 10000000 : ℝ) ≤ Real.exp (-(8799777 / 625000 : ℝ)) ∧
    Real.exp (-(8799777 / 625000 : ℝ)) ≤ (1 / 1250000 : ℝ) := by
  have hsmall : (15526899057 / 10000000000 : ℝ) ≤ Real.exp (8799777 / 20000000 : ℝ) ∧
      Real.exp (8799777 / 20000000 : ℝ) ≤ (776344953 / 500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (8799777 / 20000000 : ℝ))
    (a := (15526899057 / 10000000000 : ℝ)) (b := (776344953 / 500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_478 :
    (391 / 2000000 : ℝ) ≤ Real.exp (-(85397323 / 10000000 : ℝ)) ∧
    Real.exp (-(85397323 / 10000000 : ℝ)) ≤ (489 / 2500000 : ℝ) := by
  have hsmall : (1305866277 / 1000000000 : ℝ) ≤ Real.exp (85397323 / 320000000 : ℝ) ∧
      Real.exp (85397323 / 320000000 : ℝ) ≤ (13058662771 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (85397323 / 320000000 : ℝ))
    (a := (1305866277 / 1000000000 : ℝ)) (b := (13058662771 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_479 :
    (617 / 5000000 : ℝ) ≤ Real.exp (-(9 / 1 : ℝ)) ∧
    Real.exp (-(9 / 1 : ℝ)) ≤ (247 / 2000000 : ℝ) := by
  have hsmall : (13247847587 / 10000000000 : ℝ) ≤ Real.exp (9 / 32 : ℝ) ∧
      Real.exp (9 / 32 : ℝ) ≤ (3311961897 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (9 / 32 : ℝ))
    (a := (13247847587 / 10000000000 : ℝ)) (b := (3311961897 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_480 :
    (91440447 / 5000000 : ℝ) ≤ Real.exp (93 / 32 : ℝ) ∧
    Real.exp (93 / 32 : ℝ) ≤ (36576179 / 2000000 : ℝ) := by
  have hsmall : (54753610839491 / 50000000000000 : ℝ) ≤ Real.exp (93 / 1024 : ℝ) ∧
      Real.exp (93 / 1024 : ℝ) ≤ (109507221678983 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (93 / 1024 : ℝ))
    (a := (54753610839491 / 50000000000000 : ℝ)) (b := (109507221678983 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_481 :
    (121824939 / 10000000 : ℝ) ≤ Real.exp (5 / 2 : ℝ) ∧
    Real.exp (5 / 2 : ℝ) ≤ (6091247 / 500000 : ℝ) := by
  have hsmall : (108125780744903 / 100000000000000 : ℝ) ≤ Real.exp (5 / 64 : ℝ) ∧
      Real.exp (5 / 64 : ℝ) ≤ (13515722593113 / 12500000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (5 / 64 : ℝ))
    (a := (108125780744903 / 100000000000000 : ℝ)) (b := (13515722593113 / 12500000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_482 :
    (0 : ℝ) ≤ Real.exp (-(382724379 / 10000000 : ℝ)) ∧
    Real.exp (-(382724379 / 10000000 : ℝ)) ≤ (1 / 1048576 : ℝ) :=
  neg_enclosure_of_twenty_le (by norm_num)

theorem n1_exp_483 :
    (7 / 10000000 : ℝ) ≤ Real.exp (-(140796383 / 10000000 : ℝ)) ∧
    Real.exp (-(140796383 / 10000000 : ℝ)) ≤ (1 / 1250000 : ℝ) := by
  have hsmall : (388172417 / 250000000 : ℝ) ≤ Real.exp (140796383 / 320000000 : ℝ) ∧
      Real.exp (140796383 / 320000000 : ℝ) ≤ (7763448341 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (140796383 / 320000000 : ℝ))
    (a := (388172417 / 250000000 : ℝ)) (b := (7763448341 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_484 :
    (1 / 10000000 : ℝ) ≤ Real.exp (-(16 / 1 : ℝ)) ∧
    Real.exp (-(16 / 1 : ℝ)) ≤ (1 / 5000000 : ℝ) := by
  have hsmall : (16487212701 / 10000000000 : ℝ) ≤ Real.exp (1 / 2 : ℝ) ∧
      Real.exp (1 / 2 : ℝ) ≤ (4121803177 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1 / 2 : ℝ))
    (a := (16487212701 / 10000000000 : ℝ)) (b := (4121803177 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_485 :
    (900171313 / 10000000 : ℝ) ≤ Real.exp (9 / 2 : ℝ) ∧
    Real.exp (9 / 2 : ℝ) ≤ (450085657 / 5000000 : ℝ) := by
  have hsmall : (115099294469117 / 100000000000000 : ℝ) ≤ Real.exp (9 / 64 : ℝ) ∧
      Real.exp (9 / 64 : ℝ) ≤ (57549647234559 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (9 / 64 : ℝ))
    (a := (115099294469117 / 100000000000000 : ℝ)) (b := (57549647234559 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_486 :
    (0 : ℝ) ≤ Real.exp (-(2827971899 / 10000000 : ℝ)) ∧
    Real.exp (-(2827971899 / 10000000 : ℝ)) ≤ (1 / 1048576 : ℝ) :=
  neg_enclosure_of_twenty_le (by norm_num)

theorem n1_exp_487 :
    (0 : ℝ) ≤ Real.exp (-(382724253 / 10000000 : ℝ)) ∧
    Real.exp (-(382724253 / 10000000 : ℝ)) ≤ (1 / 1048576 : ℝ) :=
  neg_enclosure_of_twenty_le (by norm_num)

theorem n1_exp_488 :
    (0 : ℝ) ≤ Real.exp (-(36 / 1 : ℝ)) ∧
    Real.exp (-(36 / 1 : ℝ)) ≤ (1 / 1048576 : ℝ) :=
  neg_enclosure_of_twenty_le (by norm_num)

theorem n1_exp_489 :
    (3344542169 / 10000000 : ℝ) ≤ Real.exp (93 / 16 : ℝ) ∧
    Real.exp (93 / 16 : ℝ) ≤ (334454217 / 1000000 : ℝ) := by
  have hsmall : (59959157999249 / 50000000000000 : ℝ) ≤ Real.exp (93 / 512 : ℝ) ∧
      Real.exp (93 / 512 : ℝ) ≤ (119918315998499 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (93 / 512 : ℝ))
    (a := (59959157999249 / 50000000000000 : ℝ)) (b := (119918315998499 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_490 :
    (665141633 / 1000000 : ℝ) ≤ Real.exp (13 / 2 : ℝ) ∧
    Real.exp (13 / 2 : ℝ) ≤ (6651416331 / 10000000 : ℝ) := by
  have hsmall : (12252256118773 / 10000000000000 : ℝ) ≤ Real.exp (13 / 64 : ℝ) ∧
      Real.exp (13 / 64 : ℝ) ≤ (122522561187731 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (13 / 64 : ℝ))
    (a := (12252256118773 / 10000000000000 : ℝ)) (b := (122522561187731 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_491 :
    (0 : ℝ) ≤ Real.exp (-(10448021493 / 5000000 : ℝ)) ∧
    Real.exp (-(10448021493 / 5000000 : ℝ)) ≤ (1 / 1048576 : ℝ) :=
  neg_enclosure_of_twenty_le (by norm_num)

theorem n1_exp_492 :
    (0 : ℝ) ≤ Real.exp (-(565594199 / 2000000 : ℝ)) ∧
    Real.exp (-(565594199 / 2000000 : ℝ)) ≤ (1 / 1048576 : ℝ) :=
  neg_enclosure_of_twenty_le (by norm_num)

theorem n1_exp_493 :
    (11607862073 / 5000000 : ℝ) ≤ Real.exp (31 / 4 : ℝ) ∧
    Real.exp (31 / 4 : ℝ) ≤ (23215724147 / 10000000 : ℝ) := by
  have hsmall : (63701652580983 / 50000000000000 : ℝ) ≤ Real.exp (31 / 128 : ℝ) ∧
      Real.exp (31 / 128 : ℝ) ≤ (127403305161967 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (31 / 128 : ℝ))
    (a := (63701652580983 / 50000000000000 : ℝ)) (b := (127403305161967 / 100000000000000 : ℝ))
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

/- Unchanged original pointwise certificates for this subinterval. -/
section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open MasulloRH.GaussianApproximation MasulloRH.CertifiedExp
namespace MasulloRH.HeightOne
theorem cell_074 (x : ℝ) (hx : x ∈ Set.Ioo (1 / 2 : ℝ) (33 / 64 : ℝ)) :
    density x ≤ (124527 / 25000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (3032653 / 5000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (6257841 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_376.1 n1_exp_380.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (3032653 / 5000000 : ℝ)) pi_rational_enclosure hi
  have ha : (4763679 / 2500000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (1965959 / 1000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (280043 / 2000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (59501 / 400000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_381.1 n1_exp_382.2
  have hpoly : (3476057 / 25000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (118387 / 800000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (280043 / 2000000 : ℝ))
      (by norm_num : (59501 / 400000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (3476057 / 12500000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (118387 / 400000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (1726267 / 5000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (735759 / 2000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_383.1 n1_exp_299.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1726267 / 5000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (9739417 / 25000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (10377697 / 25000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (13578143 / 5000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_384.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (9739417 / 25000000 : ℝ) (10377697 / 25000000 : ℝ) (3476057 / 12500000 : ℝ) (118387 / 400000 : ℝ)
    (4253587 / 100000000 : ℝ) (13578143 / 5000000 : ℝ) (124527 / 25000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_075 (x : ℝ) (hx : x ∈ Set.Ioo (33 / 64 : ℝ) (17 / 32 : ℝ)) :
    density x ≤ (20227 / 4000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (78223 / 125000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (3228243 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_380.1 n1_exp_385.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (78223 / 125000 : ℝ)) pi_rational_enclosure hi
  have ha : (982979 / 500000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (5070913 / 2500000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (82219 / 625000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (1400217 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_386.1 n1_exp_387.2
  have hpoly : (13078161 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (3485569 / 25000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (82219 / 625000 : ℝ))
      (by norm_num : (1400217 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (13078161 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (3485569 / 12500000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (33 / 64 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (3233867 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (690507 / 2000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_388.1 n1_exp_383.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (3233867 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (9122569 / 25000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (7791543 / 20000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (27990971 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_144.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (9122569 / 25000000 : ℝ) (7791543 / 20000000 : ℝ) (13078161 / 50000000 : ℝ) (3485569 / 12500000 : ℝ)
    (422117 / 10000000 : ℝ) (27990971 / 10000000 : ℝ) (20227 / 4000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_076 (x : ℝ) (hx : x ∈ Set.Ioo (17 / 32 : ℝ) (35 / 64 : ℝ)) :
    density x ≤ (253781 / 50000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (1291297 / 2000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (6661437 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_385.1 n1_exp_389.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1291297 / 2000000 : ℝ)) pi_rational_enclosure hi
  have ha : (20283641 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (5231881 / 2500000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (1233471 / 10000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (657753 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_390.1 n1_exp_391.2
  have hpoly : (6137407 / 50000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (2621753 / 20000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (1233471 / 10000000 : ℝ))
      (by norm_num : (657753 / 5000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (6137407 / 25000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (2621753 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (17 / 32 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (151157 / 500000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (808467 / 2500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_392.1 n1_exp_388.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (151157 / 500000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (8528119 / 25000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (456129 / 1250000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (28851311 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_393.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (8528119 / 25000000 : ℝ) (456129 / 1250000 : ℝ) (6137407 / 25000000 : ℝ) (2621753 / 10000000 : ℝ)
    (2082559 / 50000000 : ℝ) (28851311 / 10000000 : ℝ) (253781 / 50000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_077 (x : ℝ) (hx : x ∈ Set.Ioo (35 / 64 : ℝ) (9 / 16 : ℝ)) :
    density x ≤ (503707 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (1665359 / 2500000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (6872893 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_389.1 n1_exp_394.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1665359 / 2500000 : ℝ)) pi_rational_enclosure hi
  have ha : (10463757 / 5000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (21591833 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (1154193 / 10000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (1233473 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_395.1 n1_exp_396.2
  have hpoly : (11495633 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (6149619 / 50000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (1154193 / 10000000 : ℝ))
      (by norm_num : (1233473 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (11495633 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (6149619 / 25000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (35 / 64 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (2820629 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (3023141 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_397.1 n1_exp_392.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (2820629 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (6365477 / 20000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (34112519 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (14869047 / 5000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_398.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (6365477 / 20000000 : ℝ) (34112519 / 100000000 : ℝ) (11495633 / 50000000 : ℝ) (6149619 / 25000000 : ℝ)
    (408639 / 10000000 : ℝ) (14869047 / 5000000 : ℝ) (503707 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_078 (x : ℝ) (hx : x ∈ Set.Ioo (9 / 16 : ℝ) (37 / 64 : ℝ)) :
    density x ≤ (494239 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (1718223 / 2500000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (3545531 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_394.1 n1_exp_399.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1718223 / 2500000 : ℝ)) pi_rational_enclosure hi
  have ha : (10795911 / 5000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (22277231 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (215547 / 2000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (230839 / 2000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_400.1 n1_exp_401.2
  have hpoly : (335683 / 3125000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (11514969 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (215547 / 2000000 : ℝ))
      (by norm_num : (230839 / 2000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (335683 / 1562500 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (11514969 / 50000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (9 / 16 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (2626549 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (282063 / 1000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_402.1 n1_exp_397.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (2626549 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (29637427 / 100000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (1273097 / 4000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (15326067 / 5000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_403.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (29637427 / 100000000 : ℝ) (1273097 / 4000000 : ℝ) (335683 / 1562500 : ℝ) (11514969 / 50000000 : ℝ)
    (3986283 / 100000000 : ℝ) (15326067 / 5000000 : ℝ) (494239 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_079 (x : ℝ) (hx : x ∈ Set.Ioo (37 / 64 : ℝ) (19 / 32 : ℝ)) :
    density x ≤ (239713 / 50000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (7091061 / 10000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (7316157 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_399.1 n1_exp_404.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (7091061 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (1113861 / 500000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (5746097 / 2500000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (502077 / 5000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (1077737 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_405.1 n1_exp_406.2
  have hpoly : (10014557 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (2689259 / 25000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (502077 / 5000000 : ℝ))
      (by norm_num : (1077737 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (10014557 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (2689259 / 12500000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (37 / 64 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (2441051 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (52531 / 200000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_407.1 n1_exp_402.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (2441051 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (13772153 / 50000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (5927493 / 20000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (31594269 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_408.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (13772153 / 50000000 : ℝ) (5927493 / 20000000 : ℝ) (10014557 / 50000000 : ℝ) (2689259 / 12500000 : ℝ)
    (6041 / 156250 : ℝ) (31594269 / 10000000 : ℝ) (239713 / 50000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_080 (x : ℝ) (hx : x ∈ Set.Ioo (19 / 32 : ℝ) (39 / 64 : ℝ)) :
    density x ≤ (229853 / 50000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (1829039 / 2500000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (7548397 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_404.1 n1_exp_409.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1829039 / 2500000 : ℝ)) pi_rational_enclosure hi
  have ha : (22984377 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (2964249 / 1250000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (1867 / 20000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (1004157 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_410.1 n1_exp_411.2
  have hpoly : (1862933 / 20000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (10026383 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (1867 / 20000 : ℝ))
      (by norm_num : (1004157 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (1862933 / 10000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (10026383 / 50000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (19 / 32 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (2264227 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (610263 / 2500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_412.1 n1_exp_407.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (2264227 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (25549061 / 100000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (27544343 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (32565361 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_413.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (25549061 / 100000000 : ℝ) (27544343 / 100000000 : ℝ) (1862933 / 10000000 : ℝ) (10026383 / 50000000 : ℝ)
    (1863989 / 50000000 : ℝ) (32565361 / 10000000 : ℝ) (229853 / 50000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_081 (x : ℝ) (hx : x ∈ Set.Ioo (39 / 64 : ℝ) (5 / 8 : ℝ)) :
    density x ≤ (87127 / 20000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (1509679 / 2000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (973501 / 1250000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_409.1 n1_exp_157.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1509679 / 2000000 : ℝ)) pi_rational_enclosure hi
  have ha : (23713977 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (382293 / 156250 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (865809 / 10000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (466751 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_414.1 n1_exp_415.2
  have hpoly : (4321451 / 50000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (4661891 / 50000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (865809 / 10000000 : ℝ))
      (by norm_num : (466751 / 5000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (4321451 / 25000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (4661891 / 25000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (39 / 64 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (2096113 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (566057 / 2500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_225.1 n1_exp_412.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (2096113 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (11826049 / 50000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (3193637 / 12500000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (33566301 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_416.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (11826049 / 50000000 : ℝ) (3193637 / 12500000 : ℝ) (4321451 / 25000000 : ℝ) (4661891 / 25000000 : ℝ)
    (1786673 / 50000000 : ℝ) (33566301 / 10000000 : ℝ) (87127 / 20000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_082 (x : ℝ) (hx : x ∈ Set.Ioo (5 / 8 : ℝ) (21 / 32 : ℝ)) :
    density x ≤ (942741 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (7788007 / 10000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (2072573 / 2500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_157.1 n1_exp_417.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (7788007 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (1223337 / 500000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (6511181 / 2500000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (739421 / 10000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (865811 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_418.1 n1_exp_419.2
  have hpoly : (7382971 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (2163033 / 25000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (739421 / 10000000 : ℝ))
      (by norm_num : (865811 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (7382971 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (2163033 / 12500000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5 / 8 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (1785911 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (1048057 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_420.1 n1_exp_225.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1785911 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (5037961 / 25000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (5913033 / 25000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (17830711 / 5000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_421.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (5037961 / 25000000 : ℝ) (5913033 / 25000000 : ℝ) (7382971 / 50000000 : ℝ) (2163033 / 12500000 : ℝ)
    (2556191 / 50000000 : ℝ) (17830711 / 5000000 : ℝ) (942741 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_083 (x : ℝ) (hx : x ∈ Set.Ioo (21 / 32 : ℝ) (11 / 16 : ℝ)) :
    density x ≤ (793167 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (8290291 / 10000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (882497 / 1000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_417.1 n1_exp_422.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (8290291 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (26044711 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (1732779 / 625000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (9767 / 156250 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (739423 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_423.1 n1_exp_424.2
  have hpoly : (6244901 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (7391177 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (9767 / 156250 : ℝ))
      (by norm_num : (739423 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (6244901 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (7391177 / 50000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (21 / 32 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (754887 / 5000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (223239 / 1250000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_425.1 n1_exp_420.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (754887 / 5000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (4258993 / 25000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (10075937 / 50000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (7577463 / 2000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_426.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (4258993 / 25000000 : ℝ) (10075937 / 50000000 : ℝ) (6244901 / 50000000 : ℝ) (7391177 / 50000000 : ℝ)
    (909253 / 20000000 : ℝ) (7577463 / 2000000 : ℝ) (793167 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_084 (x : ℝ) (hx : x ∈ Set.Ioo (11 / 16 : ℝ) (23 / 32 : ℝ)) :
    density x ≤ (640073 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (8824969 / 10000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (9394131 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_422.1 n1_exp_198.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (8824969 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (6931113 / 2500000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (29512537 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (522741 / 10000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (62509 / 1000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_427.1 n1_exp_428.2
  have hpoly : (1306089 / 25000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (6249407 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (522741 / 10000000 : ℝ))
      (by norm_num : (62509 / 1000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (1306089 / 12500000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (6249407 / 50000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (11 / 16 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (1583 / 12500 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (60391 / 400000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_037.1 n1_exp_425.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1583 / 12500 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (14289791 / 100000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (4259 / 25000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (20126071 / 5000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_429.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (14289791 / 100000000 : ℝ) (4259 / 25000 : ℝ) (1306089 / 12500000 : ℝ) (6249407 / 50000000 : ℝ)
    (1979239 / 50000000 : ℝ) (20126071 / 5000000 : ℝ) (640073 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_085 (x : ℝ) (hx : x ∈ Set.Ioo (23 / 32 : ℝ) (3 / 4 : ℝ)) :
    density x ≤ (246923 / 50000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (939413 / 1000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (1 / 1 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_198.1 n1_exp_238.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (939413 / 1000000 : ℝ)) pi_rational_enclosure hi
  have ha : (29512523 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (3141593 / 1000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (432139 / 10000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (522743 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_430.1 n1_exp_431.2
  have hpoly : (539987 / 12500000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (5226733 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (432139 / 10000000 : ℝ))
      (by norm_num : (522743 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (539987 / 6250000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (5226733 / 50000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (23 / 32 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (131749 / 1250000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (1266401 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_432.1 n1_exp_037.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (131749 / 1250000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (371657 / 3125000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (1786227 / 12500000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (1336393 / 312500 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_433.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (371657 / 3125000 : ℝ) (1786227 / 12500000 : ℝ) (539987 / 6250000 : ℝ) (5226733 / 50000000 : ℝ)
    (3369037 / 100000000 : ℝ) (1336393 / 312500 : ℝ) (246923 / 50000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_086 (x : ℝ) (hx : x ∈ Set.Ioo (3 / 4 : ℝ) (25 / 32 : ℝ)) :
    density x ≤ (22671 / 6250000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (1 / 1 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (2128989 / 2000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_238.1 n1_exp_434.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1 / 1 : ℝ)) pi_rational_enclosure hi
  have ha : (392699 / 125000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (6688417 / 2000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (352881 / 10000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (21607 / 500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_435.1 n1_exp_436.2
  have hpoly : (220507 / 6250000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (432109 / 10000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (352881 / 10000000 : ℝ))
      (by norm_num : (21607 / 500000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (220507 / 3125000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (432109 / 5000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3 / 4 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (870383 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (1053993 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_437.1 n1_exp_432.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (870383 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (4910609 / 50000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (11893047 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (4543383 / 1000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_438.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (4910609 / 50000000 : ℝ) (11893047 / 100000000 : ℝ) (220507 / 3125000 : ℝ) (432109 / 5000000 : ℝ)
    (559273 / 20000000 : ℝ) (4543383 / 1000000 : ℝ) (22671 / 6250000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_087 (x : ℝ) (hx : x ∈ Set.Ioo (25 / 32 : ℝ) (13 / 16 : ℝ)) :
    density x ≤ (50439 / 20000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (665309 / 625000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (2266297 / 2000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_434.1 n1_exp_439.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (665309 / 625000 : ℝ)) pi_rational_enclosure hi
  have ha : (3344207 / 1000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (17799457 / 5000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (284419 / 10000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (176441 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_440.1 n1_exp_441.2
  have hpoly : (2843879 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (352869 / 10000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (284419 / 10000000 : ℝ))
      (by norm_num : (176441 / 5000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (2843879 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (352869 / 5000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (25 / 32 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (356583 / 5000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (54399 / 625000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_442.1 n1_exp_437.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (356583 / 5000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (1609443 / 20000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (9821239 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (48269691 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_443.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (1609443 / 20000000 : ℝ) (9821239 / 100000000 : ℝ) (2843879 / 50000000 : ℝ) (352869 / 5000000 : ℝ)
    (28207 / 1250000 : ℝ) (48269691 / 10000000 : ℝ) (50439 / 20000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_088 (x : ℝ) (hx : x ∈ Set.Ioo (13 / 16 : ℝ) (27 / 32 : ℝ)) :
    density x ≤ (1029 / 625000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (2832871 / 2500000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (12062303 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_439.1 n1_exp_444.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (2832871 / 2500000 : ℝ)) pi_rational_enclosure hi
  have ha : (35598899 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (37894847 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (28259 / 1250000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (14221 / 500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_445.1 n1_exp_446.2
  have hpoly : (2260589 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (711037 / 25000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (28259 / 1250000 : ℝ))
      (by norm_num : (14221 / 500000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (2260589 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (711037 / 12500000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (13 / 16 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (2899 / 50000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (713167 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_447.1 n1_exp_442.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (2899 / 50000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (6542341 / 100000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (4023617 / 50000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (80129 / 15625 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_448.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (6542341 / 100000000 : ℝ) (4023617 / 50000000 : ℝ) (2260589 / 50000000 : ℝ) (711037 / 12500000 : ℝ)
    (440643 / 25000000 : ℝ) (80129 / 15625 : ℝ) (1029 / 625000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_089 (x : ℝ) (hx : x ∈ Set.Ioo (27 / 32 : ℝ) (7 / 8 : ℝ)) :
    density x ≤ (53529 / 50000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (6031151 / 5000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (2568051 / 2000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_444.1 n1_exp_449.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (6031151 / 5000000 : ℝ)) pi_rational_enclosure hi
  have ha : (37894831 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (5042357 / 1250000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (177053 / 10000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (226073 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_450.1 n1_exp_451.2
  have hpoly : (1770477 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (2260711 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (177053 / 10000000 : ℝ))
      (by norm_num : (226073 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (1770477 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (2260711 / 50000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (27 / 32 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (233853 / 5000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (579801 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_452.1 n1_exp_447.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (233853 / 5000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (659687 / 12500000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (6542359 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (13620871 / 2500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_453.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (659687 / 12500000 : ℝ) (6542359 / 100000000 : ℝ) (1770477 / 50000000 : ℝ) (2260711 / 50000000 : ℝ)
    (1372567 / 100000000 : ℝ) (13620871 / 2500000 : ℝ) (53529 / 50000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_090 (x : ℝ) (hx : x ∈ Set.Ioo (7 / 8 : ℝ) (15 / 16 : ℝ)) :
    density x ≤ (20073 / 6250000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (6420127 / 5000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (2909983 / 2000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_449.1 n1_exp_454.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (6420127 / 5000000 : ℝ)) pi_rational_enclosure hi
  have ha : (40338839 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (5713739 / 1250000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (25869 / 2500000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (35411 / 2000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_455.1 n1_exp_456.2
  have hpoly : (51737 / 5000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (442637 / 25000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (25869 / 2500000 : ℝ))
      (by norm_num : (35411 / 2000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (51737 / 2500000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (442637 / 12500000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7 / 8 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (74323 / 2500000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (467707 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_457.1 n1_exp_452.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (74323 / 2500000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (167729 / 5000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (5277513 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (30748591 / 5000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_458.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (167729 / 5000000 : ℝ) (5277513 / 100000000 : ℝ) (51737 / 2500000 : ℝ) (442637 / 12500000 : ℝ)
    (2256073 / 100000000 : ℝ) (30748591 / 5000000 : ℝ) (20073 / 6250000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_091 (x : ℝ) (hx : x ∈ Set.Ioo (15 / 16 : ℝ) (1 / 1 : ℝ)) :
    density x ≤ (210113 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (7274957 / 5000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (16487213 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_454.1 n1_exp_459.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (7274957 / 5000000 : ℝ)) pi_rational_enclosure hi
  have ha : (45709893 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (51796113 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (56301 / 10000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (51739 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_460.1 n1_exp_461.2
  have hpoly : (563007 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (51739 / 5000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (56301 / 10000000 : ℝ))
      (by norm_num : (51739 / 5000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (563007 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (51739 / 2500000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (15 / 16 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (45789 / 2500000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (297293 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_462.1 n1_exp_457.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (45789 / 2500000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (2066693 / 100000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (670919 / 20000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (69413759 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_012.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (2066693 / 100000000 : ℝ) (670919 / 20000000 : ℝ) (563007 / 50000000 : ℝ) (51739 / 2500000 : ℝ)
    (342123 / 20000000 : ℝ) (69413759 / 10000000 : ℝ) (210113 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_092 (x : ℝ) (hx : x ∈ Set.Ioo (1 / 1 : ℝ) (17 / 16 : ℝ)) :
    density x ≤ (126577 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (4121803 / 2500000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (934123 / 500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_459.1 n1_exp_463.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (4121803 / 2500000 : ℝ)) pi_rational_enclosure hi
  have ha : (51796093 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (29346343 / 5000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (28249 / 10000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (56303 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_464.1 n1_exp_465.2
  have hpoly : (282489 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (56303 / 10000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (28249 / 10000000 : ℝ))
      (by norm_num : (56303 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (282489 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (56303 / 5000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1 / 1 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (109367 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (183157 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_466.1 n1_exp_462.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (109367 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (617037 / 50000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (2066707 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (39174721 / 5000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_141.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (617037 / 50000000 : ℝ) (2066707 / 100000000 : ℝ) (282489 / 50000000 : ℝ) (56303 / 5000000 : ℝ)
    (15523 / 1250000 : ℝ) (39174721 / 5000000 : ℝ) (126577 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_093 (x : ℝ) (hx : x ∈ Set.Ioo (17 / 16 : ℝ) (9 / 8 : ℝ)) :
    density x ≤ (3469 / 5000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (18682459 / 10000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (21170001 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_463.1 n1_exp_467.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (18682459 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (58692663 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (66507527 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (1293 / 1000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (113 / 40000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_468.1 n1_exp_469.2
  have hpoly : (129299 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (113 / 40000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (1293 / 1000000 : ℝ))
      (by norm_num : (113 / 40000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (129299 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (113 / 20000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (17 / 16 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (63297 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (13671 / 1250000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_470.1 n1_exp_466.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (63297 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (71423 / 10000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (1234087 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (88435423 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_471.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (71423 / 10000000 : ℝ) (1234087 / 100000000 : ℝ) (129299 / 50000000 : ℝ) (113 / 20000 : ℝ)
    (428267 / 50000000 : ℝ) (88435423 / 10000000 : ℝ) (3469 / 5000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_094 (x : ℝ) (hx : x ∈ Set.Ioo (9 / 8 : ℝ) (5 / 4 : ℝ)) :
    density x ≤ (26539 / 50000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (2117 / 1000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (27182819 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_467.1 n1_exp_156.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (2117 / 1000 : ℝ)) pi_rational_enclosure hi
  have ha : (33253751 / 5000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (42698677 / 5000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (391 / 2000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (12931 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_472.1 n1_exp_473.2
  have hpoly : (19549 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (12931 / 10000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (391 / 2000000 : ℝ))
      (by norm_num : (12931 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (19549 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (12931 / 5000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (9 / 8 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (2413 / 1250000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (31649 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_474.1 n1_exp_470.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (2413 / 1250000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (108911 / 50000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (357121 / 50000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (112669651 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_475.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (108911 / 50000000 : ℝ) (357121 / 50000000 : ℝ) (19549 / 50000000 : ℝ) (12931 / 5000000 : ℝ)
    (657159 / 100000000 : ℝ) (112669651 / 10000000 : ℝ) (26539 / 50000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_095 (x : ℝ) (hx : x ∈ Set.Ioo (5 / 4 : ℝ) (3 / 2 : ℝ)) :
    density x ≤ (11143 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (13591409 / 5000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (44816891 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_156.1 n1_exp_476.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (13591409 / 5000000 : ℝ)) pi_rational_enclosure hi
  have ha : (85397323 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (8799777 / 625000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (7 / 10000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (489 / 2500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_477.1 n1_exp_478.2
  have hpoly : (69 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (489 / 2500000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (7 / 10000000 : ℝ))
      (by norm_num : (489 / 2500000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (69 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (489 / 1250000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5 / 4 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (617 / 5000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (3861 / 2000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_479.1 n1_exp_474.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (617 / 5000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (3481 / 25000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (108917 / 50000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (36576179 / 2000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_480.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (3481 / 25000000 : ℝ) (108917 / 50000000 : ℝ) (69 / 50000000 : ℝ) (489 / 1250000 : ℝ)
    (217633 / 100000000 : ℝ) (36576179 / 2000000 : ℝ) (11143 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_096 (x : ℝ) (hx : x ∈ Set.Ioo (3 / 2 : ℝ) (2 / 1 : ℝ)) :
    density x ≤ (897 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (4481689 / 1000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (6091247 / 500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_476.1 n1_exp_481.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (4481689 / 1000000 : ℝ)) pi_rational_enclosure hi
  have ha : (140796383 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (382724379 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (0 / 1 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (1 / 1250000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_482.1 n1_exp_483.2
  have hpoly : (-1 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (81 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (0 / 1 : ℝ))
      (by norm_num : (1 / 1250000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (-1 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (81 / 50000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3 / 2 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (1 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (247 / 2000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_484.1 n1_exp_479.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (11 / 100000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (871 / 6250000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (481826983 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_009.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (11 / 100000000 : ℝ) (871 / 6250000 : ℝ) (-1 / 50000000 : ℝ) (81 / 50000000 : ℝ)
    (13939 / 100000000 : ℝ) (481826983 / 10000000 : ℝ) (897 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_097 (x : ℝ) (hx : x ∈ Set.Ioo (2 / 1 : ℝ) (3 / 1 : ℝ)) :
    density x ≤ (2907 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (121824939 / 10000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (450085657 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_481.1 n1_exp_485.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (121824939 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (382724253 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (2827971899 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (0 / 1 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (1 / 1048576 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_486.1 n1_exp_487.2
  have hpoly : (-1 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (3 / 3125000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (0 / 1 : ℝ))
      (by norm_num : (1 / 1048576 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (-1 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (3 / 1562500 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (2 / 1 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (0 / 1 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (1 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_488.1 n1_exp_484.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (0 / 1 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (0 / 1 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (23 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (334454217 / 1000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_489.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (0 / 1 : ℝ) (23 / 100000000 : ℝ) (-1 / 50000000 : ℝ) (3 / 1562500 : ℝ)
    (281 / 100000000 : ℝ) (334454217 / 1000000 : ℝ) (2907 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_098 (x : ℝ) (hx : x ∈ Set.Ioo (3 / 1 : ℝ) (4 / 1 : ℝ)) :
    density x ≤ (10089 / 50000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (900171313 / 10000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (6651416331 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_485.1 n1_exp_490.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (900171313 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (565594199 / 2000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (10448021493 / 5000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (0 / 1 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (1 / 1048576 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_491.1 n1_exp_492.2
  have hpoly : (-1 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (3 / 3125000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (0 / 1 : ℝ))
      (by norm_num : (1 / 1048576 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (-1 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (3 / 1562500 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3 / 1 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (0 / 1 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (1 / 1048576 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_006.1 n1_exp_488.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (0 / 1 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (0 / 1 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (27 / 25000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (23215724147 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_493.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (0 / 1 : ℝ) (27 / 25000000 : ℝ) (-1 / 50000000 : ℝ) (3 / 1562500 : ℝ)
    (281 / 100000000 : ℝ) (23215724147 / 10000000 : ℝ) (10089 / 50000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)


#print axioms cell_098

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

/- Exact rational subinterval partition and actual-density assembly. -/
section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open MeasureTheory Set
open scoped BigOperators
namespace MasulloRH.HeightOne

noncomputable def endpoints : Fin 26 → ℝ :=
  ![(1 / 2 : ℝ), (33 / 64 : ℝ), (17 / 32 : ℝ), (35 / 64 : ℝ), (9 / 16 : ℝ), (37 / 64 : ℝ), (19 / 32 : ℝ), (39 / 64 : ℝ), (5 / 8 : ℝ), (21 / 32 : ℝ), (11 / 16 : ℝ), (23 / 32 : ℝ), (3 / 4 : ℝ), (25 / 32 : ℝ), (13 / 16 : ℝ), (27 / 32 : ℝ), (7 / 8 : ℝ), (15 / 16 : ℝ), (1 / 1 : ℝ), (17 / 16 : ℝ), (9 / 8 : ℝ), (5 / 4 : ℝ), (3 / 2 : ℝ), (2 / 1 : ℝ), (3 / 1 : ℝ), (4 / 1 : ℝ)]

noncomputable def cellBounds : Fin 25 → ℝ :=
  ![(124527 / 25000000 : ℝ), (20227 / 4000000 : ℝ), (253781 / 50000000 : ℝ), (503707 / 100000000 : ℝ), (494239 / 100000000 : ℝ), (239713 / 50000000 : ℝ), (229853 / 50000000 : ℝ), (87127 / 20000000 : ℝ), (942741 / 100000000 : ℝ), (793167 / 100000000 : ℝ), (640073 / 100000000 : ℝ), (246923 / 50000000 : ℝ), (22671 / 6250000 : ℝ), (50439 / 20000000 : ℝ), (1029 / 625000 : ℝ), (53529 / 50000000 : ℝ), (20073 / 6250000 : ℝ), (210113 / 100000000 : ℝ), (126577 / 100000000 : ℝ), (3469 / 5000000 : ℝ), (26539 / 50000000 : ℝ), (11143 / 100000000 : ℝ), (897 / 100000000 : ℝ), (2907 / 100000000 : ℝ), (10089 / 50000000 : ℝ)]

theorem endpoint_first : endpoints 0 = (1 / 2 : ℝ) := by norm_num [endpoints]
theorem endpoint_last : endpoints (Fin.last 25) = (4 : ℝ) := by norm_num [endpoints, Fin.last]

theorem endpoints_step (k : Fin 25) : endpoints k.castSucc ≤ endpoints k.succ := by
  fin_cases k
  · change (1 / 2 : ℝ) ≤ (33 / 64 : ℝ)
    norm_num
  · change (33 / 64 : ℝ) ≤ (17 / 32 : ℝ)
    norm_num
  · change (17 / 32 : ℝ) ≤ (35 / 64 : ℝ)
    norm_num
  · change (35 / 64 : ℝ) ≤ (9 / 16 : ℝ)
    norm_num
  · change (9 / 16 : ℝ) ≤ (37 / 64 : ℝ)
    norm_num
  · change (37 / 64 : ℝ) ≤ (19 / 32 : ℝ)
    norm_num
  · change (19 / 32 : ℝ) ≤ (39 / 64 : ℝ)
    norm_num
  · change (39 / 64 : ℝ) ≤ (5 / 8 : ℝ)
    norm_num
  · change (5 / 8 : ℝ) ≤ (21 / 32 : ℝ)
    norm_num
  · change (21 / 32 : ℝ) ≤ (11 / 16 : ℝ)
    norm_num
  · change (11 / 16 : ℝ) ≤ (23 / 32 : ℝ)
    norm_num
  · change (23 / 32 : ℝ) ≤ (3 / 4 : ℝ)
    norm_num
  · change (3 / 4 : ℝ) ≤ (25 / 32 : ℝ)
    norm_num
  · change (25 / 32 : ℝ) ≤ (13 / 16 : ℝ)
    norm_num
  · change (13 / 16 : ℝ) ≤ (27 / 32 : ℝ)
    norm_num
  · change (27 / 32 : ℝ) ≤ (7 / 8 : ℝ)
    norm_num
  · change (7 / 8 : ℝ) ≤ (15 / 16 : ℝ)
    norm_num
  · change (15 / 16 : ℝ) ≤ (1 / 1 : ℝ)
    norm_num
  · change (1 / 1 : ℝ) ≤ (17 / 16 : ℝ)
    norm_num
  · change (17 / 16 : ℝ) ≤ (9 / 8 : ℝ)
    norm_num
  · change (9 / 8 : ℝ) ≤ (5 / 4 : ℝ)
    norm_num
  · change (5 / 4 : ℝ) ≤ (3 / 2 : ℝ)
    norm_num
  · change (3 / 2 : ℝ) ≤ (2 / 1 : ℝ)
    norm_num
  · change (2 / 1 : ℝ) ≤ (3 / 1 : ℝ)
    norm_num
  · change (3 / 1 : ℝ) ≤ (4 / 1 : ℝ)
    norm_num

theorem cell_bounds (k : Fin 25) (x : ℝ)
    (hx : x ∈ Ioo (endpoints k.castSucc) (endpoints k.succ)) :
    density x ≤ cellBounds k := by
  fin_cases k
  · change density x ≤ (124527 / 25000000 : ℝ)
    change x ∈ Ioo (1 / 2 : ℝ) (33 / 64 : ℝ) at hx
    exact cell_074 x hx
  · change density x ≤ (20227 / 4000000 : ℝ)
    change x ∈ Ioo (33 / 64 : ℝ) (17 / 32 : ℝ) at hx
    exact cell_075 x hx
  · change density x ≤ (253781 / 50000000 : ℝ)
    change x ∈ Ioo (17 / 32 : ℝ) (35 / 64 : ℝ) at hx
    exact cell_076 x hx
  · change density x ≤ (503707 / 100000000 : ℝ)
    change x ∈ Ioo (35 / 64 : ℝ) (9 / 16 : ℝ) at hx
    exact cell_077 x hx
  · change density x ≤ (494239 / 100000000 : ℝ)
    change x ∈ Ioo (9 / 16 : ℝ) (37 / 64 : ℝ) at hx
    exact cell_078 x hx
  · change density x ≤ (239713 / 50000000 : ℝ)
    change x ∈ Ioo (37 / 64 : ℝ) (19 / 32 : ℝ) at hx
    exact cell_079 x hx
  · change density x ≤ (229853 / 50000000 : ℝ)
    change x ∈ Ioo (19 / 32 : ℝ) (39 / 64 : ℝ) at hx
    exact cell_080 x hx
  · change density x ≤ (87127 / 20000000 : ℝ)
    change x ∈ Ioo (39 / 64 : ℝ) (5 / 8 : ℝ) at hx
    exact cell_081 x hx
  · change density x ≤ (942741 / 100000000 : ℝ)
    change x ∈ Ioo (5 / 8 : ℝ) (21 / 32 : ℝ) at hx
    exact cell_082 x hx
  · change density x ≤ (793167 / 100000000 : ℝ)
    change x ∈ Ioo (21 / 32 : ℝ) (11 / 16 : ℝ) at hx
    exact cell_083 x hx
  · change density x ≤ (640073 / 100000000 : ℝ)
    change x ∈ Ioo (11 / 16 : ℝ) (23 / 32 : ℝ) at hx
    exact cell_084 x hx
  · change density x ≤ (246923 / 50000000 : ℝ)
    change x ∈ Ioo (23 / 32 : ℝ) (3 / 4 : ℝ) at hx
    exact cell_085 x hx
  · change density x ≤ (22671 / 6250000 : ℝ)
    change x ∈ Ioo (3 / 4 : ℝ) (25 / 32 : ℝ) at hx
    exact cell_086 x hx
  · change density x ≤ (50439 / 20000000 : ℝ)
    change x ∈ Ioo (25 / 32 : ℝ) (13 / 16 : ℝ) at hx
    exact cell_087 x hx
  · change density x ≤ (1029 / 625000 : ℝ)
    change x ∈ Ioo (13 / 16 : ℝ) (27 / 32 : ℝ) at hx
    exact cell_088 x hx
  · change density x ≤ (53529 / 50000000 : ℝ)
    change x ∈ Ioo (27 / 32 : ℝ) (7 / 8 : ℝ) at hx
    exact cell_089 x hx
  · change density x ≤ (20073 / 6250000 : ℝ)
    change x ∈ Ioo (7 / 8 : ℝ) (15 / 16 : ℝ) at hx
    exact cell_090 x hx
  · change density x ≤ (210113 / 100000000 : ℝ)
    change x ∈ Ioo (15 / 16 : ℝ) (1 / 1 : ℝ) at hx
    exact cell_091 x hx
  · change density x ≤ (126577 / 100000000 : ℝ)
    change x ∈ Ioo (1 / 1 : ℝ) (17 / 16 : ℝ) at hx
    exact cell_092 x hx
  · change density x ≤ (3469 / 5000000 : ℝ)
    change x ∈ Ioo (17 / 16 : ℝ) (9 / 8 : ℝ) at hx
    exact cell_093 x hx
  · change density x ≤ (26539 / 50000000 : ℝ)
    change x ∈ Ioo (9 / 8 : ℝ) (5 / 4 : ℝ) at hx
    exact cell_094 x hx
  · change density x ≤ (11143 / 100000000 : ℝ)
    change x ∈ Ioo (5 / 4 : ℝ) (3 / 2 : ℝ) at hx
    exact cell_095 x hx
  · change density x ≤ (897 / 100000000 : ℝ)
    change x ∈ Ioo (3 / 2 : ℝ) (2 / 1 : ℝ) at hx
    exact cell_096 x hx
  · change density x ≤ (2907 / 100000000 : ℝ)
    change x ∈ Ioo (2 / 1 : ℝ) (3 / 1 : ℝ) at hx
    exact cell_097 x hx
  · change density x ≤ (10089 / 50000000 : ℝ)
    change x ∈ Ioo (3 / 1 : ℝ) (4 / 1 : ℝ) at hx
    exact cell_098 x hx

theorem cell_bound_sum :
    (∑ k : Fin 25, cellBounds k * (endpoints k.succ - endpoints k.castSucc)) =
      (8207489 / 3200000000 : ℝ) := by
  norm_num [endpoints, cellBounds, Fin.sum_univ_succ]

theorem density_integrable : Integrable density :=
  MasulloRH.DirectIntegrability.height_one_density_integrable

theorem compact_certificate :
    IntegrableOn density (Icc (1 / 2 : ℝ) (4 : ℝ)) ∧
    (∫ x : ℝ in Icc (1 / 2 : ℝ) (4 : ℝ), density x) ≤ (7 / 2500 : ℝ) := by
  have h := MasulloRH.EnergyCertificate.integral_le_fin_partition_sum
    density 25 endpoints cellBounds density_integrable endpoints_step cell_bounds
  rw [endpoint_first, endpoint_last,
    intervalIntegral.integral_of_le (show (1 / 2 : ℝ) ≤ (4 : ℝ) by norm_num),
    ← integral_Icc_eq_integral_Ioc, cell_bound_sum] at h
  refine ⟨density_integrable.integrableOn, h.trans ?_⟩
  norm_num

end MasulloRH.HeightOne
end

end N1HalfFourProof

open MeasureTheory

theorem solution :
    MeasureTheory.IntegrableOn (fun x : ℝ =>
      Real.exp (2 * (3 / 4 : ℝ) * x + 2 * (7 / 32 : ℝ) * |x|) *
      ‖MasulloRH.GaussianApproximation.residual 1
        (fun _ : Fin 1 => (73 / 50 : ℂ))
        (fun _ : Fin 1 => (3 / 4 : ℝ)) x‖ ^ 2) (Set.Icc (1 / 2 : ℝ) (4 : ℝ)) ∧
    (∫ x : ℝ in Set.Icc (1 / 2 : ℝ) (4 : ℝ),
      Real.exp (2 * (3 / 4 : ℝ) * x + 2 * (7 / 32 : ℝ) * |x|) *
      ‖MasulloRH.GaussianApproximation.residual 1
        (fun _ : Fin 1 => (73 / 50 : ℂ))
        (fun _ : Fin 1 => (3 / 4 : ℝ)) x‖ ^ 2) ≤ (7 / 2500 : ℝ) := by
  have h := N1HalfFourProof.MasulloRH.HeightOne.compact_certificate
  constructor
  · convert! h.1 using 1
    funext x
    simp only [N1HalfFourProof.MasulloRH.HeightOne.density,
      MasulloRH.GaussianApproximation.residual, Fin.sum_univ_one,
      show (2 : ℝ) * (3 / 4) = 3 / 2 by norm_num,
      show (2 : ℝ) * (7 / 32) = 7 / 16 by norm_num]
  · simpa only [N1HalfFourProof.MasulloRH.HeightOne.density,
      MasulloRH.GaussianApproximation.residual, Fin.sum_univ_one,
      show (2 : ℝ) * (3 / 4) = 3 / 2 by norm_num,
      show (2 : ℝ) * (7 / 32) = 7 / 16 by norm_num] using h.2
