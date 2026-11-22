-- Prove2me | solution 1 for MasulloRH.height_one_zero_to_half_energy_certificate
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T17:45:40.69936+00:00
-- url     : https://prove2.me/submissions/22abc38b-b746-4da6-993f-f06f9b1d4906

/- Actual height-one residual energy on [0,1/2].
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

namespace N1ZeroHalfProof

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


theorem n1_exp_239 :
    (230213 / 1000000 : ℝ) ≤ Real.exp (-(47 / 32 : ℝ)) ∧
    Real.exp (-(47 / 32 : ℝ)) ≤ (2302131 / 10000000 : ℝ) := by
  have hsmall : (1308710091 / 1250000000 : ℝ) ≤ Real.exp (47 / 1024 : ℝ) ∧
      Real.exp (47 / 1024 : ℝ) ≤ (10469680729 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (47 / 1024 : ℝ))
    (a := (1308710091 / 1250000000 : ℝ)) (b := (10469680729 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_240 :
    (4851797 / 10000000 : ℝ) ≤ Real.exp (-(7232359 / 10000000 : ℝ)) ∧
    Real.exp (-(7232359 / 10000000 : ℝ)) ≤ (2425899 / 5000000 : ℝ) := by
  have hsmall : (10228584623 / 10000000000 : ℝ) ≤ Real.exp (7232359 / 320000000 : ℝ) ∧
      Real.exp (7232359 / 320000000 : ℝ) ≤ (639286539 / 625000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7232359 / 320000000 : ℝ))
    (a := (10228584623 / 10000000000 : ℝ)) (b := (639286539 / 625000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_241 :
    (496097 / 1000000 : ℝ) ≤ Real.exp (-(7009837 / 10000000 : ℝ)) ∧
    Real.exp (-(7009837 / 10000000 : ℝ)) ≤ (4960971 / 10000000 : ℝ) := by
  have hsmall : (10221474329 / 10000000000 : ℝ) ≤ Real.exp (7009837 / 320000000 : ℝ) ∧
      Real.exp (7009837 / 320000000 : ℝ) ≤ (1022147433 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7009837 / 320000000 : ℝ))
    (a := (10221474329 / 10000000000 : ℝ)) (b := (1022147433 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_242 :
    (10307363 / 10000000 : ℝ) ≤ Real.exp (31 / 1024 : ℝ) ∧
    Real.exp (31 / 1024 : ℝ) ≤ (2576841 / 2500000 : ℝ) := by
  have hsmall : (3127957789261 / 3125000000000 : ℝ) ≤ Real.exp (31 / 32768 : ℝ) ∧
      Real.exp (31 / 32768 : ℝ) ≤ (100094649256353 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (31 / 32768 : ℝ))
    (a := (3127957789261 / 3125000000000 : ℝ)) (b := (100094649256353 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_243 :
    (296901 / 1250000 : ℝ) ≤ Real.exp (-(23 / 16 : ℝ)) ∧
    Real.exp (-(23 / 16 : ℝ)) ≤ (2375209 / 10000000 : ℝ) := by
  have hsmall : (10459461421 / 10000000000 : ℝ) ≤ Real.exp (23 / 512 : ℝ) ∧
      Real.exp (23 / 512 : ℝ) ≤ (5229730711 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (23 / 512 : ℝ))
    (a := (10459461421 / 10000000000 : ℝ)) (b := (5229730711 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_244 :
    (2370839 / 5000000 : ℝ) ≤ Real.exp (-(373097 / 500000 : ℝ)) ∧
    Real.exp (-(373097 / 500000 : ℝ)) ≤ (4741679 / 10000000 : ℝ) := by
  have hsmall : (5117962829 / 5000000000 : ℝ) ≤ Real.exp (373097 / 16000000 : ℝ) ∧
      Real.exp (373097 / 16000000 : ℝ) ≤ (10235925659 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (373097 / 16000000 : ℝ))
    (a := (5117962829 / 5000000000 : ℝ)) (b := (10235925659 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_245 :
    (24259 / 50000 : ℝ) ≤ Real.exp (-(7232353 / 10000000 : ℝ)) ∧
    Real.exp (-(7232353 / 10000000 : ℝ)) ≤ (4851801 / 10000000 : ℝ) := by
  have hsmall : (10228584431 / 10000000000 : ℝ) ≤ Real.exp (7232353 / 320000000 : ℝ) ∧
      Real.exp (7232353 / 320000000 : ℝ) ≤ (639286527 / 625000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7232353 / 320000000 : ℝ))
    (a := (10228584431 / 10000000000 : ℝ)) (b := (639286527 / 625000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_246 :
    (10624173 / 10000000 : ℝ) ≤ Real.exp (31 / 512 : ℝ) ∧
    Real.exp (31 / 512 : ℝ) ≤ (5312087 / 5000000 : ℝ) := by
  have hsmall : (50094694048761 / 50000000000000 : ℝ) ≤ Real.exp (31 / 16384 : ℝ) ∧
      Real.exp (31 / 16384 : ℝ) ≤ (100189388097523 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (31 / 16384 : ℝ))
    (a := (50094694048761 / 50000000000000 : ℝ)) (b := (100189388097523 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_247 :
    (490121 / 2000000 : ℝ) ≤ Real.exp (-(45 / 32 : ℝ)) ∧
    Real.exp (-(45 / 32 : ℝ)) ≤ (1225303 / 5000000 : ℝ) := by
  have hsmall : (10449252089 / 10000000000 : ℝ) ≤ Real.exp (45 / 1024 : ℝ) ∧
      Real.exp (45 / 1024 : ℝ) ≤ (1044925209 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (45 / 1024 : ℝ))
    (a := (10449252089 / 10000000000 : ℝ)) (b := (1044925209 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_248 :
    (4630683 / 10000000 : ℝ) ≤ Real.exp (-(7698807 / 10000000 : ℝ)) ∧
    Real.exp (-(7698807 / 10000000 : ℝ)) ≤ (1157671 / 2500000 : ℝ) := by
  have hsmall : (10243505191 / 10000000000 : ℝ) ≤ Real.exp (7698807 / 320000000 : ℝ) ∧
      Real.exp (7698807 / 320000000 : ℝ) ≤ (1280438149 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7698807 / 320000000 : ℝ))
    (a := (10243505191 / 10000000000 : ℝ)) (b := (1280438149 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_249 :
    (59271 / 125000 : ℝ) ≤ Real.exp (-(3730967 / 5000000 : ℝ)) ∧
    Real.exp (-(3730967 / 5000000 : ℝ)) ≤ (4741681 / 10000000 : ℝ) := by
  have hsmall : (5117962733 / 5000000000 : ℝ) ≤ Real.exp (3730967 / 160000000 : ℝ) ∧
      Real.exp (3730967 / 160000000 : ℝ) ≤ (10235925467 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3730967 / 160000000 : ℝ))
    (a := (5117962733 / 5000000000 : ℝ)) (b := (10235925467 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_250 :
    (5475361 / 5000000 : ℝ) ≤ Real.exp (93 / 1024 : ℝ) ∧
    Real.exp (93 / 1024 : ℝ) ≤ (10950723 / 10000000 : ℝ) := by
  have hsmall : (1002842166083 / 1000000000000 : ℝ) ≤ Real.exp (93 / 32768 : ℝ) ∧
      Real.exp (93 / 32768 : ℝ) ≤ (100284216608301 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (93 / 32768 : ℝ))
    (a := (1002842166083 / 1000000000000 : ℝ)) (b := (100284216608301 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_251 :
    (505679 / 2000000 : ℝ) ≤ Real.exp (-(11 / 8 : ℝ)) ∧
    Real.exp (-(11 / 8 : ℝ)) ≤ (632099 / 2500000 : ℝ) := by
  have hsmall : (10439052723 / 10000000000 : ℝ) ≤ Real.exp (11 / 256 : ℝ) ∧
      Real.exp (11 / 256 : ℝ) ≤ (2609763181 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (11 / 256 : ℝ))
    (a := (10439052723 / 10000000000 : ℝ)) (b := (2609763181 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_252 :
    (4518887 / 10000000 : ℝ) ≤ Real.exp (-(992899 / 1250000 : ℝ)) ∧
    Real.exp (-(992899 / 1250000 : ℝ)) ≤ (564861 / 1250000 : ℝ) := by
  have hsmall : (1281416397 / 1250000000 : ℝ) ≤ Real.exp (992899 / 40000000 : ℝ) ∧
      Real.exp (992899 / 40000000 : ℝ) ≤ (10251331177 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (992899 / 40000000 : ℝ))
    (a := (1281416397 / 1250000000 : ℝ)) (b := (10251331177 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_253 :
    (926137 / 2000000 : ℝ) ≤ Real.exp (-(7698801 / 10000000 : ℝ)) ∧
    Real.exp (-(7698801 / 10000000 : ℝ)) ≤ (2315343 / 5000000 : ℝ) := by
  have hsmall : (10243504999 / 10000000000 : ℝ) ≤ Real.exp (7698801 / 320000000 : ℝ) ∧
      Real.exp (7698801 / 320000000 : ℝ) ≤ (2048701 / 2000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7698801 / 320000000 : ℝ))
    (a := (10243504999 / 10000000000 : ℝ)) (b := (2048701 / 2000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_254 :
    (11287307 / 10000000 : ℝ) ≤ Real.exp (31 / 256 : ℝ) ∧
    Real.exp (31 / 256 : ℝ) ≤ (2821827 / 2500000 : ℝ) := by
  have hsmall : (50189567436779 / 50000000000000 : ℝ) ≤ Real.exp (31 / 8192 : ℝ) ∧
      Real.exp (31 / 8192 : ℝ) ≤ (100379134873559 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (31 / 8192 : ℝ))
    (a := (50189567436779 / 50000000000000 : ℝ)) (b := (100379134873559 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_255 :
    (521731 / 2000000 : ℝ) ≤ Real.exp (-(43 / 32 : ℝ)) ∧
    Real.exp (-(43 / 32 : ℝ)) ≤ (163041 / 625000 : ℝ) := by
  have hsmall : (10428863311 / 10000000000 : ℝ) ≤ Real.exp (43 / 1024 : ℝ) ∧
      Real.exp (43 / 1024 : ℝ) ≤ (651803957 / 625000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (43 / 1024 : ℝ))
    (a := (10428863311 / 10000000000 : ℝ)) (b := (651803957 / 625000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_256 :
    (4406371 / 10000000 : ℝ) ≤ Real.exp (-(1024417 / 1250000 : ℝ)) ∧
    Real.exp (-(1024417 / 1250000 : ℝ)) ≤ (1101593 / 2500000 : ℝ) := by
  have hsmall : (2051882379 / 2000000000 : ℝ) ≤ Real.exp (1024417 / 40000000 : ℝ) ∧
      Real.exp (1024417 / 40000000 : ℝ) ≤ (1282426487 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1024417 / 40000000 : ℝ))
    (a := (2051882379 / 2000000000 : ℝ)) (b := (1282426487 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_257 :
    (451889 / 1000000 : ℝ) ≤ Real.exp (-(1588637 / 2000000 : ℝ)) ∧
    Real.exp (-(1588637 / 2000000 : ℝ)) ≤ (4518891 / 10000000 : ℝ) := by
  have hsmall : (10251330951 / 10000000000 : ℝ) ≤ Real.exp (1588637 / 64000000 : ℝ) ∧
      Real.exp (1588637 / 64000000 : ℝ) ≤ (1281416369 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1588637 / 64000000 : ℝ))
    (a := (10251330951 / 10000000000 : ℝ)) (b := (1281416369 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_258 :
    (11634237 / 10000000 : ℝ) ≤ Real.exp (155 / 1024 : ℝ) ∧
    Real.exp (155 / 1024 : ℝ) ≤ (5817119 / 5000000 : ℝ) := by
  have hsmall : (100474142978249 / 100000000000000 : ℝ) ≤ Real.exp (155 / 32768 : ℝ) ∧
      Real.exp (155 / 32768 : ℝ) ≤ (401896571913 / 400000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (155 / 32768 : ℝ))
    (a := (100474142978249 / 100000000000000 : ℝ)) (b := (401896571913 / 400000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_259 :
    (2691463 / 10000000 : ℝ) ≤ Real.exp (-(21 / 16 : ℝ)) ∧
    Real.exp (-(21 / 16 : ℝ)) ≤ (336433 / 1250000 : ℝ) := by
  have hsmall : (5209341923 / 5000000000 : ℝ) ≤ Real.exp (21 / 512 : ℝ) ∧
      Real.exp (21 / 512 : ℝ) ≤ (10418683847 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (21 / 512 : ℝ))
    (a := (5209341923 / 5000000000 : ℝ)) (b := (10418683847 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_260 :
    (2146609 / 5000000 : ℝ) ≤ Real.exp (-(1691097 / 2000000 : ℝ)) ∧
    Real.exp (-(1691097 / 2000000 : ℝ)) ≤ (4293219 / 10000000 : ℝ) := by
  have hsmall : (2566938959 / 2500000000 : ℝ) ≤ Real.exp (1691097 / 64000000 : ℝ) ∧
      Real.exp (1691097 / 64000000 : ℝ) ≤ (10267755837 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1691097 / 64000000 : ℝ))
    (a := (2566938959 / 2500000000 : ℝ)) (b := (10267755837 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_261 :
    (2203187 / 5000000 : ℝ) ≤ Real.exp (-(8195329 / 10000000 : ℝ)) ∧
    Real.exp (-(8195329 / 10000000 : ℝ)) ≤ (35251 / 80000 : ℝ) := by
  have hsmall : (10259411671 / 10000000000 : ℝ) ≤ Real.exp (8195329 / 320000000 : ℝ) ∧
      Real.exp (8195329 / 320000000 : ℝ) ≤ (1282426459 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (8195329 / 320000000 : ℝ))
    (a := (10259411671 / 10000000000 : ℝ)) (b := (1282426459 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_262 :
    (11991831 / 10000000 : ℝ) ≤ Real.exp (93 / 512 : ℝ) ∧
    Real.exp (93 / 512 : ℝ) ≤ (1498979 / 1250000 : ℝ) := by
  have hsmall : (20113848201481 / 20000000000000 : ℝ) ≤ Real.exp (93 / 16384 : ℝ) ∧
      Real.exp (93 / 16384 : ℝ) ≤ (50284620503703 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (93 / 16384 : ℝ))
    (a := (20113848201481 / 20000000000000 : ℝ)) (b := (50284620503703 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_263 :
    (2776899 / 10000000 : ℝ) ≤ Real.exp (-(41 / 32 : ℝ)) ∧
    Real.exp (-(41 / 32 : ℝ)) ≤ (27769 / 100000 : ℝ) := by
  have hsmall : (2602128579 / 2500000000 : ℝ) ≤ Real.exp (41 / 1024 : ℝ) ∧
      Real.exp (41 / 1024 : ℝ) ≤ (10408514317 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (41 / 1024 : ℝ))
    (a := (2602128579 / 2500000000 : ℝ)) (b := (10408514317 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_264 :
    (2089759 / 5000000 : ℝ) ≤ Real.exp (-(872389 / 1000000 : ℝ)) ∧
    Real.exp (-(872389 / 1000000 : ℝ)) ≤ (4179519 / 10000000 : ℝ) := by
  have hsmall : (10276371689 / 10000000000 : ℝ) ≤ Real.exp (872389 / 32000000 : ℝ) ∧
      Real.exp (872389 / 32000000 : ℝ) ≤ (1027637169 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (872389 / 32000000 : ℝ))
    (a := (10276371689 / 10000000000 : ℝ)) (b := (1027637169 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_265 :
    (4293221 / 10000000 : ℝ) ≤ Real.exp (-(4227739 / 5000000 : ℝ)) ∧
    Real.exp (-(4227739 / 5000000 : ℝ)) ≤ (2146611 / 5000000 : ℝ) := by
  have hsmall : (10267755611 / 10000000000 : ℝ) ≤ Real.exp (4227739 / 160000000 : ℝ) ∧
      Real.exp (4227739 / 160000000 : ℝ) ≤ (2566938903 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (4227739 / 160000000 : ℝ))
    (a := (10267755611 / 10000000000 : ℝ)) (b := (2566938903 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_266 :
    (386263 / 312500 : ℝ) ≤ Real.exp (217 / 1024 : ℝ) ∧
    Real.exp (217 / 1024 : ℝ) ≤ (12360417 / 10000000 : ℝ) := by
  have hsmall : (100664429046137 / 100000000000000 : ℝ) ≤ Real.exp (217 / 32768 : ℝ) ∧
      Real.exp (217 / 32768 : ℝ) ≤ (50332214523069 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (217 / 32768 : ℝ))
    (a := (100664429046137 / 100000000000000 : ℝ)) (b := (50332214523069 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_267 :
    (2865047 / 10000000 : ℝ) ≤ Real.exp (-(5 / 4 : ℝ)) ∧
    Real.exp (-(5 / 4 : ℝ)) ≤ (358131 / 1250000 : ℝ) := by
  have hsmall : (10398354713 / 10000000000 : ℝ) ≤ Real.exp (5 / 128 : ℝ) ∧
      Real.exp (5 / 128 : ℝ) ≤ (5199177357 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5 / 128 : ℝ))
    (a := (10398354713 / 10000000000 : ℝ)) (b := (5199177357 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_268 :
    (813073 / 2000000 : ℝ) ≤ Real.exp (-(1800163 / 2000000 : ℝ)) ∧
    Real.exp (-(1800163 / 2000000 : ℝ)) ≤ (2032683 / 5000000 : ℝ) := by
  have hsmall : (5142634307 / 5000000000 : ℝ) ≤ Real.exp (1800163 / 64000000 : ℝ) ∧
      Real.exp (1800163 / 64000000 : ℝ) ≤ (2057053723 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1800163 / 64000000 : ℝ))
    (a := (5142634307 / 5000000000 : ℝ)) (b := (2057053723 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_269 :
    (4179521 / 10000000 : ℝ) ≤ Real.exp (-(8723883 / 10000000 : ℝ)) ∧
    Real.exp (-(8723883 / 10000000 : ℝ)) ≤ (2089761 / 5000000 : ℝ) := by
  have hsmall : (1284546433 / 1250000000 : ℝ) ≤ Real.exp (8723883 / 320000000 : ℝ) ∧
      Real.exp (8723883 / 320000000 : ℝ) ≤ (2055274293 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (8723883 / 320000000 : ℝ))
    (a := (1284546433 / 1250000000 : ℝ)) (b := (2055274293 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_270 :
    (1274033 / 1000000 : ℝ) ≤ Real.exp (31 / 128 : ℝ) ∧
    Real.exp (31 / 128 : ℝ) ≤ (12740331 / 10000000 : ℝ) := by
  have hsmall : (100759707179641 / 100000000000000 : ℝ) ≤ Real.exp (31 / 4096 : ℝ) ∧
      Real.exp (31 / 4096 : ℝ) ≤ (50379853589821 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (31 / 4096 : ℝ))
    (a := (100759707179641 / 100000000000000 : ℝ)) (b := (50379853589821 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_271 :
    (1477997 / 5000000 : ℝ) ≤ Real.exp (-(39 / 32 : ℝ)) ∧
    Real.exp (-(39 / 32 : ℝ)) ≤ (591199 / 2000000 : ℝ) := by
  have hsmall : (5194102513 / 5000000000 : ℝ) ≤ Real.exp (39 / 1024 : ℝ) ∧
      Real.exp (39 / 1024 : ℝ) ≤ (10388205027 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (39 / 1024 : ℝ))
    (a := (5194102513 / 5000000000 : ℝ)) (b := (10388205027 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_272 :
    (3950853 / 10000000 : ℝ) ≤ Real.exp (-(4643267 / 5000000 : ℝ)) ∧
    Real.exp (-(4643267 / 5000000 : ℝ)) ≤ (1975427 / 5000000 : ℝ) := by
  have hsmall : (5147228071 / 5000000000 : ℝ) ≤ Real.exp (4643267 / 160000000 : ℝ) ∧
      Real.exp (4643267 / 160000000 : ℝ) ≤ (10294456143 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (4643267 / 160000000 : ℝ))
    (a := (5147228071 / 5000000000 : ℝ)) (b := (10294456143 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_273 :
    (508171 / 1250000 : ℝ) ≤ Real.exp (-(1125101 / 1250000 : ℝ)) ∧
    Real.exp (-(1125101 / 1250000 : ℝ)) ≤ (4065369 / 10000000 : ℝ) := by
  have hsmall : (10285268389 / 10000000000 : ℝ) ≤ Real.exp (1125101 / 40000000 : ℝ) ∧
      Real.exp (1125101 / 40000000 : ℝ) ≤ (1028526839 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1125101 / 40000000 : ℝ))
    (a := (10285268389 / 10000000000 : ℝ)) (b := (1028526839 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_274 :
    (13131921 / 10000000 : ℝ) ≤ Real.exp (279 / 1024 : ℝ) ∧
    Real.exp (279 / 1024 : ℝ) ≤ (6565961 / 5000000 : ℝ) := by
  have hsmall : (100855075493189 / 100000000000000 : ℝ) ≤ Real.exp (279 / 32768 : ℝ) ∧
      Real.exp (279 / 32768 : ℝ) ≤ (10085507549319 / 10000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (279 / 32768 : ℝ))
    (a := (100855075493189 / 100000000000000 : ℝ)) (b := (10085507549319 / 10000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_275 :
    (3049827 / 10000000 : ℝ) ≤ Real.exp (-(19 / 16 : ℝ)) ∧
    Real.exp (-(19 / 16 : ℝ)) ≤ (762457 / 2500000 : ℝ) := by
  have hsmall : (10378065247 / 10000000000 : ℝ) ≤ Real.exp (19 / 512 : ℝ) ∧
      Real.exp (19 / 512 : ℝ) ≤ (324314539 / 312500000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (19 / 512 : ℝ))
    (a := (10378065247 / 10000000000 : ℝ)) (b := (324314539 / 312500000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_276 :
    (479511 / 1250000 : ℝ) ≤ Real.exp (-(9581319 / 10000000 : ℝ)) ∧
    Real.exp (-(9581319 / 10000000 : ℝ)) ≤ (3836089 / 10000000 : ℝ) := by
  have hsmall : (10303943797 / 10000000000 : ℝ) ≤ Real.exp (9581319 / 320000000 : ℝ) ∧
      Real.exp (9581319 / 320000000 : ℝ) ≤ (5151971899 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (9581319 / 320000000 : ℝ))
    (a := (10303943797 / 10000000000 : ℝ)) (b := (5151971899 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_277 :
    (493857 / 1250000 : ℝ) ≤ Real.exp (-(9286527 / 10000000 : ℝ)) ∧
    Real.exp (-(9286527 / 10000000 : ℝ)) ≤ (3950857 / 10000000 : ℝ) := by
  have hsmall : (10294455917 / 10000000000 : ℝ) ≤ Real.exp (9286527 / 320000000 : ℝ) ∧
      Real.exp (9286527 / 320000000 : ℝ) ≤ (5147227959 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (9286527 / 320000000 : ℝ))
    (a := (10294455917 / 10000000000 : ℝ)) (b := (5147227959 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_278 :
    (3383887 / 2500000 : ℝ) ≤ Real.exp (155 / 512 : ℝ) ∧
    Real.exp (155 / 512 : ℝ) ≤ (13535549 / 10000000 : ℝ) := by
  have hsmall : (100950534072137 / 100000000000000 : ℝ) ≤ Real.exp (155 / 16384 : ℝ) ∧
      Real.exp (155 / 16384 : ℝ) ≤ (50475267036069 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (155 / 16384 : ℝ))
    (a := (100950534072137 / 100000000000000 : ℝ)) (b := (50475267036069 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_279 :
    (3146639 / 10000000 : ℝ) ≤ Real.exp (-(37 / 32 : ℝ)) ∧
    Real.exp (-(37 / 32 : ℝ)) ≤ (39333 / 125000 : ℝ) := by
  have hsmall : (2591983841 / 2500000000 : ℝ) ≤ Real.exp (37 / 1024 : ℝ) ∧
      Real.exp (37 / 1024 : ℝ) ≤ (2073587073 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (37 / 1024 : ℝ))
    (a := (2591983841 / 2500000000 : ℝ)) (b := (2073587073 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_280 :
    (930293 / 2500000 : ℝ) ≤ Real.exp (-(9885463 / 10000000 : ℝ)) ∧
    Real.exp (-(9885463 / 10000000 : ℝ)) ≤ (3721173 / 10000000 : ℝ) := by
  have hsmall : (2062748367 / 2000000000 : ℝ) ≤ Real.exp (9885463 / 320000000 : ℝ) ∧
      Real.exp (9885463 / 320000000 : ℝ) ≤ (2578435459 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (9885463 / 320000000 : ℝ))
    (a := (2062748367 / 2000000000 : ℝ)) (b := (2578435459 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_281 :
    (3836091 / 10000000 : ℝ) ≤ Real.exp (-(74854 / 78125 : ℝ)) ∧
    Real.exp (-(74854 / 78125 : ℝ)) ≤ (959023 / 2500000 : ℝ) := by
  have hsmall : (10303943571 / 10000000000 : ℝ) ≤ Real.exp (37427 / 1250000 : ℝ) ∧
      Real.exp (37427 / 1250000 : ℝ) ≤ (2575985893 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (37427 / 1250000 : ℝ))
    (a := (10303943571 / 10000000000 : ℝ)) (b := (2575985893 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_282 :
    (13951581 / 10000000 : ℝ) ≤ Real.exp (341 / 1024 : ℝ) ∧
    Real.exp (341 / 1024 : ℝ) ≤ (6975791 / 5000000 : ℝ) := by
  have hsmall : (315769009381 / 312500000000 : ℝ) ≤ Real.exp (341 / 32768 : ℝ) ∧
      Real.exp (341 / 32768 : ℝ) ≤ (101046083001921 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (341 / 32768 : ℝ))
    (a := (315769009381 / 312500000000 : ℝ)) (b := (101046083001921 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_283 :
    (811631 / 2500000 : ℝ) ≤ Real.exp (-(9 / 8 : ℝ)) ∧
    Real.exp (-(9 / 8 : ℝ)) ≤ (129861 / 400000 : ℝ) := by
  have hsmall : (1035781537 / 1000000000 : ℝ) ≤ Real.exp (9 / 256 : ℝ) ∧
      Real.exp (9 / 256 : ℝ) ≤ (10357815371 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (9 / 256 : ℝ))
    (a := (1035781537 / 1000000000 : ℝ)) (b := (10357815371 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_284 :
    (721243 / 2000000 : ℝ) ≤ Real.exp (-(10199261 / 10000000 : ℝ)) ∧
    Real.exp (-(10199261 / 10000000 : ℝ)) ≤ (450777 / 1250000 : ℝ) := by
  have hsmall : (2064772129 / 2000000000 : ℝ) ≤ Real.exp (10199261 / 320000000 : ℝ) ∧
      Real.exp (10199261 / 320000000 : ℝ) ≤ (5161930323 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (10199261 / 320000000 : ℝ))
    (a := (2064772129 / 2000000000 : ℝ)) (b := (5161930323 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_285 :
    (148847 / 400000 : ℝ) ≤ Real.exp (-(1977091 / 2000000 : ℝ)) ∧
    Real.exp (-(1977091 / 2000000 : ℝ)) ≤ (465147 / 1250000 : ℝ) := by
  have hsmall : (5156870789 / 5000000000 : ℝ) ≤ Real.exp (1977091 / 64000000 : ℝ) ∧
      Real.exp (1977091 / 64000000 : ℝ) ≤ (10313741579 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1977091 / 64000000 : ℝ))
    (a := (5156870789 / 5000000000 : ℝ)) (b := (10313741579 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_286 :
    (7190201 / 5000000 : ℝ) ≤ Real.exp (93 / 256 : ℝ) ∧
    Real.exp (93 / 256 : ℝ) ≤ (14380403 / 10000000 : ℝ) := by
  have hsmall : (20228344473611 / 20000000000000 : ℝ) ≤ Real.exp (93 / 8192 : ℝ) ∧
      Real.exp (93 / 8192 : ℝ) ≤ (12642715296007 / 12500000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (93 / 8192 : ℝ))
    (a := (20228344473611 / 20000000000000 : ℝ)) (b := (12642715296007 / 12500000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_287 :
    (167479 / 500000 : ℝ) ≤ Real.exp (-(35 / 32 : ℝ)) ∧
    Real.exp (-(35 / 32 : ℝ)) ≤ (3349581 / 10000000 : ℝ) := by
  have hsmall : (10347705253 / 10000000000 : ℝ) ≤ Real.exp (35 / 1024 : ℝ) ∧
      Real.exp (35 / 1024 : ℝ) ≤ (5173852627 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (35 / 1024 : ℝ))
    (a := (10347705253 / 10000000000 : ℝ)) (b := (5173852627 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_288 :
    (349133 / 1000000 : ℝ) ≤ Real.exp (-(10523021 / 10000000 : ℝ)) ∧
    Real.exp (-(10523021 / 10000000 : ℝ)) ≤ (3491331 / 10000000 : ℝ) := by
  have hsmall : (1291788887 / 1250000000 : ℝ) ≤ Real.exp (10523021 / 320000000 : ℝ) ∧
      Real.exp (10523021 / 320000000 : ℝ) ≤ (10334311097 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (10523021 / 320000000 : ℝ))
    (a := (1291788887 / 1250000000 : ℝ)) (b := (10334311097 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_289 :
    (1803109 / 5000000 : ℝ) ≤ Real.exp (-(10199253 / 10000000 : ℝ)) ∧
    Real.exp (-(10199253 / 10000000 : ℝ)) ≤ (3606219 / 10000000 : ℝ) := by
  have hsmall : (10323860387 / 10000000000 : ℝ) ≤ Real.exp (10199253 / 320000000 : ℝ) ∧
      Real.exp (10199253 / 320000000 : ℝ) ≤ (2580965097 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (10199253 / 320000000 : ℝ))
    (a := (10323860387 / 10000000000 : ℝ)) (b := (2580965097 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_290 :
    (14822403 / 10000000 : ℝ) ≤ Real.exp (403 / 1024 : ℝ) ∧
    Real.exp (403 / 1024 : ℝ) ≤ (3705601 / 2500000 : ℝ) := by
  have hsmall : (50618726128069 / 50000000000000 : ℝ) ≤ Real.exp (403 / 32768 : ℝ) ∧
      Real.exp (403 / 32768 : ℝ) ≤ (101237452256139 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (403 / 32768 : ℝ))
    (a := (50618726128069 / 50000000000000 : ℝ)) (b := (101237452256139 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_291 :
    (3455907 / 10000000 : ℝ) ≤ Real.exp (-(17 / 16 : ℝ)) ∧
    Real.exp (-(17 / 16 : ℝ)) ≤ (863977 / 2500000 : ℝ) := by
  have hsmall : (2067521001 / 2000000000 : ℝ) ≤ Real.exp (17 / 512 : ℝ) ∧
      Real.exp (17 / 512 : ℝ) ≤ (5168802503 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (17 / 512 : ℝ))
    (a := (2067521001 / 2000000000 : ℝ)) (b := (5168802503 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_292 :
    (1688317 / 5000000 : ℝ) ≤ Real.exp (-(10857057 / 10000000 : ℝ)) ∧
    Real.exp (-(10857057 / 10000000 : ℝ)) ≤ (675327 / 2000000 : ℝ) := by
  have hsmall : (10345104329 / 10000000000 : ℝ) ≤ Real.exp (10857057 / 320000000 : ℝ) ∧
      Real.exp (10857057 / 320000000 : ℝ) ≤ (1034510433 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (10857057 / 320000000 : ℝ))
    (a := (10345104329 / 10000000000 : ℝ)) (b := (1034510433 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_293 :
    (3491333 / 10000000 : ℝ) ≤ Real.exp (-(10523013 / 10000000 : ℝ)) ∧
    Real.exp (-(10523013 / 10000000 : ℝ)) ≤ (1745667 / 5000000 : ℝ) := by
  have hsmall : (5167155419 / 5000000000 : ℝ) ≤ Real.exp (10523013 / 320000000 : ℝ) ∧
      Real.exp (10523013 / 320000000 : ℝ) ≤ (10334310839 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (10523013 / 320000000 : ℝ))
    (a := (5167155419 / 5000000000 : ℝ)) (b := (10334310839 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_294 :
    (15277989 / 10000000 : ℝ) ≤ Real.exp (217 / 512 : ℝ) ∧
    Real.exp (217 / 512 : ℝ) ≤ (1527799 / 1000000 : ℝ) := by
  have hsmall : (101333272751849 / 100000000000000 : ℝ) ≤ Real.exp (217 / 16384 : ℝ) ∧
      Real.exp (217 / 16384 : ℝ) ≤ (2026665455037 / 2000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (217 / 16384 : ℝ))
    (a := (101333272751849 / 100000000000000 : ℝ)) (b := (2026665455037 / 2000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_295 :
    (3565609 / 10000000 : ℝ) ≤ Real.exp (-(33 / 32 : ℝ)) ∧
    Real.exp (-(33 / 32 : ℝ)) ≤ (356561 / 1000000 : ℝ) := by
  have hsmall : (2065502923 / 2000000000 : ℝ) ≤ Real.exp (33 / 1024 : ℝ) ∧
      Real.exp (33 / 1024 : ℝ) ≤ (1290939327 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (33 / 1024 : ℝ))
    (a := (2065502923 / 2000000000 : ℝ)) (b := (1290939327 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_296 :
    (815561 / 2500000 : ℝ) ≤ Real.exp (-(350053 / 312500 : ℝ)) ∧
    Real.exp (-(350053 / 312500 : ℝ)) ≤ (652449 / 2000000 : ℝ) := by
  have hsmall : (414250079 / 400000000 : ℝ) ≤ Real.exp (350053 / 10000000 : ℝ) ∧
      Real.exp (350053 / 10000000 : ℝ) ≤ (1294531497 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (350053 / 10000000 : ℝ))
    (a := (414250079 / 400000000 : ℝ)) (b := (1294531497 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_297 :
    (844159 / 2500000 : ℝ) ≤ Real.exp (-(10857049 / 10000000 : ℝ)) ∧
    Real.exp (-(10857049 / 10000000 : ℝ)) ≤ (3376637 / 10000000 : ℝ) := by
  have hsmall : (1034510407 / 1000000000 : ℝ) ≤ Real.exp (10857049 / 320000000 : ℝ) ∧
      Real.exp (10857049 / 320000000 : ℝ) ≤ (10345104071 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (10857049 / 320000000 : ℝ))
    (a := (1034510407 / 1000000000 : ℝ)) (b := (10345104071 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_298 :
    (15747579 / 10000000 : ℝ) ≤ Real.exp (465 / 1024 : ℝ) ∧
    Real.exp (465 / 1024 : ℝ) ≤ (787379 / 500000 : ℝ) := by
  have hsmall : (50714591970473 / 50000000000000 : ℝ) ≤ Real.exp (465 / 32768 : ℝ) ∧
      Real.exp (465 / 32768 : ℝ) ≤ (101429183940947 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (465 / 32768 : ℝ))
    (a := (50714591970473 / 50000000000000 : ℝ)) (b := (101429183940947 / 100000000000000 : ℝ))
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


theorem n1_exp_300 :
    (3148283 / 10000000 : ℝ) ≤ Real.exp (-(11557277 / 10000000 : ℝ)) ∧
    Real.exp (-(11557277 / 10000000 : ℝ)) ≤ (787071 / 2500000 : ℝ) := by
  have hsmall : (5183883071 / 5000000000 : ℝ) ≤ Real.exp (11557277 / 320000000 : ℝ) ∧
      Real.exp (11557277 / 320000000 : ℝ) ≤ (10367766143 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (11557277 / 320000000 : ℝ))
    (a := (5183883071 / 5000000000 : ℝ)) (b := (10367766143 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_301 :
    (3262247 / 10000000 : ℝ) ≤ Real.exp (-(1400211 / 1250000 : ℝ)) ∧
    Real.exp (-(1400211 / 1250000 : ℝ)) ≤ (407781 / 1250000 : ℝ) := by
  have hsmall : (10356251717 / 10000000000 : ℝ) ≤ Real.exp (1400211 / 40000000 : ℝ) ∧
      Real.exp (1400211 / 40000000 : ℝ) ≤ (5178125859 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1400211 / 40000000 : ℝ))
    (a := (10356251717 / 10000000000 : ℝ)) (b := (5178125859 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_302 :
    (8115801 / 5000000 : ℝ) ≤ Real.exp (31 / 64 : ℝ) ∧
    Real.exp (31 / 64 : ℝ) ≤ (16231603 / 10000000 : ℝ) := by
  have hsmall : (10152518590927 / 10000000000000 : ℝ) ≤ Real.exp (31 / 2048 : ℝ) ∧
      Real.exp (31 / 2048 : ℝ) ≤ (101525185909271 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (31 / 2048 : ℝ))
    (a := (10152518590927 / 10000000000000 : ℝ)) (b := (101525185909271 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_303 :
    (3795571 / 10000000 : ℝ) ≤ Real.exp (-(31 / 32 : ℝ)) ∧
    Real.exp (-(31 / 32 : ℝ)) ≤ (948893 / 2500000 : ℝ) := by
  have hsmall : (10307363373 / 10000000000 : ℝ) ≤ Real.exp (31 / 1024 : ℝ) ∧
      Real.exp (31 / 1024 : ℝ) ≤ (5153681687 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (31 / 1024 : ℝ))
    (a := (10307363373 / 10000000000 : ℝ)) (b := (5153681687 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_304 :
    (758719 / 2500000 : ℝ) ≤ Real.exp (-(11924143 / 10000000 : ℝ)) ∧
    Real.exp (-(11924143 / 10000000 : ℝ)) ≤ (3034877 / 10000000 : ℝ) := by
  have hsmall : (2594914787 / 2500000000 : ℝ) ≤ Real.exp (11924143 / 320000000 : ℝ) ∧
      Real.exp (11924143 / 320000000 : ℝ) ≤ (10379659149 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (11924143 / 320000000 : ℝ))
    (a := (2594914787 / 2500000000 : ℝ)) (b := (10379659149 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_305 :
    (1574143 / 5000000 : ℝ) ≤ Real.exp (-(11557269 / 10000000 : ℝ)) ∧
    Real.exp (-(11557269 / 10000000 : ℝ)) ≤ (3148287 / 10000000 : ℝ) := by
  have hsmall : (5183882941 / 5000000000 : ℝ) ≤ Real.exp (11557269 / 320000000 : ℝ) ∧
      Real.exp (11557269 / 320000000 : ℝ) ≤ (10367765883 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (11557269 / 320000000 : ℝ))
    (a := (5183882941 / 5000000000 : ℝ)) (b := (10367765883 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_306 :
    (1885257 / 2500000 : ℝ) ≤ Real.exp (-(289 / 1024 : ℝ)) ∧
    Real.exp (-(289 / 1024 : ℝ)) ≤ (7541029 / 10000000 : ℝ) := by
  have hsmall : (10088585871 / 10000000000 : ℝ) ≤ Real.exp (289 / 32768 : ℝ) ∧
      Real.exp (289 / 32768 : ℝ) ≤ (630536617 / 625000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (289 / 32768 : ℝ))
    (a := (10088585871 / 10000000000 : ℝ)) (b := (630536617 / 625000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_307 :
    (8365251 / 5000000 : ℝ) ≤ Real.exp (527 / 1024 : ℝ) ∧
    Real.exp (527 / 1024 : ℝ) ≤ (16730503 / 10000000 : ℝ) := by
  have hsmall : (12702659842843 / 12500000000000 : ℝ) ≤ Real.exp (527 / 32768 : ℝ) ∧
      Real.exp (527 / 32768 : ℝ) ≤ (20324255748549 / 20000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (527 / 32768 : ℝ))
    (a := (12702659842843 / 12500000000000 : ℝ)) (b := (20324255748549 / 20000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_308 :
    (489507 / 1250000 : ℝ) ≤ Real.exp (-(15 / 16 : ℝ)) ∧
    Real.exp (-(15 / 16 : ℝ)) ≤ (3916057 / 10000000 : ℝ) := by
  have hsmall : (5148651251 / 5000000000 : ℝ) ≤ Real.exp (15 / 512 : ℝ) ∧
      Real.exp (15 / 512 : ℝ) ≤ (10297302503 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (15 / 512 : ℝ))
    (a := (5148651251 / 5000000000 : ℝ)) (b := (10297302503 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_309 :
    (730537 / 2500000 : ℝ) ≤ Real.exp (-(6151329 / 5000000 : ℝ)) ∧
    Real.exp (-(6151329 / 5000000 : ℝ)) ≤ (2922149 / 10000000 : ℝ) := by
  have hsmall : (10391944089 / 10000000000 : ℝ) ≤ Real.exp (6151329 / 160000000 : ℝ) ∧
      Real.exp (6151329 / 160000000 : ℝ) ≤ (1039194409 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (6151329 / 160000000 : ℝ))
    (a := (10391944089 / 10000000000 : ℝ)) (b := (1039194409 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_310 :
    (3034879 / 10000000 : ℝ) ≤ Real.exp (-(2384827 / 2000000 : ℝ)) ∧
    Real.exp (-(2384827 / 2000000 : ℝ)) ≤ (4742 / 15625 : ℝ) := by
  have hsmall : (10379658889 / 10000000000 : ℝ) ≤ Real.exp (2384827 / 64000000 : ℝ) ∧
      Real.exp (2384827 / 64000000 : ℝ) ≤ (1037965889 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (2384827 / 64000000 : ℝ))
    (a := (10379658889 / 10000000000 : ℝ)) (b := (1037965889 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_311 :
    (7287633 / 10000000 : ℝ) ≤ Real.exp (-(81 / 256 : ℝ)) ∧
    Real.exp (-(81 / 256 : ℝ)) ≤ (3643817 / 5000000 : ℝ) := by
  have hsmall : (50496837 / 50000000 : ℝ) ≤ Real.exp (81 / 8192 : ℝ) ∧
      Real.exp (81 / 8192 : ℝ) ≤ (10099367401 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (81 / 8192 : ℝ))
    (a := (50496837 / 50000000 : ℝ)) (b := (10099367401 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_312 :
    (269449 / 156250 : ℝ) ≤ Real.exp (279 / 512 : ℝ) ∧
    Real.exp (279 / 512 : ℝ) ≤ (17244737 / 10000000 : ℝ) := by
  have hsmall : (10171746252737 / 10000000000000 : ℝ) ≤ Real.exp (279 / 16384 : ℝ) ∧
      Real.exp (279 / 16384 : ℝ) ≤ (101717462527371 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (279 / 16384 : ℝ))
    (a := (10171746252737 / 10000000000000 : ℝ)) (b := (101717462527371 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_313 :
    (808073 / 2000000 : ℝ) ≤ Real.exp (-(29 / 32 : ℝ)) ∧
    Real.exp (-(29 / 32 : ℝ)) ≤ (2020183 / 5000000 : ℝ) := by
  have hsmall : (10287251451 / 10000000000 : ℝ) ≤ Real.exp (29 / 1024 : ℝ) ∧
      Real.exp (29 / 1024 : ℝ) ≤ (2571812863 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (29 / 1024 : ℝ))
    (a := (10287251451 / 10000000000 : ℝ)) (b := (2571812863 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_314 :
    (281023 / 1000000 : ℝ) ≤ Real.exp (-(6346593 / 5000000 : ℝ)) ∧
    Real.exp (-(6346593 / 5000000 : ℝ)) ≤ (2810231 / 10000000 : ℝ) := by
  have hsmall : (130057927 / 125000000 : ℝ) ≤ Real.exp (6346593 / 160000000 : ℝ) ∧
      Real.exp (6346593 / 160000000 : ℝ) ≤ (10404634161 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (6346593 / 160000000 : ℝ))
    (a := (130057927 / 125000000 : ℝ)) (b := (10404634161 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_315 :
    (2922151 / 10000000 : ℝ) ≤ Real.exp (-(246053 / 200000 : ℝ)) ∧
    Real.exp (-(246053 / 200000 : ℝ)) ≤ (365269 / 1250000 : ℝ) := by
  have hsmall : (1039194383 / 1000000000 : ℝ) ≤ Real.exp (246053 / 6400000 : ℝ) ∧
      Real.exp (246053 / 6400000 : ℝ) ≤ (10391943831 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (246053 / 6400000 : ℝ))
    (a := (1039194383 / 1000000000 : ℝ)) (b := (10391943831 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_316 :
    (7029011 / 10000000 : ℝ) ≤ Real.exp (-(361 / 1024 : ℝ)) ∧
    Real.exp (-(361 / 1024 : ℝ)) ≤ (1757253 / 2500000 : ℝ) := by
  have hsmall : (5055388773 / 5000000000 : ℝ) ≤ Real.exp (361 / 32768 : ℝ) ∧
      Real.exp (361 / 32768 : ℝ) ≤ (10110777547 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (361 / 32768 : ℝ))
    (a := (5055388773 / 5000000000 : ℝ)) (b := (10110777547 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_317 :
    (2221847 / 1250000 : ℝ) ≤ Real.exp (589 / 1024 : ℝ) ∧
    Real.exp (589 / 1024 : ℝ) ≤ (17774777 / 10000000 : ℝ) := by
  have hsmall : (6363358584327 / 6250000000000 : ℝ) ≤ Real.exp (589 / 32768 : ℝ) ∧
      Real.exp (589 / 32768 : ℝ) ≤ (101813737349233 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (589 / 32768 : ℝ))
    (a := (6363358584327 / 6250000000000 : ℝ)) (b := (101813737349233 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_318 :
    (208431 / 500000 : ℝ) ≤ Real.exp (-(7 / 8 : ℝ)) ∧
    Real.exp (-(7 / 8 : ℝ)) ≤ (4168621 / 10000000 : ℝ) := by
  have hsmall : (10277210211 / 10000000000 : ℝ) ≤ Real.exp (7 / 256 : ℝ) ∧
      Real.exp (7 / 256 : ℝ) ≤ (2569302553 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7 / 256 : ℝ))
    (a := (10277210211 / 10000000000 : ℝ)) (b := (2569302553 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_319 :
    (10797 / 40000 : ℝ) ≤ Real.exp (-(13096111 / 10000000 : ℝ)) ∧
    Real.exp (-(13096111 / 10000000 : ℝ)) ≤ (2699251 / 10000000 : ℝ) := by
  have hsmall : (10417743309 / 10000000000 : ℝ) ≤ Real.exp (13096111 / 320000000 : ℝ) ∧
      Real.exp (13096111 / 320000000 : ℝ) ≤ (1041774331 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (13096111 / 320000000 : ℝ))
    (a := (10417743309 / 10000000000 : ℝ)) (b := (1041774331 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_320 :
    (351279 / 1250000 : ℝ) ≤ Real.exp (-(6346589 / 5000000 : ℝ)) ∧
    Real.exp (-(6346589 / 5000000 : ℝ)) ≤ (2810233 / 10000000 : ℝ) := by
  have hsmall : (104046339 / 100000000 : ℝ) ≤ Real.exp (6346589 / 160000000 : ℝ) ∧
      Real.exp (6346589 / 160000000 : ℝ) ≤ (10404633901 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (6346589 / 160000000 : ℝ))
    (a := (104046339 / 100000000 : ℝ)) (b := (10404633901 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_321 :
    (3383169 / 5000000 : ℝ) ≤ Real.exp (-(25 / 64 : ℝ)) ∧
    Real.exp (-(25 / 64 : ℝ)) ≤ (6766339 / 10000000 : ℝ) := by
  have hsmall : (10122818411 / 10000000000 : ℝ) ≤ Real.exp (25 / 2048 : ℝ) ∧
      Real.exp (25 / 2048 : ℝ) ≤ (2530704603 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (25 / 2048 : ℝ))
    (a := (10122818411 / 10000000000 : ℝ)) (b := (2530704603 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_322 :
    (4580277 / 2500000 : ℝ) ≤ Real.exp (155 / 256 : ℝ) ∧
    Real.exp (155 / 256 : ℝ) ≤ (18321109 / 10000000 : ℝ) := by
  have hsmall : (50955051647249 / 50000000000000 : ℝ) ≤ Real.exp (155 / 8192 : ℝ) ∧
      Real.exp (155 / 8192 : ℝ) ≤ (101910103294499 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (155 / 8192 : ℝ))
    (a := (50955051647249 / 50000000000000 : ℝ)) (b := (101910103294499 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_323 :
    (2150473 / 5000000 : ℝ) ≤ Real.exp (-(27 / 32 : ℝ)) ∧
    Real.exp (-(27 / 32 : ℝ)) ≤ (4300947 / 10000000 : ℝ) := by
  have hsmall : (2566794693 / 2500000000 : ℝ) ≤ Real.exp (27 / 1024 : ℝ) ∧
      Real.exp (27 / 1024 : ℝ) ≤ (10267178773 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (27 / 1024 : ℝ))
    (a := (2566794693 / 2500000000 : ℝ)) (b := (10267178773 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_324 :
    (1294669 / 5000000 : ℝ) ≤ Real.exp (-(540473 / 400000 : ℝ)) ∧
    Real.exp (-(540473 / 400000 : ℝ)) ≤ (2589339 / 10000000 : ℝ) := by
  have hsmall : (10431285859 / 10000000000 : ℝ) ≤ Real.exp (540473 / 12800000 : ℝ) ∧
      Real.exp (540473 / 12800000 : ℝ) ≤ (521564293 / 500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (540473 / 12800000 : ℝ))
    (a := (10431285859 / 10000000000 : ℝ)) (b := (521564293 / 500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_325 :
    (674813 / 2500000 : ℝ) ≤ Real.exp (-(13096103 / 10000000 : ℝ)) ∧
    Real.exp (-(13096103 / 10000000 : ℝ)) ≤ (2699253 / 10000000 : ℝ) := by
  have hsmall : (1302217881 / 1250000000 : ℝ) ≤ Real.exp (13096103 / 320000000 : ℝ) ∧
      Real.exp (13096103 / 320000000 : ℝ) ≤ (10417743049 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (13096103 / 320000000 : ℝ))
    (a := (1302217881 / 1250000000 : ℝ)) (b := (10417743049 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_326 :
    (1625193 / 2500000 : ℝ) ≤ Real.exp (-(441 / 1024 : ℝ)) ∧
    Real.exp (-(441 / 1024 : ℝ)) ≤ (6500773 / 10000000 : ℝ) := by
  have hsmall : (5067746109 / 5000000000 : ℝ) ≤ Real.exp (441 / 32768 : ℝ) ∧
      Real.exp (441 / 32768 : ℝ) ≤ (10135492219 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (441 / 32768 : ℝ))
    (a := (5067746109 / 5000000000 : ℝ)) (b := (10135492219 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_327 :
    (18884231 / 10000000 : ℝ) ≤ Real.exp (651 / 1024 : ℝ) ∧
    Real.exp (651 / 1024 : ℝ) ≤ (2360529 / 1250000 : ℝ) := by
  have hsmall : (51003280224707 / 50000000000000 : ℝ) ≤ Real.exp (651 / 32768 : ℝ) ∧
      Real.exp (651 / 32768 : ℝ) ≤ (20401312089883 / 20000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (651 / 32768 : ℝ))
    (a := (51003280224707 / 50000000000000 : ℝ)) (b := (20401312089883 / 20000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_328 :
    (4437473 / 10000000 : ℝ) ≤ Real.exp (-(13 / 16 : ℝ)) ∧
    Real.exp (-(13 / 16 : ℝ)) ≤ (2218737 / 5000000 : ℝ) := by
  have hsmall : (2564289281 / 2500000000 : ℝ) ≤ Real.exp (13 / 512 : ℝ) ∧
      Real.exp (13 / 512 : ℝ) ≤ (82057257 / 80000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (13 / 512 : ℝ))
    (a := (2564289281 / 2500000000 : ℝ)) (b := (82057257 / 80000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_329 :
    (1240313 / 5000000 : ℝ) ≤ Real.exp (-(6970369 / 5000000 : ℝ)) ∧
    Real.exp (-(6970369 / 5000000 : ℝ)) ≤ (2480627 / 10000000 : ℝ) := by
  have hsmall : (261131921 / 250000000 : ℝ) ≤ Real.exp (6970369 / 160000000 : ℝ) ∧
      Real.exp (6970369 / 160000000 : ℝ) ≤ (10445276841 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (6970369 / 160000000 : ℝ))
    (a := (261131921 / 250000000 : ℝ)) (b := (10445276841 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_330 :
    (129467 / 500000 : ℝ) ≤ Real.exp (-(13511817 / 10000000 : ℝ)) ∧
    Real.exp (-(13511817 / 10000000 : ℝ)) ≤ (2589341 / 10000000 : ℝ) := by
  have hsmall : (5215642799 / 5000000000 : ℝ) ≤ Real.exp (13511817 / 320000000 : ℝ) ∧
      Real.exp (13511817 / 320000000 : ℝ) ≤ (10431285599 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (13511817 / 320000000 : ℝ))
    (a := (5215642799 / 5000000000 : ℝ)) (b := (10431285599 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_331 :
    (6233443 / 10000000 : ℝ) ≤ Real.exp (-(121 / 256 : ℝ)) ∧
    Real.exp (-(121 / 256 : ℝ)) ≤ (1558361 / 2500000 : ℝ) := by
  have hsmall : (2537200327 / 2500000000 : ℝ) ≤ Real.exp (121 / 8192 : ℝ) ∧
      Real.exp (121 / 8192 : ℝ) ≤ (10148801309 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (121 / 8192 : ℝ))
    (a := (2537200327 / 2500000000 : ℝ)) (b := (10148801309 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_332 :
    (19464663 / 10000000 : ℝ) ≤ Real.exp (341 / 512 : ℝ) ∧
    Real.exp (341 / 512 : ℝ) ≤ (2433083 / 1250000 : ℝ) := by
  have hsmall : (10210310890031 / 10000000000000 : ℝ) ≤ Real.exp (341 / 16384 : ℝ) ∧
      Real.exp (341 / 16384 : ℝ) ≤ (102103108900311 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (341 / 16384 : ℝ))
    (a := (10210310890031 / 10000000000000 : ℝ)) (b := (102103108900311 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_333 :
    (4578333 / 10000000 : ℝ) ≤ Real.exp (-(25 / 32 : ℝ)) ∧
    Real.exp (-(25 / 32 : ℝ)) ≤ (2289167 / 5000000 : ℝ) := by
  have hsmall : (10247145259 / 10000000000 : ℝ) ≤ Real.exp (25 / 1024 : ℝ) ∧
      Real.exp (25 / 1024 : ℝ) ≤ (512357263 / 500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (25 / 1024 : ℝ))
    (a := (10247145259 / 10000000000 : ℝ)) (b := (512357263 / 500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_334 :
    (1186623 / 5000000 : ℝ) ≤ Real.exp (-(14383263 / 10000000 : ℝ)) ∧
    Real.exp (-(14383263 / 10000000 : ℝ)) ≤ (2373247 / 10000000 : ℝ) := by
  have hsmall : (2614932877 / 2500000000 : ℝ) ≤ Real.exp (14383263 / 320000000 : ℝ) ∧
      Real.exp (14383263 / 320000000 : ℝ) ≤ (10459731509 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (14383263 / 320000000 : ℝ))
    (a := (2614932877 / 2500000000 : ℝ)) (b := (10459731509 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_335 :
    (2480629 / 10000000 : ℝ) ≤ Real.exp (-(13940729 / 10000000 : ℝ)) ∧
    Real.exp (-(13940729 / 10000000 : ℝ)) ≤ (248063 / 1000000 : ℝ) := by
  have hsmall : (5222638273 / 5000000000 : ℝ) ≤ Real.exp (13940729 / 320000000 : ℝ) ∧
      Real.exp (13940729 / 320000000 : ℝ) ≤ (10445276547 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (13940729 / 320000000 : ℝ))
    (a := (5222638273 / 5000000000 : ℝ)) (b := (10445276547 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_336 :
    (1491361 / 2500000 : ℝ) ≤ Real.exp (-(529 / 1024 : ℝ)) ∧
    Real.exp (-(529 / 1024 : ℝ)) ≤ (1193089 / 2000000 : ℝ) := by
  have hsmall : (508137407 / 500000000 : ℝ) ≤ Real.exp (529 / 32768 : ℝ) ∧
      Real.exp (529 / 32768 : ℝ) ≤ (10162748141 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (529 / 32768 : ℝ))
    (a := (508137407 / 500000000 : ℝ)) (b := (10162748141 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_337 :
    (2507867 / 1250000 : ℝ) ≤ Real.exp (713 / 1024 : ℝ) ∧
    Real.exp (713 / 1024 : ℝ) ≤ (20062937 / 10000000 : ℝ) := by
  have hsmall : (102199748733597 / 100000000000000 : ℝ) ≤ Real.exp (713 / 32768 : ℝ) ∧
      Real.exp (713 / 32768 : ℝ) ≤ (51099874366799 / 50000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (713 / 32768 : ℝ))
    (a := (102199748733597 / 100000000000000 : ℝ)) (b := (51099874366799 / 50000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_338 :
    (944733 / 2000000 : ℝ) ≤ Real.exp (-(3 / 4 : ℝ)) ∧
    Real.exp (-(3 / 4 : ℝ)) ≤ (2361833 / 5000000 : ℝ) := by
  have hsmall : (5118571583 / 5000000000 : ℝ) ≤ Real.exp (3 / 128 : ℝ) ∧
      Real.exp (3 / 128 : ℝ) ≤ (10237143167 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3 / 128 : ℝ))
    (a := (5118571583 / 5000000000 : ℝ)) (b := (10237143167 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_339 :
    (1133663 / 5000000 : ℝ) ≤ Real.exp (-(14839837 / 10000000 : ℝ)) ∧
    Real.exp (-(14839837 / 10000000 : ℝ)) ≤ (2267327 / 10000000 : ℝ) := by
  have hsmall : (10474666039 / 10000000000 : ℝ) ≤ Real.exp (14839837 / 320000000 : ℝ) ∧
      Real.exp (14839837 / 320000000 : ℝ) ≤ (261866651 / 250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (14839837 / 320000000 : ℝ))
    (a := (10474666039 / 10000000000 : ℝ)) (b := (261866651 / 250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_340 :
    (18541 / 78125 : ℝ) ≤ Real.exp (-(7191627 / 5000000 : ℝ)) ∧
    Real.exp (-(7191627 / 5000000 : ℝ)) ≤ (2373249 / 10000000 : ℝ) := by
  have hsmall : (10459731213 / 10000000000 : ℝ) ≤ Real.exp (7191627 / 160000000 : ℝ) ∧
      Real.exp (7191627 / 160000000 : ℝ) ≤ (5229865607 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7191627 / 160000000 : ℝ))
    (a := (10459731213 / 10000000000 : ℝ)) (b := (5229865607 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_341 :
    (1424457 / 2500000 : ℝ) ≤ Real.exp (-(9 / 16 : ℝ)) ∧
    Real.exp (-(9 / 16 : ℝ)) ≤ (5697829 / 10000000 : ℝ) := by
  have hsmall : (5088667647 / 5000000000 : ℝ) ≤ Real.exp (9 / 512 : ℝ) ∧
      Real.exp (9 / 512 : ℝ) ≤ (2035467059 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (9 / 512 : ℝ))
    (a := (5088667647 / 5000000000 : ℝ)) (b := (2035467059 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_342 :
    (20679597 / 10000000 : ℝ) ≤ Real.exp (93 / 128 : ℝ) ∧
    Real.exp (93 / 128 : ℝ) ≤ (10339799 / 5000000 : ℝ) := by
  have hsmall : (12787060004471 / 12500000000000 : ℝ) ≤ Real.exp (93 / 4096 : ℝ) ∧
      Real.exp (93 / 4096 : ℝ) ≤ (102296480035769 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (93 / 4096 : ℝ))
    (a := (12787060004471 / 12500000000000 : ℝ)) (b := (102296480035769 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_343 :
    (487361 / 1000000 : ℝ) ≤ Real.exp (-(23 / 32 : ℝ)) ∧
    Real.exp (-(23 / 32 : ℝ)) ≤ (4873611 / 10000000 : ℝ) := by
  have hsmall : (2045430167 / 2000000000 : ℝ) ≤ Real.exp (23 / 1024 : ℝ) ∧
      Real.exp (23 / 1024 : ℝ) ≤ (2556787709 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (23 / 1024 : ℝ))
    (a := (2045430167 / 2000000000 : ℝ)) (b := (2556787709 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_344 :
    (2162997 / 10000000 : ℝ) ≤ Real.exp (-(15310903 / 10000000 : ℝ)) ∧
    Real.exp (-(15310903 / 10000000 : ℝ)) ≤ (1081499 / 5000000 : ℝ) := by
  have hsmall : (10490096953 / 10000000000 : ℝ) ≤ Real.exp (15310903 / 320000000 : ℝ) ∧
      Real.exp (15310903 / 320000000 : ℝ) ≤ (5245048477 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (15310903 / 320000000 : ℝ))
    (a := (10490096953 / 10000000000 : ℝ)) (b := (5245048477 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_345 :
    (35427 / 156250 : ℝ) ≤ Real.exp (-(3709957 / 2500000 : ℝ)) ∧
    Real.exp (-(3709957 / 2500000 : ℝ)) ≤ (2267329 / 10000000 : ℝ) := by
  have hsmall : (654666609 / 625000000 : ℝ) ≤ Real.exp (3709957 / 80000000 : ℝ) ∧
      Real.exp (3709957 / 80000000 : ℝ) ≤ (2094933149 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (3709957 / 80000000 : ℝ))
    (a := (654666609 / 625000000 : ℝ)) (b := (2094933149 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_346 :
    (2715799 / 5000000 : ℝ) ≤ Real.exp (-(625 / 1024 : ℝ)) ∧
    Real.exp (-(625 / 1024 : ℝ)) ≤ (5431599 / 10000000 : ℝ) := by
  have hsmall : (318517671 / 312500000 : ℝ) ≤ Real.exp (625 / 32768 : ℝ) ∧
      Real.exp (625 / 32768 : ℝ) ≤ (10192565473 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (625 / 32768 : ℝ))
    (a := (318517671 / 312500000 : ℝ)) (b := (10192565473 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_347 :
    (5328803 / 2500000 : ℝ) ≤ Real.exp (775 / 1024 : ℝ) ∧
    Real.exp (775 / 1024 : ℝ) ≤ (21315213 / 10000000 : ℝ) := by
  have hsmall : (25598325723349 / 25000000000000 : ℝ) ≤ Real.exp (775 / 32768 : ℝ) ∧
      Real.exp (775 / 32768 : ℝ) ≤ (102393302893397 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (775 / 32768 : ℝ))
    (a := (25598325723349 / 25000000000000 : ℝ)) (b := (102393302893397 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_348 :
    (1005663 / 2000000 : ℝ) ≤ Real.exp (-(11 / 16 : ℝ)) ∧
    Real.exp (-(11 / 16 : ℝ)) ≤ (1257079 / 2500000 : ℝ) := by
  have hsmall : (5108584129 / 5000000000 : ℝ) ≤ Real.exp (11 / 512 : ℝ) ∧
      Real.exp (11 / 512 : ℝ) ≤ (10217168259 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (11 / 512 : ℝ))
    (a := (5108584129 / 5000000000 : ℝ)) (b := (10217168259 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_349 :
    (64387 / 312500 : ℝ) ≤ Real.exp (-(15796923 / 10000000 : ℝ)) ∧
    Real.exp (-(15796923 / 10000000 : ℝ)) ≤ (412077 / 2000000 : ℝ) := by
  have hsmall : (10506041549 / 10000000000 : ℝ) ≤ Real.exp (15796923 / 320000000 : ℝ) ∧
      Real.exp (15796923 / 320000000 : ℝ) ≤ (210120831 / 200000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (15796923 / 320000000 : ℝ))
    (a := (10506041549 / 10000000000 : ℝ)) (b := (210120831 / 200000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_350 :
    (2162999 / 10000000 : ℝ) ≤ Real.exp (-(7655447 / 5000000 : ℝ)) ∧
    Real.exp (-(7655447 / 5000000 : ℝ)) ≤ (2163 / 10000 : ℝ) := by
  have hsmall : (5245048329 / 5000000000 : ℝ) ≤ Real.exp (7655447 / 160000000 : ℝ) ∧
      Real.exp (7655447 / 160000000 : ℝ) ≤ (10490096659 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7655447 / 160000000 : ℝ))
    (a := (5245048329 / 5000000000 : ℝ)) (b := (10490096659 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_351 :
    (1033541 / 2000000 : ℝ) ≤ Real.exp (-(169 / 256 : ℝ)) ∧
    Real.exp (-(169 / 256 : ℝ)) ≤ (2583853 / 5000000 : ℝ) := by
  have hsmall : (10208441497 / 10000000000 : ℝ) ≤ Real.exp (169 / 8192 : ℝ) ∧
      Real.exp (169 / 8192 : ℝ) ≤ (5104220749 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (169 / 8192 : ℝ))
    (a := (10208441497 / 10000000000 : ℝ)) (b := (5104220749 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_352 :
    (5492591 / 2500000 : ℝ) ≤ Real.exp (403 / 512 : ℝ) ∧
    Real.exp (403 / 512 : ℝ) ≤ (4394073 / 2000000 : ℝ) := by
  have hsmall : (102490217393139 / 100000000000000 : ℝ) ≤ Real.exp (403 / 16384 : ℝ) ∧
      Real.exp (403 / 16384 : ℝ) ≤ (5124510869657 / 5000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (403 / 16384 : ℝ))
    (a := (102490217393139 / 100000000000000 : ℝ)) (b := (5124510869657 / 5000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_353 :
    (5187931 / 10000000 : ℝ) ≤ Real.exp (-(21 / 32 : ℝ)) ∧
    Real.exp (-(21 / 32 : ℝ)) ≤ (1296983 / 2500000 : ℝ) := by
  have hsmall : (408287817 / 400000000 : ℝ) ≤ Real.exp (21 / 1024 : ℝ) ∧
      Real.exp (21 / 1024 : ℝ) ≤ (5103597713 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (21 / 1024 : ℝ))
    (a := (408287817 / 400000000 : ℝ)) (b := (5103597713 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_354 :
    (979807 / 5000000 : ℝ) ≤ Real.exp (-(16298371 / 10000000 : ℝ)) ∧
    Real.exp (-(16298371 / 10000000 : ℝ)) ≤ (391923 / 2000000 : ℝ) := by
  have hsmall : (2104503537 / 2000000000 : ℝ) ≤ Real.exp (16298371 / 320000000 : ℝ) ∧
      Real.exp (16298371 / 320000000 : ℝ) ≤ (5261258843 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (16298371 / 320000000 : ℝ))
    (a := (2104503537 / 2000000000 : ℝ)) (b := (5261258843 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_355 :
    (1030193 / 5000000 : ℝ) ≤ Real.exp (-(7898457 / 5000000 : ℝ)) ∧
    Real.exp (-(7898457 / 5000000 : ℝ)) ≤ (2060387 / 10000000 : ℝ) := by
  have hsmall : (5253020627 / 5000000000 : ℝ) ≤ Real.exp (7898457 / 160000000 : ℝ) ∧
      Real.exp (7898457 / 160000000 : ℝ) ≤ (2101208251 / 2000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (7898457 / 160000000 : ℝ))
    (a := (5253020627 / 5000000000 : ℝ)) (b := (2101208251 / 2000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_356 :
    (30669 / 62500 : ℝ) ≤ Real.exp (-(729 / 1024 : ℝ)) ∧
    Real.exp (-(729 / 1024 : ℝ)) ≤ (4907041 / 10000000 : ℝ) := by
  have hsmall : (10224966313 / 10000000000 : ℝ) ≤ Real.exp (729 / 32768 : ℝ) ∧
      Real.exp (729 / 32768 : ℝ) ≤ (5112483157 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (729 / 32768 : ℝ))
    (a := (10224966313 / 10000000000 : ℝ)) (b := (5112483157 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_357 :
    (5661413 / 2500000 : ℝ) ≤ Real.exp (837 / 1024 : ℝ) ∧
    Real.exp (837 / 1024 : ℝ) ≤ (22645653 / 10000000 : ℝ) := by
  have hsmall : (12823402952717 / 12500000000000 : ℝ) ≤ Real.exp (837 / 32768 : ℝ) ∧
      Real.exp (837 / 32768 : ℝ) ≤ (102587223621737 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (837 / 32768 : ℝ))
    (a := (12823402952717 / 12500000000000 : ℝ)) (b := (102587223621737 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_358 :
    (2676307 / 5000000 : ℝ) ≤ Real.exp (-(5 / 8 : ℝ)) ∧
    Real.exp (-(5 / 8 : ℝ)) ≤ (1070523 / 2000000 : ℝ) := by
  have hsmall : (10197232327 / 10000000000 : ℝ) ≤ Real.exp (5 / 256 : ℝ) ∧
      Real.exp (5 / 256 : ℝ) ≤ (1274654041 / 1250000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (5 / 256 : ℝ))
    (a := (10197232327 / 10000000000 : ℝ)) (b := (1274654041 / 1250000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_359 :
    (232601 / 1250000 : ℝ) ≤ Real.exp (-(8407869 / 5000000 : ℝ)) ∧
    Real.exp (-(8407869 / 5000000 : ℝ)) ≤ (1860809 / 10000000 : ℝ) := by
  have hsmall : (2107908791 / 2000000000 : ℝ) ≤ Real.exp (8407869 / 160000000 : ℝ) ∧
      Real.exp (8407869 / 160000000 : ℝ) ≤ (2634885989 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (8407869 / 160000000 : ℝ))
    (a := (2107908791 / 2000000000 : ℝ)) (b := (2634885989 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_360 :
    (30619 / 156250 : ℝ) ≤ Real.exp (-(8149181 / 5000000 : ℝ)) ∧
    Real.exp (-(8149181 / 5000000 : ℝ)) ≤ (1959617 / 10000000 : ℝ) := by
  have hsmall : (10522517389 / 10000000000 : ℝ) ≤ Real.exp (8149181 / 160000000 : ℝ) ∧
      Real.exp (8149181 / 160000000 : ℝ) ≤ (1052251739 / 1000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (8149181 / 160000000 : ℝ))
    (a := (10522517389 / 10000000000 : ℝ)) (b := (1052251739 / 1000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_361 :
    (4650431 / 10000000 : ℝ) ≤ Real.exp (-(49 / 64 : ℝ)) ∧
    Real.exp (-(49 / 64 : ℝ)) ≤ (72663 / 156250 : ℝ) := by
  have hsmall : (10242142991 / 10000000000 : ℝ) ≤ Real.exp (49 / 2048 : ℝ) ∧
      Real.exp (49 / 2048 : ℝ) ≤ (640133937 / 625000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (49 / 2048 : ℝ))
    (a := (10242142991 / 10000000000 : ℝ)) (b := (640133937 / 625000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_362 :
    (23341697 / 10000000 : ℝ) ≤ Real.exp (217 / 256 : ℝ) ∧
    Real.exp (217 / 256 : ℝ) ≤ (11670849 / 5000000 : ℝ) := by
  have hsmall : (51342160833003 / 50000000000000 : ℝ) ≤ Real.exp (217 / 8192 : ℝ) ∧
      Real.exp (217 / 8192 : ℝ) ≤ (102684321666007 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (217 / 8192 : ℝ))
    (a := (51342160833003 / 50000000000000 : ℝ)) (b := (102684321666007 / 100000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_363 :
    (1380631 / 2500000 : ℝ) ≤ Real.exp (-(19 / 32 : ℝ)) ∧
    Real.exp (-(19 / 32 : ℝ)) ≤ (220901 / 400000 : ℝ) := by
  have hsmall : (10187278953 / 10000000000 : ℝ) ≤ Real.exp (19 / 1024 : ℝ) ∧
      Real.exp (19 / 1024 : ℝ) ≤ (5093639477 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (19 / 1024 : ℝ))
    (a := (10187278953 / 10000000000 : ℝ)) (b := (5093639477 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_364 :
    (352817 / 2000000 : ℝ) ≤ Real.exp (-(8674763 / 5000000 : ℝ)) ∧
    Real.exp (-(8674763 / 5000000 : ℝ)) ≤ (882043 / 5000000 : ℝ) := by
  have hsmall : (2639284877 / 2500000000 : ℝ) ≤ Real.exp (8674763 / 160000000 : ℝ) ∧
      Real.exp (8674763 / 160000000 : ℝ) ≤ (10557139509 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (8674763 / 160000000 : ℝ))
    (a := (2639284877 / 2500000000 : ℝ)) (b := (10557139509 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_365 :
    (186081 / 1000000 : ℝ) ≤ Real.exp (-(16815729 / 10000000 : ℝ)) ∧
    Real.exp (-(16815729 / 10000000 : ℝ)) ≤ (1860811 / 10000000 : ℝ) := by
  have hsmall : (10539543659 / 10000000000 : ℝ) ≤ Real.exp (16815729 / 320000000 : ℝ) ∧
      Real.exp (16815729 / 320000000 : ℝ) ≤ (526977183 / 500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (16815729 / 320000000 : ℝ))
    (a := (10539543659 / 10000000000 : ℝ)) (b := (526977183 / 500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_366 :
    (2199321 / 5000000 : ℝ) ≤ Real.exp (-(841 / 1024 : ℝ)) ∧
    Real.exp (-(841 / 1024 : ℝ)) ≤ (4398643 / 10000000 : ℝ) := by
  have hsmall : (2564993681 / 2500000000 : ℝ) ≤ Real.exp (841 / 32768 : ℝ) ∧
      Real.exp (841 / 32768 : ℝ) ≤ (410398989 / 400000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (841 / 32768 : ℝ))
    (a := (2564993681 / 2500000000 : ℝ)) (b := (410398989 / 400000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_367 :
    (4811827 / 2000000 : ℝ) ≤ Real.exp (899 / 1024 : ℝ) ∧
    Real.exp (899 / 1024 : ℝ) ≤ (187962 / 78125 : ℝ) := by
  have hsmall : (51390755806427 / 50000000000000 : ℝ) ≤ Real.exp (899 / 32768 : ℝ) ∧
      Real.exp (899 / 32768 : ℝ) ≤ (20556302322571 / 20000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (899 / 32768 : ℝ))
    (a := (51390755806427 / 50000000000000 : ℝ)) (b := (20556302322571 / 20000000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_368 :
    (834779 / 5000000 : ℝ) ≤ Real.exp (-(895013 / 500000 : ℝ)) ∧
    Real.exp (-(895013 / 500000 : ℝ)) ≤ (1669559 / 10000000 : ℝ) := by
  have hsmall : (10575324451 / 10000000000 : ℝ) ≤ Real.exp (895013 / 16000000 : ℝ) ∧
      Real.exp (895013 / 16000000 : ℝ) ≤ (2643831113 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (895013 / 16000000 : ℝ))
    (a := (10575324451 / 10000000000 : ℝ)) (b := (2643831113 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_369 :
    (1764087 / 10000000 : ℝ) ≤ Real.exp (-(17349517 / 10000000 : ℝ)) ∧
    Real.exp (-(17349517 / 10000000 : ℝ)) ≤ (220511 / 1250000 : ℝ) := by
  have hsmall : (10557139211 / 10000000000 : ℝ) ≤ Real.exp (17349517 / 320000000 : ℝ) ∧
      Real.exp (17349517 / 320000000 : ℝ) ≤ (2639284803 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (17349517 / 320000000 : ℝ))
    (a := (10557139211 / 10000000000 : ℝ)) (b := (2639284803 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_370 :
    (259523 / 625000 : ℝ) ≤ Real.exp (-(225 / 256 : ℝ)) ∧
    Real.exp (-(225 / 256 : ℝ)) ≤ (4152369 / 10000000 : ℝ) := by
  have hsmall : (1027846483 / 1000000000 : ℝ) ≤ Real.exp (225 / 8192 : ℝ) ∧
      Real.exp (225 / 8192 : ℝ) ≤ (10278464831 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (225 / 8192 : ℝ))
    (a := (1027846483 / 1000000000 : ℝ)) (b := (10278464831 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_371 :
    (198389 / 80000 : ℝ) ≤ Real.exp (465 / 512 : ℝ) ∧
    Real.exp (465 / 512 : ℝ) ≤ (12399313 / 5000000 : ℝ) := by
  have hsmall : (102878793549263 / 100000000000000 : ℝ) ≤ Real.exp (465 / 16384 : ℝ) ∧
      Real.exp (465 / 16384 : ℝ) ≤ (6429924596829 / 6250000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (465 / 16384 : ℝ))
    (a := (102878793549263 / 100000000000000 : ℝ)) (b := (6429924596829 / 6250000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_372 :
    (734837 / 1250000 : ℝ) ≤ Real.exp (-(17 / 32 : ℝ)) ∧
    Real.exp (-(17 / 32 : ℝ)) ≤ (5878697 / 10000000 : ℝ) := by
  have hsmall : (5083700671 / 5000000000 : ℝ) ≤ Real.exp (17 / 1024 : ℝ) ∧
      Real.exp (17 / 1024 : ℝ) ≤ (10167401343 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (17 / 1024 : ℝ))
    (a := (5083700671 / 5000000000 : ℝ)) (b := (10167401343 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_373 :
    (197167 / 1250000 : ℝ) ≤ Real.exp (-(9234237 / 5000000 : ℝ)) ∧
    Real.exp (-(9234237 / 5000000 : ℝ)) ≤ (1577337 / 10000000 : ℝ) := by
  have hsmall : (5297059703 / 5000000000 : ℝ) ≤ Real.exp (9234237 / 160000000 : ℝ) ∧
      Real.exp (9234237 / 160000000 : ℝ) ≤ (10594119407 / 10000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (9234237 / 160000000 : ℝ))
    (a := (5297059703 / 5000000000 : ℝ)) (b := (10594119407 / 10000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_374 :
    (1669559 / 10000000 : ℝ) ≤ Real.exp (-(71601 / 40000 : ℝ)) ∧
    Real.exp (-(71601 / 40000 : ℝ)) ≤ (41739 / 250000 : ℝ) := by
  have hsmall : (10575324121 / 10000000000 : ℝ) ≤ Real.exp (71601 / 1280000 : ℝ) ∧
      Real.exp (71601 / 1280000 : ℝ) ≤ (5287662061 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (71601 / 1280000 : ℝ))
    (a := (10575324121 / 10000000000 : ℝ)) (b := (5287662061 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_375 :
    (6390211 / 2500000 : ℝ) ≤ Real.exp (961 / 1024 : ℝ) ∧
    Real.exp (961 / 1024 : ℝ) ≤ (5112169 / 2000000 : ℝ) := by
  have hsmall : (51488083781151 / 50000000000000 : ℝ) ≤ Real.exp (961 / 32768 : ℝ) ∧
      Real.exp (961 / 32768 : ℝ) ≤ (102976167562303 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (961 / 32768 : ℝ))
    (a := (51488083781151 / 50000000000000 : ℝ)) (b := (102976167562303 / 100000000000000 : ℝ))
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


theorem n1_exp_377 :
    (1487523 / 10000000 : ℝ) ≤ Real.exp (-(19054727 / 10000000 : ℝ)) ∧
    Real.exp (-(19054727 / 10000000 : ℝ)) ≤ (371881 / 2500000 : ℝ) := by
  have hsmall : (10613546053 / 10000000000 : ℝ) ≤ Real.exp (19054727 / 320000000 : ℝ) ∧
      Real.exp (19054727 / 320000000 : ℝ) ≤ (5306773027 / 5000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (19054727 / 320000000 : ℝ))
    (a := (10613546053 / 10000000000 : ℝ)) (b := (5306773027 / 5000000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_378 :
    (788669 / 5000000 : ℝ) ≤ Real.exp (-(1154279 / 625000 : ℝ)) ∧
    Real.exp (-(1154279 / 625000 : ℝ)) ≤ (1577339 / 10000000 : ℝ) := by
  have hsmall : (423764763 / 400000000 : ℝ) ≤ Real.exp (1154279 / 20000000 : ℝ) ∧
      Real.exp (1154279 / 20000000 : ℝ) ≤ (2648529769 / 2500000000 : ℝ) := by
    apply enclosure_of_taylor (n := 10)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact neg_enclosure_of_scaled (n := 32) (x := (1154279 / 20000000 : ℝ))
    (a := (423764763 / 400000000 : ℝ)) (b := (2648529769 / 2500000000 : ℝ))
    (by norm_num) (by norm_num) hsmall (by norm_num) (by norm_num)


theorem n1_exp_379 :
    (2634649 / 1000000 : ℝ) ≤ Real.exp (31 / 32 : ℝ) ∧
    Real.exp (31 / 32 : ℝ) ≤ (26346491 / 10000000 : ℝ) := by
  have hsmall : (1288420421739 / 1250000000000 : ℝ) ≤ Real.exp (31 / 1024 : ℝ) ∧
      Real.exp (31 / 1024 : ℝ) ≤ (103073633739121 / 100000000000000 : ℝ) := by
    apply enclosure_of_taylor (n := 16)
    · norm_num
    · norm_num
    · norm_num [Finset.sum_range_succ, Nat.factorial]
    · norm_num [Finset.sum_range_succ, Nat.factorial]
  exact enclosure_of_scaled (n := 32) (x := (31 / 1024 : ℝ))
    (a := (1288420421739 / 1250000000000 : ℝ)) (b := (103073633739121 / 100000000000000 : ℝ))
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
theorem cell_042 (x : ℝ) (hx : x ∈ Set.Ioo (0 / 1 : ℝ) (1 / 64 : ℝ)) :
    density x ≤ (387741 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (2231301 / 10000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (2302131 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_235.1 n1_exp_239.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (2231301 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (7009837 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (7232359 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (4851797 / 10000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (4960971 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_240.1 n1_exp_241.2
  have hpoly : (36552693 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (7741831 / 20000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (4851797 / 10000000 : ℝ))
      (by norm_num : (4960971 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (36552693 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (7741831 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (0 / 1 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
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
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (2576841 / 2500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_242.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (56363879 / 50000000 : ℝ) (56419 / 50000 : ℝ) (36552693 / 50000000 : ℝ) (7741831 / 10000000 : ℝ)
    (6104137 / 100000000 : ℝ) (2576841 / 2500000 : ℝ) (387741 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_043 (x : ℝ) (hx : x ∈ Set.Ioo (1 / 64 : ℝ) (1 / 32 : ℝ)) :
    density x ≤ (16907 / 4000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (230213 / 1000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (2375209 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_239.1 n1_exp_243.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (230213 / 1000000 : ℝ)) pi_rational_enclosure hi
  have ha : (7232353 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (373097 / 500000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (2370839 / 5000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (4851801 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_244.1 n1_exp_245.2
  have hpoly : (18227671 / 50000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (38556827 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (2370839 / 5000000 : ℝ))
      (by norm_num : (4851801 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (18227671 / 25000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (38556827 / 50000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1 / 64 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
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
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (5312087 / 5000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_246.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (56198989 / 50000000 : ℝ) (112727871 / 100000000 : ℝ) (18227671 / 25000000 : ℝ) (38556827 / 50000000 : ℝ)
    (6278273 / 100000000 : ℝ) (5312087 / 5000000 : ℝ) (16907 / 4000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_044 (x : ℝ) (hx : x ∈ Set.Ioo (1 / 32 : ℝ) (3 / 64 : ℝ)) :
    density x ≤ (91037 / 20000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (296901 / 1250000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (1225303 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_243.1 n1_exp_247.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (296901 / 1250000 : ℝ)) pi_rational_enclosure hi
  have ha : (3730967 / 5000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (7698807 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (4630683 / 10000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (4741681 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_248.1 n1_exp_249.2
  have hpoly : (7258909 / 20000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (19170871 / 50000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (4630683 / 10000000 : ℝ))
      (by norm_num : (4741681 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (7258909 / 10000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (19170871 / 25000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1 / 32 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
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
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (10950723 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_250.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (223701 / 200000 : ℝ) (11239809 / 10000000 : ℝ) (7258909 / 10000000 : ℝ) (19170871 / 25000000 : ℝ)
    (6418019 / 100000000 : ℝ) (10950723 / 10000000 : ℝ) (91037 / 20000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_045 (x : ℝ) (hx : x ∈ Set.Ioo (3 / 64 : ℝ) (1 / 16 : ℝ)) :
    density x ≤ (7571 / 1562500 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (490121 / 2000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (632099 / 2500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_247.1 n1_exp_251.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (490121 / 2000000 : ℝ)) pi_rational_enclosure hi
  have ha : (7698801 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (992899 / 1250000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (4518887 / 10000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (2315343 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_252.1 n1_exp_253.2
  have hpoly : (36071183 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (38064961 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (4518887 / 10000000 : ℝ))
      (by norm_num : (2315343 / 5000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (36071183 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (38064961 / 50000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3 / 64 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
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
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (2821827 / 2500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_254.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (55544253 / 50000000 : ℝ) (27962653 / 25000000 : ℝ) (36071183 / 50000000 : ℝ) (38064961 / 50000000 : ℝ)
    (3261379 / 50000000 : ℝ) (2821827 / 2500000 : ℝ) (7571 / 1562500 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_046 (x : ℝ) (hx : x ∈ Set.Ioo (1 / 16 : ℝ) (5 / 64 : ℝ)) :
    density x ≤ (63757 / 12500000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (505679 / 2000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (163041 / 625000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_251.1 n1_exp_255.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (505679 / 2000000 : ℝ)) pi_rational_enclosure hi
  have ha : (1588637 / 2000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (1024417 / 1250000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (4406371 / 10000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (4518891 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_256.1 n1_exp_257.2
  have hpoly : (35786497 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (37727783 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (4406371 / 10000000 : ℝ))
      (by norm_num : (4518891 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (35786497 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (37727783 / 50000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1 / 16 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
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
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (5817119 / 5000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_258.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (110116419 / 100000000 : ℝ) (111088617 / 100000000 : ℝ) (35786497 / 50000000 : ℝ) (37727783 / 50000000 : ℝ)
    (3296023 / 50000000 : ℝ) (5817119 / 5000000 : ℝ) (63757 / 12500000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_047 (x : ℝ) (hx : x ∈ Set.Ioo (5 / 64 : ℝ) (3 / 32 : ℝ)) :
    density x ≤ (531121 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (521731 / 2000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (336433 / 1250000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_255.1 n1_exp_259.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (521731 / 2000000 : ℝ)) pi_rational_enclosure hi
  have ha : (8195329 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (1691097 / 2000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (2146609 / 5000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (35251 / 80000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_260.1 n1_exp_261.2
  have hpoly : (17721 / 50000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (37331807 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (2146609 / 5000000 : ℝ))
      (by norm_num : (35251 / 80000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (17721 / 25000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (37331807 / 50000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5 / 64 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
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
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (1498979 / 1250000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_262.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (54469929 / 50000000 : ℝ) (6882283 / 6250000 : ℝ) (17721 / 25000 : ℝ) (37331807 / 50000000 : ℝ)
    (207059 / 3125000 : ℝ) (1498979 / 1250000 : ℝ) (531121 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_048 (x : ℝ) (hx : x ∈ Set.Ioo (3 / 32 : ℝ) (7 / 64 : ℝ)) :
    density x ≤ (547237 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (2691463 / 10000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (27769 / 100000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_259.1 n1_exp_263.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (2691463 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (4227739 / 5000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (872389 / 1000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (2089759 / 5000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (2146611 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_264.1 n1_exp_265.2
  have hpoly : (2189969 / 6250000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (9219723 / 25000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (2089759 / 5000000 : ℝ))
      (by norm_num : (2146611 / 5000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (2189969 / 3125000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (9219723 / 12500000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3 / 32 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
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
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (12360417 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_266.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (107565571 / 100000000 : ℝ) (108939967 / 100000000 : ℝ) (2189969 / 3125000 : ℝ) (9219723 / 12500000 : ℝ)
    (828077 / 12500000 : ℝ) (12360417 / 10000000 : ℝ) (547237 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_049 (x : ℝ) (hx : x ∈ Set.Ioo (7 / 64 : ℝ) (1 / 8 : ℝ)) :
    density x ≤ (558023 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (2776899 / 10000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (358131 / 1250000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_263.1 n1_exp_267.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (2776899 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (8723883 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (1800163 / 2000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (813073 / 2000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (2089761 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_268.1 n1_exp_269.2
  have hpoly : (17290539 / 50000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (4546397 / 12500000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (813073 / 2000000 : ℝ))
      (by norm_num : (2089761 / 5000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (17290539 / 25000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (4546397 / 6250000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7 / 64 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
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
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (12740331 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_270.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (10600139 / 10000000 : ℝ) (107565679 / 100000000 : ℝ) (17290539 / 25000000 : ℝ) (4546397 / 6250000 : ℝ)
    (1647233 / 25000000 : ℝ) (12740331 / 10000000 : ℝ) (558023 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_050 (x : ℝ) (hx : x ∈ Set.Ioo (1 / 8 : ℝ) (9 / 64 : ℝ)) :
    density x ≤ (281629 / 50000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (2865047 / 10000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (591199 / 2000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_267.1 n1_exp_271.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (2865047 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (1125101 / 1250000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (4643267 / 5000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (3950853 / 10000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (4065369 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_272.1 n1_exp_273.2
  have hpoly : (34069 / 100000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (7162211 / 20000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (3950853 / 10000000 : ℝ))
      (by norm_num : (4065369 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (34069 / 50000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (7162211 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1 / 8 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
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
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (6565961 / 5000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_274.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (52128063 / 50000000 : ℝ) (13250187 / 12500000 : ℝ) (34069 / 50000 : ℝ) (7162211 / 10000000 : ℝ)
    (407501 / 6250000 : ℝ) (6565961 / 5000000 : ℝ) (281629 / 50000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_051 (x : ℝ) (hx : x ∈ Set.Ioo (9 / 64 : ℝ) (5 / 32 : ℝ)) :
    density x ≤ (562809 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (1477997 / 5000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (762457 / 2500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_271.1 n1_exp_275.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1477997 / 5000000 : ℝ)) pi_rational_enclosure hi
  have ha : (9286527 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (9581319 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (479511 / 1250000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (3950857 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_276.1 n1_exp_277.2
  have hpoly : (33505881 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (4400133 / 12500000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (479511 / 1250000 : ℝ))
      (by norm_num : (3950857 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (33505881 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (4400133 / 6250000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (9 / 64 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
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
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (13535549 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_278.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (102339529 / 100000000 : ℝ) (104256231 / 100000000 : ℝ) (33505881 / 50000000 : ℝ) (4400133 / 6250000 : ℝ)
    (6419059 / 100000000 : ℝ) (13535549 / 10000000 : ℝ) (562809 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_052 (x : ℝ) (hx : x ∈ Set.Ioo (5 / 32 : ℝ) (11 / 64 : ℝ)) :
    density x ≤ (34797 / 6250000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (3049827 / 10000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (39333 / 125000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_275.1 n1_exp_279.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (3049827 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (74854 / 78125 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (9885463 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (930293 / 2500000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (959023 / 2500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_280.1 n1_exp_281.2
  have hpoly : (16447211 / 50000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (17272027 / 50000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (930293 / 2500000 : ℝ))
      (by norm_num : (959023 / 2500000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (16447211 / 25000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (17272027 / 25000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5 / 32 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
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
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (6975791 / 5000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_282.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (50131069 / 50000000 : ℝ) (6396227 / 6250000 : ℝ) (16447211 / 25000000 : ℝ) (17272027 / 25000000 : ℝ)
    (78599 / 1250000 : ℝ) (6975791 / 5000000 : ℝ) (34797 / 6250000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_053 (x : ℝ) (hx : x ∈ Set.Ioo (11 / 64 : ℝ) (3 / 16 : ℝ)) :
    density x ≤ (27263 / 5000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (3146639 / 10000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (129861 / 400000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_279.1 n1_exp_283.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (3146639 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (1977091 / 2000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (10199261 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (721243 / 2000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (465147 / 1250000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_284.1 n1_exp_285.2
  have hpoly : (32237593 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (4230369 / 12500000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (721243 / 2000000 : ℝ))
      (by norm_num : (465147 / 1250000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (32237593 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (4230369 / 6250000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (11 / 64 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
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
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (14380403 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_286.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (4901763 / 5000000 : ℝ) (100262239 / 100000000 : ℝ) (32237593 / 50000000 : ℝ) (4230369 / 6250000 : ℝ)
    (1532117 / 25000000 : ℝ) (14380403 / 10000000 : ℝ) (27263 / 5000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_054 (x : ℝ) (hx : x ∈ Set.Ioo (3 / 16 : ℝ) (13 / 64 : ℝ)) :
    density x ≤ (264331 / 50000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (811631 / 2500000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (3349581 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_283.1 n1_exp_287.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (811631 / 2500000 : ℝ)) pi_rational_enclosure hi
  have ha : (10199253 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (10523021 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (349133 / 1000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (3606219 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_288.1 n1_exp_289.2
  have hpoly : (31538503 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (33100883 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (349133 / 1000000 : ℝ))
      (by norm_num : (3606219 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (31538503 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (33100883 / 50000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3 / 16 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
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
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (3705601 / 2500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_290.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (47835399 / 50000000 : ℝ) (98035359 / 100000000 : ℝ) (31538503 / 50000000 : ℝ) (33100883 / 50000000 : ℝ)
    (5942931 / 100000000 : ℝ) (3705601 / 2500000 : ℝ) (264331 / 50000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_055 (x : ℝ) (hx : x ∈ Set.Ioo (13 / 64 : ℝ) (7 / 32 : ℝ)) :
    density x ≤ (253699 / 50000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (167479 / 500000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (863977 / 2500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_287.1 n1_exp_291.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (167479 / 500000 : ℝ)) pi_rational_enclosure hi
  have ha : (10523013 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (10857057 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (1688317 / 5000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (1745667 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_292.1 n1_exp_293.2
  have hpoly : (3080041 / 10000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (8080273 / 25000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (1688317 / 5000000 : ℝ))
      (by norm_num : (1745667 / 5000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (3080041 / 5000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (8080273 / 12500000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (13 / 64 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
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
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (1527799 / 1000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_294.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (93181199 / 100000000 : ℝ) (19134179 / 20000000 : ℝ) (3080041 / 5000000 : ℝ) (8080273 / 12500000 : ℝ)
    (2866849 / 50000000 : ℝ) (1527799 / 1000000 : ℝ) (253699 / 50000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_056 (x : ℝ) (hx : x ∈ Set.Ioo (7 / 32 : ℝ) (15 / 64 : ℝ)) :
    density x ≤ (482037 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (3455907 / 10000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (356561 / 1000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_291.1 n1_exp_295.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (3455907 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (10857049 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (350053 / 312500 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (815561 / 2500000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (3376637 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_296.1 n1_exp_297.2
  have hpoly : (30026659 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (31506933 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (815561 / 2500000 : ℝ))
      (by norm_num : (3376637 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (30026659 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (31506933 / 50000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7 / 32 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
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
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (787379 / 500000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_298.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (22644823 / 25000000 : ℝ) (46590647 / 50000000 : ℝ) (30026659 / 50000000 : ℝ) (31506933 / 50000000 : ℝ)
    (110069 / 2000000 : ℝ) (787379 / 500000 : ℝ) (482037 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_057 (x : ℝ) (hx : x ∈ Set.Ioo (15 / 64 : ℝ) (1 / 4 : ℝ)) :
    density x ≤ (90643 / 20000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (3565609 / 10000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (735759 / 2000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_295.1 n1_exp_299.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (3565609 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (1400211 / 1250000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (11557277 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (3148283 / 10000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (407781 / 1250000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_300.1 n1_exp_301.2
  have hpoly : (29220713 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (6132367 / 20000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (3148283 / 10000000 : ℝ))
      (by norm_num : (407781 / 1250000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (29220713 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (6132367 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (15 / 64 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
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
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (16231603 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_302.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (17575647 / 20000000 : ℝ) (18115877 / 20000000 : ℝ) (29220713 / 50000000 : ℝ) (6132367 / 10000000 : ℝ)
    (656863 / 12500000 : ℝ) (16231603 / 10000000 : ℝ) (90643 / 20000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_058 (x : ℝ) (hx : x ∈ Set.Ioo (1 / 4 : ℝ) (17 / 64 : ℝ)) :
    density x ≤ (210817 / 50000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (1839397 / 5000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (948893 / 2500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_299.1 n1_exp_303.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1839397 / 5000000 : ℝ)) pi_rational_enclosure hi
  have ha : (11557269 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (11924143 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (758719 / 2500000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (3148287 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_304.1 n1_exp_305.2
  have hpoly : (28386103 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (29789253 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (758719 / 2500000 : ℝ))
      (by norm_num : (3148287 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (28386103 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (29789253 / 50000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (1 / 4 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (1885257 / 2500000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (973501 / 1250000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_306.1 n1_exp_157.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1885257 / 2500000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (5318211 / 6250000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (3515133 / 4000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (16730503 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_307.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (5318211 / 6250000 : ℝ) (3515133 / 4000000 : ℝ) (28386103 / 50000000 : ℝ) (29789253 / 50000000 : ℝ)
    (998181 / 20000000 : ℝ) (16730503 / 10000000 : ℝ) (210817 / 50000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_059 (x : ℝ) (hx : x ∈ Set.Ioo (17 / 64 : ℝ) (9 / 32 : ℝ)) :
    density x ≤ (388049 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (3795571 / 10000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (3916057 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_303.1 n1_exp_308.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (3795571 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (2384827 / 2000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (6151329 / 5000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (730537 / 2500000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (4742 / 15625 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_309.1 n1_exp_310.2
  have hpoly : (860199 / 3125000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (3611589 / 12500000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (730537 / 2500000 : ℝ))
      (by norm_num : (4742 / 15625 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (860199 / 1562500 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (3611589 / 6250000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (17 / 64 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (7287633 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (7541029 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_311.1 n1_exp_306.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (7287633 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (2055803 / 2500000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (10636433 / 12500000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (17244737 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_312.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (2055803 / 2500000 : ℝ) (10636433 / 12500000 : ℝ) (860199 / 1562500 : ℝ) (3611589 / 6250000 : ℝ)
    (471447 / 10000000 : ℝ) (17244737 / 10000000 : ℝ) (388049 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_060 (x : ℝ) (hx : x ∈ Set.Ioo (9 / 32 : ℝ) (19 / 64 : ℝ)) :
    density x ≤ (353201 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (489507 / 1250000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (2020183 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_308.1 n1_exp_313.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (489507 / 1250000 : ℝ)) pi_rational_enclosure hi
  have ha : (246053 / 200000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (6346593 / 5000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (281023 / 1000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (365269 / 1250000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_314.1 n1_exp_315.2
  have hpoly : (3330639 / 12500000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (13987849 / 50000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (281023 / 1000000 : ℝ))
      (by norm_num : (365269 / 1250000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (3330639 / 6250000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (13987849 / 25000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (9 / 32 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (7029011 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (3643817 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_316.1 n1_exp_311.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (7029011 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (19828471 / 25000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (16446441 / 20000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (17774777 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_317.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (19828471 / 25000000 : ℝ) (16446441 / 20000000 : ℝ) (3330639 / 6250000 : ℝ) (13987849 / 25000000 : ℝ)
    (2214239 / 50000000 : ℝ) (17774777 / 10000000 : ℝ) (353201 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_061 (x : ℝ) (hx : x ∈ Set.Ioo (19 / 64 : ℝ) (5 / 16 : ℝ)) :
    density x ≤ (317851 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (808073 / 2000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (4168621 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_313.1 n1_exp_318.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (808073 / 2000000 : ℝ)) pi_rational_enclosure hi
  have ha : (6346589 / 5000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (13096111 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (10797 / 40000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (2810233 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_319.1 n1_exp_320.2
  have hpoly : (25745879 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (13520861 / 50000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (10797 / 40000 : ℝ))
      (by norm_num : (2810233 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (25745879 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (13520861 / 25000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (19 / 64 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (3383169 / 5000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (1757253 / 2500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_321.1 n1_exp_316.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (3383169 / 5000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (76349937 / 100000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (39656983 / 50000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (18321109 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_322.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (76349937 / 100000000 : ℝ) (39656983 / 50000000 : ℝ) (25745879 / 50000000 : ℝ) (13520861 / 25000000 : ℝ)
    (517 / 12500 : ℝ) (18321109 / 10000000 : ℝ) (317851 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_062 (x : ℝ) (hx : x ∈ Set.Ioo (5 / 16 : ℝ) (21 / 64 : ℝ)) :
    density x ≤ (282711 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (208431 / 500000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (4300947 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_318.1 n1_exp_323.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (208431 / 500000 : ℝ)) pi_rational_enclosure hi
  have ha : (13096103 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (540473 / 400000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (1294669 / 5000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (2699253 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_324.1 n1_exp_325.2
  have hpoly : (24832197 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (26094239 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (1294669 / 5000000 : ℝ))
      (by norm_num : (2699253 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (24832197 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (26094239 / 50000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (5 / 16 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (1625193 / 2500000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (6766339 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_326.1 n1_exp_321.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1625193 / 2500000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (36676673 / 50000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (76350017 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (2360529 / 1250000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_327.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (36676673 / 50000000 : ℝ) (76350017 / 100000000 : ℝ) (24832197 / 50000000 : ℝ) (26094239 / 50000000 : ℝ)
    (1920001 / 50000000 : ℝ) (2360529 / 1250000 : ℝ) (282711 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_063 (x : ℝ) (hx : x ∈ Set.Ioo (21 / 64 : ℝ) (11 / 32 : ℝ)) :
    density x ≤ (24843 / 10000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (2150473 / 5000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (2218737 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_323.1 n1_exp_328.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (2150473 / 5000000 : ℝ)) pi_rational_enclosure hi
  have ha : (13511817 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (6970369 / 5000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (1240313 / 5000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (2589341 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_329.1 n1_exp_330.2
  have hpoly : (23907559 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (25136621 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (1240313 / 5000000 : ℝ))
      (by norm_num : (2589341 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (23907559 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (25136621 / 50000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (21 / 64 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (6233443 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (6500773 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_331.1 n1_exp_326.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (6233443 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (70336861 / 100000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (73353423 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (2433083 / 1250000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_332.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (70336861 / 100000000 : ℝ) (73353423 / 100000000 : ℝ) (23907559 / 50000000 : ℝ) (25136621 / 50000000 : ℝ)
    (3543351 / 100000000 : ℝ) (2433083 / 1250000 : ℝ) (24843 / 10000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_064 (x : ℝ) (hx : x ∈ Set.Ioo (11 / 32 : ℝ) (23 / 64 : ℝ)) :
    density x ≤ (218381 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (4437473 / 10000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (2289167 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_328.1 n1_exp_333.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (4437473 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (13940729 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (14383263 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (1186623 / 5000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (248063 / 1000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_334.1 n1_exp_335.2
  have hpoly : (22975381 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (24172201 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (1186623 / 5000000 : ℝ))
      (by norm_num : (248063 / 1000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (22975381 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (24172201 / 50000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (11 / 32 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (1491361 / 2500000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (1558361 / 2500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_336.1 n1_exp_331.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1491361 / 2500000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (67312817 / 100000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (8792117 / 12500000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (20062937 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_337.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (67312817 / 100000000 : ℝ) (8792117 / 12500000 : ℝ) (22975381 / 50000000 : ℝ) (24172201 / 50000000 : ℝ)
    (327001 / 10000000 : ℝ) (20062937 / 10000000 : ℝ) (218381 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_065 (x : ℝ) (hx : x ∈ Set.Ioo (23 / 64 : ℝ) (3 / 8 : ℝ)) :
    density x ≤ (126107 / 50000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (4578333 / 10000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (2361833 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_333.1 n1_exp_338.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (4578333 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (7191627 / 5000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (14839837 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (1133663 / 5000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (2373249 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_339.1 n1_exp_340.2
  have hpoly : (22038959 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (1160209 / 5000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (1133663 / 5000000 : ℝ))
      (by norm_num : (2373249 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (22038959 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (1160209 / 2500000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (23 / 64 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (1424457 / 2500000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (1193089 / 2000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_341.1 n1_exp_336.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1424457 / 2500000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (32146547 / 50000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (67312889 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (10339799 / 5000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_342.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (32146547 / 50000000 : ℝ) (67312889 / 100000000 : ℝ) (22038959 / 50000000 : ℝ) (1160209 / 2500000 : ℝ)
    (432889 / 12500000 : ℝ) (10339799 / 5000000 : ℝ) (126107 / 50000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_066 (x : ℝ) (hx : x ∈ Set.Ioo (3 / 8 : ℝ) (25 / 64 : ℝ)) :
    density x ≤ (57367 / 20000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (944733 / 2000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (4873611 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_338.1 n1_exp_343.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (944733 / 2000000 : ℝ)) pi_rational_enclosure hi
  have ha : (3709957 / 2500000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (15310903 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (2162997 / 10000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (2267329 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_344.1 n1_exp_345.2
  have hpoly : (21101521 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (22235671 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (2162997 / 10000000 : ℝ))
      (by norm_num : (2267329 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (21101521 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (22235671 / 50000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (3 / 8 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (2715799 / 5000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (5697829 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_346.1 n1_exp_341.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (2715799 / 5000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (61289011 / 100000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (64293163 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (21315213 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_347.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (61289011 / 100000000 : ℝ) (64293163 / 100000000 : ℝ) (21101521 / 50000000 : ℝ) (22235671 / 50000000 : ℝ)
    (3639149 / 100000000 : ℝ) (21315213 / 10000000 : ℝ) (57367 / 20000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_067 (x : ℝ) (hx : x ∈ Set.Ioo (25 / 64 : ℝ) (13 / 32 : ℝ)) :
    density x ≤ (321499 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (487361 / 1000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (1257079 / 2500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_343.1 n1_exp_348.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (487361 / 1000000 : ℝ)) pi_rational_enclosure hi
  have ha : (7655447 / 5000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (15796923 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (64387 / 312500 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (2163 / 10000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_349.1 n1_exp_350.2
  have hpoly : (10083063 / 50000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (21269673 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (64387 / 312500 : ℝ))
      (by norm_num : (2163 / 10000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (10083063 / 25000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (21269673 / 50000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (25 / 64 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (1033541 / 2000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (5431599 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_351.1 n1_exp_346.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1033541 / 2000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (29155649 / 50000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (61289077 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (4394073 / 2000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_352.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (29155649 / 50000000 : ℝ) (61289077 / 100000000 : ℝ) (10083063 / 25000000 : ℝ) (21269673 / 50000000 : ℝ)
    (949037 / 25000000 : ℝ) (4394073 / 2000000 : ℝ) (321499 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_068 (x : ℝ) (hx : x ∈ Set.Ioo (13 / 32 : ℝ) (27 / 64 : ℝ)) :
    density x ≤ (355391 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (1005663 / 2000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (1296983 / 2500000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_348.1 n1_exp_353.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1005663 / 2000000 : ℝ)) pi_rational_enclosure hi
  have ha : (7898457 / 5000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (16298371 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (979807 / 5000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (2060387 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_354.1 n1_exp_355.2
  have hpoly : (19235749 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (5077253 / 25000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (979807 / 5000000 : ℝ))
      (by norm_num : (2060387 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (19235749 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (5077253 / 12500000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (13 / 32 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (30669 / 62500 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (2583853 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_356.1 n1_exp_351.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (30669 / 62500 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (6921251 / 12500000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (58311361 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (22645653 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_357.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (6921251 / 12500000 : ℝ) (58311361 / 100000000 : ℝ) (19235749 / 50000000 : ℝ) (5077253 / 12500000 : ℝ)
    (983077 / 25000000 : ℝ) (22645653 / 10000000 : ℝ) (355391 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_069 (x : ℝ) (hx : x ∈ Set.Ioo (27 / 64 : ℝ) (7 / 16 : ℝ)) :
    density x ≤ (96923 / 25000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (5187931 / 10000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (1070523 / 2000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_353.1 n1_exp_358.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (5187931 / 10000000 : ℝ)) pi_rational_enclosure hi
  have ha : (8149181 / 5000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (8407869 / 5000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (232601 / 1250000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (1959617 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_359.1 n1_exp_360.2
  have hpoly : (18313179 / 100000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (967821 / 5000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (232601 / 1250000 : ℝ))
      (by norm_num : (1959617 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (18313179 / 50000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (967821 / 2500000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (27 / 64 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (4650431 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (4907041 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_361.1 n1_exp_356.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (4650431 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (26237243 / 50000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (5537007 / 10000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (11670849 / 5000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_362.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (26237243 / 50000000 : ℝ) (5537007 / 10000000 : ℝ) (18313179 / 50000000 : ℝ) (967821 / 2500000 : ℝ)
    (4046261 / 100000000 : ℝ) (11670849 / 5000000 : ℝ) (96923 / 25000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_070 (x : ℝ) (hx : x ∈ Set.Ioo (7 / 16 : ℝ) (29 / 64 : ℝ)) :
    density x ≤ (417567 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (2676307 / 5000000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (220901 / 400000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_358.1 n1_exp_363.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (2676307 / 5000000 : ℝ)) pi_rational_enclosure hi
  have ha : (16815729 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (8674763 / 5000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (352817 / 2000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (1860811 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_364.1 n1_exp_365.2
  have hpoly : (1087567 / 6250000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (18414447 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (352817 / 2000000 : ℝ))
      (by norm_num : (1860811 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (1087567 / 3125000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (18414447 / 50000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (7 / 16 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (2199321 / 5000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (72663 / 156250 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_366.1 n1_exp_361.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (2199321 / 5000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (6204169 / 12500000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (10494909 / 20000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (187962 / 78125 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_367.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (6204169 / 12500000 : ℝ) (10494909 / 20000000 : ℝ) (1087567 / 3125000 : ℝ) (18414447 / 50000000 : ℝ)
    (2068417 / 50000000 : ℝ) (187962 / 78125 : ℝ) (417567 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_071 (x : ℝ) (hx : x ∈ Set.Ioo (29 / 64 : ℝ) (15 / 32 : ℝ)) :
    density x ≤ (444227 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (1380631 / 2500000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (5697829 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_363.1 n1_exp_341.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1380631 / 2500000 : ℝ)) pi_rational_enclosure hi
  have ha : (17349517 / 10000000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (895013 / 500000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (834779 / 5000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (220511 / 1250000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_368.1 n1_exp_369.2
  have hpoly : (8250949 / 50000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (8742751 / 50000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (834779 / 5000000 : ℝ))
      (by norm_num : (220511 / 1250000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (8250949 / 25000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (8742751 / 25000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (29 / 64 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (259523 / 625000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (4398643 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_370.1 n1_exp_366.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (259523 / 625000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (2928403 / 6250000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (387761 / 781250 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (12399313 / 5000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_371.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (2928403 / 6250000 : ℝ) (387761 / 781250 : ℝ) (8250949 / 25000000 : ℝ) (8742751 / 25000000 : ℝ)
    (2101609 / 50000000 : ℝ) (12399313 / 5000000 : ℝ) (444227 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_072 (x : ℝ) (hx : x ∈ Set.Ioo (15 / 32 : ℝ) (31 / 64 : ℝ)) :
    density x ≤ (466937 / 100000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (1424457 / 2500000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (5878697 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_341.1 n1_exp_372.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1424457 / 2500000 : ℝ)) pi_rational_enclosure hi
  have ha : (71601 / 40000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (9234237 / 5000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (197167 / 1250000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (41739 / 250000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_373.1 n1_exp_374.2
  have hpoly : (1561797 / 10000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (16571809 / 100000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (197167 / 1250000 : ℝ))
      (by norm_num : (41739 / 250000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (1561797 / 5000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (16571809 / 50000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (15 / 32 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (3912233 / 10000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (4152369 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_079.1 n1_exp_370.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (3912233 / 10000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (8828963 / 20000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (23427251 / 50000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (5112169 / 2000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_375.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (8828963 / 20000000 : ℝ) (23427251 / 50000000 : ℝ) (1561797 / 5000000 : ℝ) (16571809 / 50000000 : ℝ)
    (1061217 / 25000000 : ℝ) (5112169 / 2000000 : ℝ) (466937 / 100000000 : ℝ)
    hwindow htheta hp ht (by norm_num) (by norm_num) (by norm_num) hw (by norm_num)

theorem cell_073 (x : ℝ) (hx : x ∈ Set.Ioo (31 / 64 : ℝ) (1 / 2 : ℝ)) :
    density x ≤ (19403 / 4000000 : ℝ) := by
  have hwindow : x ∈ Set.Icc (-4 : ℝ) 4 := by
    constructor <;> linarith only [hx.1, hx.2]
  have hi : (734837 / 1250000 : ℝ) ≤ Real.exp (2 * (x - 3 / 4)) ∧
      Real.exp (2 * (x - 3 / 4)) ≤ (6065307 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (2 * (x - 3 / 4)))
      (by constructor <;> linarith only [hx.1, hx.2]) n1_exp_372.1 n1_exp_376.2
  have ha0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 3141592 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (734837 / 1250000 : ℝ)) pi_rational_enclosure hi
  have ha : (1154279 / 625000 : ℝ) ≤ (Real.pi * Real.exp (2 * (x - 3 / 4))) ∧ (Real.pi * Real.exp (2 * (x - 3 / 4))) ≤ (19054727 / 10000000 : ℝ) := by
    constructor <;> nlinarith only [ha0.1, ha0.2]
  have hrange : (1487523 / 10000000 : ℝ) ≤ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧ (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (1577339 / 10000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := (-Real.pi * Real.exp (2 * (x - 3 / 4))))
      (by constructor <;> nlinarith only [ha.1, ha.2]) n1_exp_377.1 n1_exp_378.2
  have hpoly : (1475143 / 10000000 : ℝ) ≤ thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ∧
      thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))) ≤ (7837737 / 50000000 : ℝ) := by
    apply thetaPolynomial_six_enclosure_of_bounds
      (by norm_num : (0 : ℝ) ≤ (1487523 / 10000000 : ℝ))
      (by norm_num : (1577339 / 10000000 : ℝ) ≤ (1 : ℝ)) hrange
    · norm_num
    · norm_num
  have htheta : thetaPartialReflected 6 (x - 3 / 4) = (((2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) : ℝ) : ℂ) :=
    thetaPartialReflected_eq_direct 6 (x - 3 / 4) (by linarith only [hx.1])
  have ht : (1475143 / 5000000 : ℝ) ≤ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ∧ (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4))))) ≤ (7837737 / 25000000 : ℝ) := by
    constructor <;> nlinarith only [hpoly.1, hpoly.2]
  have hxsign : 0 ≤ x := by linarith only [hx.1]
  have hsL := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ (31 / 64 : ℝ)) hx.1.le 2
  have hsU := pow_le_pow_left₀ hxsign hx.2.le 2
  have hpe : (1839397 / 5000000 : ℝ) ≤ Real.exp (-4 * x ^ 2) ∧
      Real.exp (-4 * x ^ 2) ≤ (1956117 / 5000000 : ℝ) := by
    simpa only [zero_div, div_one] using enclosure_of_argument_interval (x := -4 * x ^ 2)
      (by constructor <;> nlinarith only [hsL, hsU]) n1_exp_299.1 n1_exp_079.2
  have hp0 := nonneg_product_enclosure
    (by norm_num : (0 : ℝ) ≤ 1128379 / 1000000)
    (by norm_num : (0 : ℝ) ≤ (1839397 / 5000000 : ℝ)) pulse_two_coefficient_enclosure hpe
  have hp : (20755369 / 50000000 : ℝ) ≤ realPulse x ∧ realPulse x ≤ (44144867 / 100000000 : ℝ) := by
    unfold realPulse
    constructor <;> nlinarith only [hp0.1, hp0.2]
  have hw : Real.exp ((3 / 2 : ℝ) * x + (7 / 16 : ℝ) * |x|) ≤ (26346491 / 10000000 : ℝ) := by
    apply le_trans (Real.exp_le_exp.mpr _) n1_exp_379.2
    rw [abs_of_nonneg hxsign]
    linarith only [hx.2]
  exact density_le_of_intervals x (2 * thetaPolynomial 6 (Real.exp (-Real.pi * Real.exp (2 * (x - 3 / 4)))))
    (20755369 / 50000000 : ℝ) (44144867 / 100000000 : ℝ) (1475143 / 5000000 : ℝ) (7837737 / 25000000 : ℝ)
    (4261647 / 100000000 : ℝ) (26346491 / 10000000 : ℝ) (19403 / 4000000 : ℝ)
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

/- Exact rational subinterval partition and actual-density assembly. -/
section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
open MeasureTheory Set
open scoped BigOperators
namespace MasulloRH.HeightOne

noncomputable def endpoints : Fin 33 → ℝ :=
  ![(0 / 1 : ℝ), (1 / 64 : ℝ), (1 / 32 : ℝ), (3 / 64 : ℝ), (1 / 16 : ℝ), (5 / 64 : ℝ), (3 / 32 : ℝ), (7 / 64 : ℝ), (1 / 8 : ℝ), (9 / 64 : ℝ), (5 / 32 : ℝ), (11 / 64 : ℝ), (3 / 16 : ℝ), (13 / 64 : ℝ), (7 / 32 : ℝ), (15 / 64 : ℝ), (1 / 4 : ℝ), (17 / 64 : ℝ), (9 / 32 : ℝ), (19 / 64 : ℝ), (5 / 16 : ℝ), (21 / 64 : ℝ), (11 / 32 : ℝ), (23 / 64 : ℝ), (3 / 8 : ℝ), (25 / 64 : ℝ), (13 / 32 : ℝ), (27 / 64 : ℝ), (7 / 16 : ℝ), (29 / 64 : ℝ), (15 / 32 : ℝ), (31 / 64 : ℝ), (1 / 2 : ℝ)]

noncomputable def cellBounds : Fin 32 → ℝ :=
  ![(387741 / 100000000 : ℝ), (16907 / 4000000 : ℝ), (91037 / 20000000 : ℝ), (7571 / 1562500 : ℝ), (63757 / 12500000 : ℝ), (531121 / 100000000 : ℝ), (547237 / 100000000 : ℝ), (558023 / 100000000 : ℝ), (281629 / 50000000 : ℝ), (562809 / 100000000 : ℝ), (34797 / 6250000 : ℝ), (27263 / 5000000 : ℝ), (264331 / 50000000 : ℝ), (253699 / 50000000 : ℝ), (482037 / 100000000 : ℝ), (90643 / 20000000 : ℝ), (210817 / 50000000 : ℝ), (388049 / 100000000 : ℝ), (353201 / 100000000 : ℝ), (317851 / 100000000 : ℝ), (282711 / 100000000 : ℝ), (24843 / 10000000 : ℝ), (218381 / 100000000 : ℝ), (126107 / 50000000 : ℝ), (57367 / 20000000 : ℝ), (321499 / 100000000 : ℝ), (355391 / 100000000 : ℝ), (96923 / 25000000 : ℝ), (417567 / 100000000 : ℝ), (444227 / 100000000 : ℝ), (466937 / 100000000 : ℝ), (19403 / 4000000 : ℝ)]

theorem endpoint_first : endpoints 0 = (0 : ℝ) := by norm_num [endpoints]
theorem endpoint_last : endpoints (Fin.last 32) = (1 / 2 : ℝ) := by norm_num [endpoints, Fin.last]

theorem endpoints_step (k : Fin 32) : endpoints k.castSucc ≤ endpoints k.succ := by
  fin_cases k
  · change (0 / 1 : ℝ) ≤ (1 / 64 : ℝ)
    norm_num
  · change (1 / 64 : ℝ) ≤ (1 / 32 : ℝ)
    norm_num
  · change (1 / 32 : ℝ) ≤ (3 / 64 : ℝ)
    norm_num
  · change (3 / 64 : ℝ) ≤ (1 / 16 : ℝ)
    norm_num
  · change (1 / 16 : ℝ) ≤ (5 / 64 : ℝ)
    norm_num
  · change (5 / 64 : ℝ) ≤ (3 / 32 : ℝ)
    norm_num
  · change (3 / 32 : ℝ) ≤ (7 / 64 : ℝ)
    norm_num
  · change (7 / 64 : ℝ) ≤ (1 / 8 : ℝ)
    norm_num
  · change (1 / 8 : ℝ) ≤ (9 / 64 : ℝ)
    norm_num
  · change (9 / 64 : ℝ) ≤ (5 / 32 : ℝ)
    norm_num
  · change (5 / 32 : ℝ) ≤ (11 / 64 : ℝ)
    norm_num
  · change (11 / 64 : ℝ) ≤ (3 / 16 : ℝ)
    norm_num
  · change (3 / 16 : ℝ) ≤ (13 / 64 : ℝ)
    norm_num
  · change (13 / 64 : ℝ) ≤ (7 / 32 : ℝ)
    norm_num
  · change (7 / 32 : ℝ) ≤ (15 / 64 : ℝ)
    norm_num
  · change (15 / 64 : ℝ) ≤ (1 / 4 : ℝ)
    norm_num
  · change (1 / 4 : ℝ) ≤ (17 / 64 : ℝ)
    norm_num
  · change (17 / 64 : ℝ) ≤ (9 / 32 : ℝ)
    norm_num
  · change (9 / 32 : ℝ) ≤ (19 / 64 : ℝ)
    norm_num
  · change (19 / 64 : ℝ) ≤ (5 / 16 : ℝ)
    norm_num
  · change (5 / 16 : ℝ) ≤ (21 / 64 : ℝ)
    norm_num
  · change (21 / 64 : ℝ) ≤ (11 / 32 : ℝ)
    norm_num
  · change (11 / 32 : ℝ) ≤ (23 / 64 : ℝ)
    norm_num
  · change (23 / 64 : ℝ) ≤ (3 / 8 : ℝ)
    norm_num
  · change (3 / 8 : ℝ) ≤ (25 / 64 : ℝ)
    norm_num
  · change (25 / 64 : ℝ) ≤ (13 / 32 : ℝ)
    norm_num
  · change (13 / 32 : ℝ) ≤ (27 / 64 : ℝ)
    norm_num
  · change (27 / 64 : ℝ) ≤ (7 / 16 : ℝ)
    norm_num
  · change (7 / 16 : ℝ) ≤ (29 / 64 : ℝ)
    norm_num
  · change (29 / 64 : ℝ) ≤ (15 / 32 : ℝ)
    norm_num
  · change (15 / 32 : ℝ) ≤ (31 / 64 : ℝ)
    norm_num
  · change (31 / 64 : ℝ) ≤ (1 / 2 : ℝ)
    norm_num

theorem cell_bounds (k : Fin 32) (x : ℝ)
    (hx : x ∈ Ioo (endpoints k.castSucc) (endpoints k.succ)) :
    density x ≤ cellBounds k := by
  fin_cases k
  · change density x ≤ (387741 / 100000000 : ℝ)
    change x ∈ Ioo (0 / 1 : ℝ) (1 / 64 : ℝ) at hx
    exact cell_042 x hx
  · change density x ≤ (16907 / 4000000 : ℝ)
    change x ∈ Ioo (1 / 64 : ℝ) (1 / 32 : ℝ) at hx
    exact cell_043 x hx
  · change density x ≤ (91037 / 20000000 : ℝ)
    change x ∈ Ioo (1 / 32 : ℝ) (3 / 64 : ℝ) at hx
    exact cell_044 x hx
  · change density x ≤ (7571 / 1562500 : ℝ)
    change x ∈ Ioo (3 / 64 : ℝ) (1 / 16 : ℝ) at hx
    exact cell_045 x hx
  · change density x ≤ (63757 / 12500000 : ℝ)
    change x ∈ Ioo (1 / 16 : ℝ) (5 / 64 : ℝ) at hx
    exact cell_046 x hx
  · change density x ≤ (531121 / 100000000 : ℝ)
    change x ∈ Ioo (5 / 64 : ℝ) (3 / 32 : ℝ) at hx
    exact cell_047 x hx
  · change density x ≤ (547237 / 100000000 : ℝ)
    change x ∈ Ioo (3 / 32 : ℝ) (7 / 64 : ℝ) at hx
    exact cell_048 x hx
  · change density x ≤ (558023 / 100000000 : ℝ)
    change x ∈ Ioo (7 / 64 : ℝ) (1 / 8 : ℝ) at hx
    exact cell_049 x hx
  · change density x ≤ (281629 / 50000000 : ℝ)
    change x ∈ Ioo (1 / 8 : ℝ) (9 / 64 : ℝ) at hx
    exact cell_050 x hx
  · change density x ≤ (562809 / 100000000 : ℝ)
    change x ∈ Ioo (9 / 64 : ℝ) (5 / 32 : ℝ) at hx
    exact cell_051 x hx
  · change density x ≤ (34797 / 6250000 : ℝ)
    change x ∈ Ioo (5 / 32 : ℝ) (11 / 64 : ℝ) at hx
    exact cell_052 x hx
  · change density x ≤ (27263 / 5000000 : ℝ)
    change x ∈ Ioo (11 / 64 : ℝ) (3 / 16 : ℝ) at hx
    exact cell_053 x hx
  · change density x ≤ (264331 / 50000000 : ℝ)
    change x ∈ Ioo (3 / 16 : ℝ) (13 / 64 : ℝ) at hx
    exact cell_054 x hx
  · change density x ≤ (253699 / 50000000 : ℝ)
    change x ∈ Ioo (13 / 64 : ℝ) (7 / 32 : ℝ) at hx
    exact cell_055 x hx
  · change density x ≤ (482037 / 100000000 : ℝ)
    change x ∈ Ioo (7 / 32 : ℝ) (15 / 64 : ℝ) at hx
    exact cell_056 x hx
  · change density x ≤ (90643 / 20000000 : ℝ)
    change x ∈ Ioo (15 / 64 : ℝ) (1 / 4 : ℝ) at hx
    exact cell_057 x hx
  · change density x ≤ (210817 / 50000000 : ℝ)
    change x ∈ Ioo (1 / 4 : ℝ) (17 / 64 : ℝ) at hx
    exact cell_058 x hx
  · change density x ≤ (388049 / 100000000 : ℝ)
    change x ∈ Ioo (17 / 64 : ℝ) (9 / 32 : ℝ) at hx
    exact cell_059 x hx
  · change density x ≤ (353201 / 100000000 : ℝ)
    change x ∈ Ioo (9 / 32 : ℝ) (19 / 64 : ℝ) at hx
    exact cell_060 x hx
  · change density x ≤ (317851 / 100000000 : ℝ)
    change x ∈ Ioo (19 / 64 : ℝ) (5 / 16 : ℝ) at hx
    exact cell_061 x hx
  · change density x ≤ (282711 / 100000000 : ℝ)
    change x ∈ Ioo (5 / 16 : ℝ) (21 / 64 : ℝ) at hx
    exact cell_062 x hx
  · change density x ≤ (24843 / 10000000 : ℝ)
    change x ∈ Ioo (21 / 64 : ℝ) (11 / 32 : ℝ) at hx
    exact cell_063 x hx
  · change density x ≤ (218381 / 100000000 : ℝ)
    change x ∈ Ioo (11 / 32 : ℝ) (23 / 64 : ℝ) at hx
    exact cell_064 x hx
  · change density x ≤ (126107 / 50000000 : ℝ)
    change x ∈ Ioo (23 / 64 : ℝ) (3 / 8 : ℝ) at hx
    exact cell_065 x hx
  · change density x ≤ (57367 / 20000000 : ℝ)
    change x ∈ Ioo (3 / 8 : ℝ) (25 / 64 : ℝ) at hx
    exact cell_066 x hx
  · change density x ≤ (321499 / 100000000 : ℝ)
    change x ∈ Ioo (25 / 64 : ℝ) (13 / 32 : ℝ) at hx
    exact cell_067 x hx
  · change density x ≤ (355391 / 100000000 : ℝ)
    change x ∈ Ioo (13 / 32 : ℝ) (27 / 64 : ℝ) at hx
    exact cell_068 x hx
  · change density x ≤ (96923 / 25000000 : ℝ)
    change x ∈ Ioo (27 / 64 : ℝ) (7 / 16 : ℝ) at hx
    exact cell_069 x hx
  · change density x ≤ (417567 / 100000000 : ℝ)
    change x ∈ Ioo (7 / 16 : ℝ) (29 / 64 : ℝ) at hx
    exact cell_070 x hx
  · change density x ≤ (444227 / 100000000 : ℝ)
    change x ∈ Ioo (29 / 64 : ℝ) (15 / 32 : ℝ) at hx
    exact cell_071 x hx
  · change density x ≤ (466937 / 100000000 : ℝ)
    change x ∈ Ioo (15 / 32 : ℝ) (31 / 64 : ℝ) at hx
    exact cell_072 x hx
  · change density x ≤ (19403 / 4000000 : ℝ)
    change x ∈ Ioo (31 / 64 : ℝ) (1 / 2 : ℝ) at hx
    exact cell_073 x hx

theorem cell_bound_sum :
    (∑ k : Fin 32, cellBounds k * (endpoints k.succ - endpoints k.castSucc)) =
      (13743667 / 6400000000 : ℝ) := by
  norm_num [endpoints, cellBounds, Fin.sum_univ_succ]

theorem density_integrable : Integrable density :=
  MasulloRH.DirectIntegrability.height_one_density_integrable

theorem compact_certificate :
    IntegrableOn density (Icc (0 : ℝ) (1 / 2 : ℝ)) ∧
    (∫ x : ℝ in Icc (0 : ℝ) (1 / 2 : ℝ), density x) ≤ (11 / 5000 : ℝ) := by
  have h := MasulloRH.EnergyCertificate.integral_le_fin_partition_sum
    density 32 endpoints cellBounds density_integrable endpoints_step cell_bounds
  rw [endpoint_first, endpoint_last,
    intervalIntegral.integral_of_le (show (0 : ℝ) ≤ (1 / 2 : ℝ) by norm_num),
    ← integral_Icc_eq_integral_Ioc, cell_bound_sum] at h
  refine ⟨density_integrable.integrableOn, h.trans ?_⟩
  norm_num

end MasulloRH.HeightOne
end

end N1ZeroHalfProof

open MeasureTheory

theorem solution :
    MeasureTheory.IntegrableOn (fun x : ℝ =>
      Real.exp (2 * (3 / 4 : ℝ) * x + 2 * (7 / 32 : ℝ) * |x|) *
      ‖MasulloRH.GaussianApproximation.residual 1
        (fun _ : Fin 1 => (73 / 50 : ℂ))
        (fun _ : Fin 1 => (3 / 4 : ℝ)) x‖ ^ 2) (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) ∧
    (∫ x : ℝ in Set.Icc (0 : ℝ) (1 / 2 : ℝ),
      Real.exp (2 * (3 / 4 : ℝ) * x + 2 * (7 / 32 : ℝ) * |x|) *
      ‖MasulloRH.GaussianApproximation.residual 1
        (fun _ : Fin 1 => (73 / 50 : ℂ))
        (fun _ : Fin 1 => (3 / 4 : ℝ)) x‖ ^ 2) ≤ (11 / 5000 : ℝ) := by
  have h := N1ZeroHalfProof.MasulloRH.HeightOne.compact_certificate
  constructor
  · convert! h.1 using 1
    funext x
    simp only [N1ZeroHalfProof.MasulloRH.HeightOne.density,
      MasulloRH.GaussianApproximation.residual, Fin.sum_univ_one,
      show (2 : ℝ) * (3 / 4) = 3 / 2 by norm_num,
      show (2 : ℝ) * (7 / 32) = 7 / 16 by norm_num]
  · simpa only [N1ZeroHalfProof.MasulloRH.HeightOne.density,
      MasulloRH.GaussianApproximation.residual, Fin.sum_univ_one,
      show (2 : ℝ) * (3 / 4) = 3 / 2 by norm_num,
      show (2 : ℝ) * (7 / 32) = 7 / 16 by norm_num] using h.2
