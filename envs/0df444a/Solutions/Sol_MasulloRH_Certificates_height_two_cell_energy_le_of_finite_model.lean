-- Prove2me | solution 1 for MasulloRH.Certificates.height_two_cell_energy_le_of_finite_model
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T20:25:34.936898+00:00
-- url     : https://prove2.me/submissions/ad44a157-1e6d-44eb-b76e-f52335ff0f02

import Mathlib
import Definitions.Def_MasulloRH_ThetaCertificate

import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Definitions.Def_MasulloRH_GaussianThetaTruncation
import Definitions.Def_MasulloRH_HeightTwoWitness
import Theorems.Thm_MasulloRH_theta_gaussian_truncation_error
import Theorems.Thm_MasulloRH_theta_reflection
import Theorems.Thm_MasulloRH_height_two_residual_exterior_bound

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

open scoped BigOperators
open _root_.MasulloRH.CertifiedExp _root_.MasulloRH.Certificates
open _root_.MasulloRH.HeightTwoScalar

open MeasureTheory Set
open _root_.MasulloRH _root_.MasulloRH.GaussianApproximation

namespace N5CellInterfaceHelpers

theorem gaussian_parameter_lower (x : ℝ) (hx : -1 ≤ x) :
    (1 / 3 : ℝ) ≤ Real.pi * (Real.exp x) ^ 2 := by
  have he : (1 / 3 : ℝ) ≤ Real.exp x := by
    have hrec : (1 / 3 : ℝ) ≤ (Real.exp 1)⁻¹ := by
      rw [← one_div (Real.exp 1)]
      apply (le_div_iff₀ (Real.exp_pos _)).2
      nlinarith [Real.exp_one_lt_three]
    exact hrec.trans (by simpa only [Real.exp_neg] using Real.exp_le_exp.mpr hx)
  have hs : (1 / 9 : ℝ) ≤ (Real.exp x) ^ 2 := by nlinarith
  have hp := Real.pi_gt_three.le
  nlinarith [mul_le_mul_of_nonneg_right hp (sq_nonneg (Real.exp x))]

theorem reflected_parameter_lower (x : ℝ) (hx : x ≤ -1) :
    (1 / 3 : ℝ) ≤ Real.pi * (Real.exp (-x - Real.log 4)) ^ 2 := by
  have he : (2 : ℝ) ≤ Real.exp (-x) := by
    have h := Real.add_one_le_exp (-x)
    linarith
  have hexp : Real.exp (-x - Real.log 4) = Real.exp (-x) / 4 := by
    rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  rw [hexp]
  have hs : (1 / 4 : ℝ) ≤ (Real.exp (-x) / 4) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right Real.pi_gt_three.le
    (sq_nonneg (Real.exp (-x) / 4))]

/-- A rational lower bound for the Gaussian parameter gives a simple common
tail allowance, uniform over every evaluation on either side of the cutoff. -/
theorem gaussian_tail_bound_le (a : ℝ) (ha : (1 / 3 : ℝ) ≤ a) (K : ℕ) :
    12 * Real.exp (-a * ((K : ℝ) + 1) ^ 2) /
        (1 - Real.exp (-a * (2 * (K : ℝ) + 3))) ≤
      24 * Real.exp (-((K : ℝ) + 1) ^ 2 / 3) := by
  have hk : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hap : 0 ≤ a := by linarith
  have ht : 1 ≤ a * (2 * (K : ℝ) + 3) := by
    nlinarith [mul_nonneg hap hk]
  have he : (2 : ℝ) ≤ Real.exp (a * (2 * (K : ℝ) + 3)) := by
    linarith [Real.add_one_le_exp (a * (2 * (K : ℝ) + 3))]
  have hneg : Real.exp (-a * (2 * (K : ℝ) + 3)) ≤ (1 / 2 : ℝ) := by
    rw [neg_mul, Real.exp_neg]
    rw [← one_div (Real.exp (a * (2 * (K : ℝ) + 3)))]
    exact (div_le_iff₀ (Real.exp_pos _)).2 (by nlinarith)
  have hd : (1 / 2 : ℝ) ≤ 1 - Real.exp (-a * (2 * (K : ℝ) + 3)) := by linarith
  have hn : Real.exp (-a * ((K : ℝ) + 1) ^ 2) ≤
      Real.exp (-((K : ℝ) + 1) ^ 2 / 3) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right ha (sq_nonneg ((K : ℝ) + 1))]
  apply (div_le_iff₀ (by linarith : 0 < 1 - Real.exp (-a * (2 * (K : ℝ) + 3)))).2
  have h := mul_le_mul_of_nonneg_left hd
    (show 0 ≤ 24 * Real.exp (-((K : ℝ) + 1) ^ 2 / 3) by positivity)
  nlinarith


end N5CellInterfaceHelpers

namespace N5CellCertificateRepairProof

/- Embedded checked source: Solutions/ThetaFinitePolynomial.lean -/
set_option autoImplicit false
open scoped BigOperators

namespace MasulloRH.CertifiedExp

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

open _root_.MasulloRH.GaussianApproximation

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

/- Embedded checked source: Solutions/MidpointDerivativeEnclosure.lean -/
/-!
# Midpoint derivative enclosures for an approximate residual

A differentiable finite model may approximate an actual residual without the
actual residual itself being differentiable. A midpoint value bound, a uniform
derivative bound, and a uniform approximation error give a bound on the whole
closed interval. The normed-space version includes real and complex residuals.

This is a generic analytic lemma. It does not certify any numerical theta data
or assert that an arbitrary bounded residual is integrable.
-/

set_option autoImplicit false

open Set

namespace MasulloRH.Certificates

/-- A midpoint enclosure transferred from a differentiable finite model to an
actual residual in a real normed space. Derivatives are only required within
the interval, so one-sided endpoint derivatives suffice. -/
theorem norm_le_midpoint_add_error_of_hasDerivWithinAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r g g' : ℝ → E} {u v A D epsilon : ℝ}
    (huv : u ≤ v) (_hA : 0 ≤ A) (hD : 0 ≤ D) (_hepsilon : 0 ≤ epsilon)
    (hg : ∀ t ∈ Icc u v, HasDerivWithinAt g (g' t) (Icc u v) t)
    (hderiv : ∀ t ∈ Icc u v, ‖g' t‖ ≤ D)
    (hmid : ‖g ((u + v) / 2)‖ ≤ A)
    (herror : ∀ t ∈ Icc u v, ‖r t - g t‖ ≤ epsilon) :
    ∀ x ∈ Icc u v, ‖r x‖ ≤ A + D * (v - u) / 2 + epsilon := by
  intro x hx
  have hm : (u + v) / 2 ∈ Icc u v := by
    constructor <;> linarith only [huv]
  have hdist : ‖x - (u + v) / 2‖ ≤ (v - u) / 2 := by
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> linarith only [hx.1, hx.2]
  have hvariation : ‖g x - g ((u + v) / 2)‖ ≤ D * ‖x - (u + v) / 2‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      hg hderiv (convex_Icc u v) hm hx
  have hr : ‖r x‖ ≤ ‖r x - g x‖ + ‖g x‖ := by
    simpa only [sub_add_cancel] using norm_add_le (r x - g x) (g x)
  have hgx : ‖g x‖ ≤ ‖g x - g ((u + v) / 2)‖ + ‖g ((u + v) / 2)‖ := by
    simpa only [sub_add_cancel] using
      norm_add_le (g x - g ((u + v) / 2)) (g ((u + v) / 2))
  calc
    ‖r x‖ ≤ ‖r x - g x‖ + (‖g x - g ((u + v) / 2)‖ + ‖g ((u + v) / 2)‖) :=
      hr.trans (add_le_add le_rfl hgx)
    _ ≤ epsilon + (D * ‖x - (u + v) / 2‖ + A) :=
      add_le_add (herror x hx) (add_le_add hvariation hmid)
    _ ≤ epsilon + (D * ((v - u) / 2) + A) :=
      add_le_add le_rfl
        (add_le_add (mul_le_mul_of_nonneg_left hdist hD) le_rfl)
    _ = A + D * (v - u) / 2 + epsilon := by ring

/-- Ordinary derivatives give the same enclosure. Only the finite model `g`
needs a derivative; the actual residual `r` enters through the error estimate. -/
theorem norm_le_midpoint_add_error_of_hasDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {r g g' : ℝ → E} {u v A D epsilon : ℝ}
    (huv : u ≤ v) (hA : 0 ≤ A) (hD : 0 ≤ D) (hepsilon : 0 ≤ epsilon)
    (hg : ∀ t ∈ Icc u v, HasDerivAt g (g' t) t)
    (hderiv : ∀ t ∈ Icc u v, ‖g' t‖ ≤ D)
    (hmid : ‖g ((u + v) / 2)‖ ≤ A)
    (herror : ∀ t ∈ Icc u v, ‖r t - g t‖ ≤ epsilon) :
    ∀ x ∈ Icc u v, ‖r x‖ ≤ A + D * (v - u) / 2 + epsilon :=
  norm_le_midpoint_add_error_of_hasDerivWithinAt huv hA hD hepsilon
    (fun t ht => (hg t ht).hasDerivWithinAt) hderiv hmid herror

/-- The real-valued absolute-value formulation of the midpoint enclosure. -/
theorem abs_le_midpoint_add_error_of_hasDerivAt
    {r g g' : ℝ → ℝ} {u v A D epsilon : ℝ}
    (huv : u ≤ v) (hA : 0 ≤ A) (hD : 0 ≤ D) (hepsilon : 0 ≤ epsilon)
    (hg : ∀ t ∈ Icc u v, HasDerivAt g (g' t) t)
    (hderiv : ∀ t ∈ Icc u v, |g' t| ≤ D)
    (hmid : |g ((u + v) / 2)| ≤ A)
    (herror : ∀ t ∈ Icc u v, |r t - g t| ≤ epsilon) :
    ∀ x ∈ Icc u v, |r x| ≤ A + D * (v - u) / 2 + epsilon := by
  simpa only [Real.norm_eq_abs] using
    (norm_le_midpoint_add_error_of_hasDerivAt huv hA hD hepsilon hg
      (by simpa only [Real.norm_eq_abs] using hderiv)
      (by simpa only [Real.norm_eq_abs] using hmid)
      (by simpa only [Real.norm_eq_abs] using herror))

end MasulloRH.Certificates

/- Embedded checked source: Solutions/ThetaFiniteModelDerivatives.lean -/
/-!
# Finite analytic models for theta midpoint certificates

Each cell chooses one analytic branch for each translate.  The choice is fixed
throughout the cell; no derivative of a piecewise function or of the infinite
theta series is used.  The branch-specific approximation bounds include the
cutoff `-1` on both sides, so adjacent closed cells are legitimate even though
the canonical finite reflected approximation chooses its direct branch there.

All numerical bounds remain explicit hypotheses of the final cell lemma.  Its
derivative and approximation hypotheses are reduced here to the finite models
and to the already proved Gaussian truncation and theta reflection theorems.
-/

set_option autoImplicit false
open scoped BigOperators
open Set _root_.MasulloRH.GaussianApproximation

namespace MasulloRH.CertifiedExp

/-- The logarithmic polynomial derivative `r * P'(r)`, written without division. -/
private theorem hasDerivAt_exp_pow {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasDerivAt f f' x) (n : ℕ) :
    HasDerivAt (fun t => (Real.exp (f t)) ^ n)
      ((n : ℝ) * (Real.exp (f x)) ^ n * f') x := by
  have h := (hf.const_mul (n : ℝ)).exp
  simp only [Real.exp_nat_mul] at h
  convert! h using 1 <;> ring

/-- Chain rule for a theta polynomial evaluated at an exponential. -/
theorem thetaPolynomial_exp_hasDerivAt {f : ℝ → ℝ} {f' x : ℝ}
    (hf : HasDerivAt f f' x) (K : ℕ) :
    HasDerivAt (fun t => thetaPolynomial K (Real.exp (f t)))
      (f' * thetaMomentPolynomial K (Real.exp (f x))) x := by
  have ht (n : ℕ) :
      HasDerivAt (fun t =>
        (Real.exp (f t)) ^ ((n + 1) ^ 2) -
          3 * (Real.exp (f t)) ^ (4 * (n + 1) ^ 2) +
          2 * (Real.exp (f t)) ^ (16 * (n + 1) ^ 2))
        (f' * ((((n + 1) ^ 2 : ℕ) : ℝ) * (Real.exp (f x)) ^ ((n + 1) ^ 2) -
          3 * ((4 * (n + 1) ^ 2 : ℕ) : ℝ) *
            (Real.exp (f x)) ^ (4 * (n + 1) ^ 2) +
          2 * ((16 * (n + 1) ^ 2 : ℕ) : ℝ) *
            (Real.exp (f x)) ^ (16 * (n + 1) ^ 2))) x := by
    convert! ((hasDerivAt_exp_pow hf ((n + 1) ^ 2)).sub
      ((hasDerivAt_exp_pow hf (4 * (n + 1) ^ 2)).const_mul 3)).add
      ((hasDerivAt_exp_pow hf (16 * (n + 1) ^ 2)).const_mul 2) using 1 <;> ring
  simpa only [thetaPolynomial, thetaMomentPolynomial, Finset.mul_sum] using
    (HasDerivAt.fun_sum (u := Finset.range K) (fun n _ => ht n))

end MasulloRH.CertifiedExp

namespace MasulloRH.Certificates
open MasulloRH.CertifiedExp

theorem thetaDirectModel_hasDerivAt (K : ℕ) (x : ℝ) :
    HasDerivAt (thetaDirectModel K) (thetaDirectDerivative K x) x := by
  have hf : HasDerivAt (fun t : ℝ => -Real.pi * Real.exp (2 * t))
      (-2 * (Real.pi * Real.exp (2 * x))) x := by
    convert! (((hasDerivAt_id' x).const_mul 2).exp.const_mul (-Real.pi)) using 1 <;>
      ring
  convert! (thetaPolynomial_exp_hasDerivAt hf K).const_mul 2 using 1 <;>
    simp only [thetaDirectModel, thetaDirectDerivative] <;> ring

theorem thetaReflectedModel_hasDerivAt (K : ℕ) (x : ℝ) :
    HasDerivAt (thetaReflectedModel K) (thetaReflectedDerivative K x) x := by
  have hf : HasDerivAt (fun t : ℝ => -(Real.pi / 16) * Real.exp (-2 * t))
      (2 * ((Real.pi / 16) * Real.exp (-2 * x))) x := by
    convert! (((hasDerivAt_id' x).const_mul (-2)).exp.const_mul (-(Real.pi / 16)))
      using 1 <;> ring
  convert! ((hasDerivAt_id' x).neg.exp).mul
    (thetaPolynomial_exp_hasDerivAt hf K) using 1 <;>
    simp only [thetaReflectedModel, thetaReflectedDerivative, Pi.neg_apply] <;> ring

/-- `true` chooses the reflected analytic branch, `false` the direct branch. -/
theorem thetaBranchModel_hasDerivAt (K : ℕ) (reflected : Bool) (x : ℝ) :
    HasDerivAt (thetaBranchModel K reflected) (thetaBranchDerivative K reflected x) x := by
  cases reflected
  · simpa only [thetaBranchModel, thetaBranchDerivative, Bool.false_eq_true, ↓reduceIte] using!
      thetaDirectModel_hasDerivAt K x
  · simpa only [thetaBranchModel, thetaBranchDerivative, ↓reduceIte] using!
      thetaReflectedModel_hasDerivAt K x

theorem pulseModel_hasDerivAt (T x : ℝ) :
    HasDerivAt (pulseModel T) (pulseDerivative T x) x := by
  have hf : HasDerivAt (fun t : ℝ => -(T + 1) ^ 2 * t ^ 2)
      (-2 * (T + 1) ^ 2 * x) x := by
    convert! ((hasDerivAt_id' x).pow 2).const_mul (-(T + 1) ^ 2) using 1 <;>
      simp only [Nat.cast_ofNat, pow_one, mul_one] <;> ring
  convert! hf.exp.const_mul ((T + 1) / Real.sqrt Real.pi) using 1 <;>
    simp only [pulseModel, pulseDerivative] <;> ring

theorem pulse_eq_model (T x : ℝ) : pulse T x = (pulseModel T x : ℂ) := by
  simp only [pulse, pulseModel, Complex.ofReal_mul, Complex.ofReal_exp,
    Complex.ofReal_neg, Complex.ofReal_pow]
  congr 2
  ring

theorem finiteResidualModel_hasDerivAt {m : ℕ} (K : ℕ) (T : ℝ)
    (a y : Fin m → ℝ) (branch : Fin m → Bool) (x : ℝ) :
    HasDerivAt (finiteResidualModel K T a y branch)
      (finiteResidualDerivative K T a y branch x) x := by
  have ht (i : Fin m) :
      HasDerivAt (fun t => a i * thetaBranchModel K (branch i) (t - y i))
        (a i * thetaBranchDerivative K (branch i) (x - y i)) x := by
    simpa only [mul_one, Function.comp_apply, id_eq] using!
      ((thetaBranchModel_hasDerivAt K (branch i) (x - y i)).comp x
        ((hasDerivAt_id' x).sub_const (y i))).const_mul (a i)
  exact (pulseModel_hasDerivAt T x).sub (HasDerivAt.fun_sum (fun i _ => ht i))

theorem thetaTruncationFactor_nonneg (K : ℕ) : 0 ≤ thetaTruncationFactor K := by
  unfold thetaTruncationFactor
  positivity

theorem thetaPartial_error_of_parameter (K : ℕ) (x : ℝ)
    (hx : (1 / 3 : ℝ) ≤ Real.pi * (Real.exp x) ^ 2) :
    ‖theta x - thetaPartial K x‖ ≤ thetaTruncationFactor K := by
  have h := _root_.MasulloRH.theta_gaussian_truncation_error x K
  change ‖theta x - thetaPartial K x‖ ≤ _ at h
  have hB := _root_.N5CellInterfaceHelpers.gaussian_tail_bound_le
    (Real.pi * (Real.exp x) ^ 2) hx K
  have hn (t : ℝ) : -(Real.pi * (Real.exp x) ^ 2) * t =
      -Real.pi * (Real.exp x) ^ 2 * t := by ring
  simp only [hn] at hB
  exact h.trans hB

/-- The reflected analytic model equals a scaled finite Gaussian sum at every
real argument, including the cutoff. -/
theorem thetaReflectedModel_eq_scaled_partial (K : ℕ) (x : ℝ) :
    (thetaReflectedModel K x : ℂ) =
      ((Real.exp (-x) / 2 : ℝ) : ℂ) * thetaPartial K (-x - Real.log 4) := by
  rw [thetaPartial_eq_polynomial, ← Complex.ofReal_mul]
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
  unfold thetaReflectedModel
  ring

theorem thetaDirectModel_error (K : ℕ) (x : ℝ) (hx : -1 ≤ x) :
    ‖theta x - (thetaDirectModel K x : ℂ)‖ ≤ thetaTruncationFactor K := by
  have h := thetaPartial_error_of_parameter K x
    (_root_.N5CellInterfaceHelpers.gaussian_parameter_lower x hx)
  simpa only [thetaPartial_eq_polynomial, thetaDirectModel] using h

theorem thetaReflectedModel_error (K : ℕ) (x : ℝ) (hx : x ≤ -1) :
    ‖theta x - (thetaReflectedModel K x : ℂ)‖ ≤
      thetaTruncationFactor K * (Real.exp (-x) / 2) := by
  rw [thetaReflectedModel_eq_scaled_partial, _root_.MasulloRH.theta_reflection x,
    ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ Real.exp (-x) / 2)]
  have h := thetaPartial_error_of_parameter K (-x - Real.log 4)
    (_root_.N5CellInterfaceHelpers.reflected_parameter_lower x hx)
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (mul_comm _ _)

theorem thetaBranchModel_error (K : ℕ) (reflected : Bool) (x : ℝ)
    (hx : thetaBranchValid reflected x) :
    ‖theta x - (thetaBranchModel K reflected x : ℂ)‖ ≤
      thetaTruncationFactor K * (1 + Real.exp (-x) / 2) := by
  cases reflected
  · simp only [thetaBranchModel, thetaBranchValid, Bool.false_eq_true, ↓reduceIte] at *
    exact (thetaDirectModel_error K x hx).trans
      (le_mul_of_one_le_right (thetaTruncationFactor_nonneg K) (by linarith [Real.exp_nonneg (-x)]))
  · simp only [thetaBranchModel, thetaBranchValid, ↓reduceIte] at *
    exact (thetaReflectedModel_error K x hx).trans
      (mul_le_mul_of_nonneg_left (by linarith) (thetaTruncationFactor_nonneg K))

/-- A monotone error budget for all points to the right of `left`. -/
theorem finiteResidualModel_error {m : ℕ} (K : ℕ) (T : ℝ)
    (a y : Fin m → ℝ) (branch : Fin m → Bool) (left x : ℝ)
    (hleft : left ≤ x) (hbranch : ∀ i, thetaBranchValid (branch i) (x - y i)) :
    ‖residual T (fun i => (a i : ℂ)) y x -
      (finiteResidualModel K T a y branch x : ℂ)‖ ≤
      finiteResidualErrorBudget K a y left := by
  have heq : residual T (fun i => (a i : ℂ)) y x -
      (finiteResidualModel K T a y branch x : ℂ) =
      -(∑ i, (a i : ℂ) *
        (theta (x - y i) - (thetaBranchModel K (branch i) (x - y i) : ℂ))) := by
    simp only [_root_.MasulloRH.GaussianApproximation.residual, pulse_eq_model, finiteResidualModel, Complex.ofReal_sub,
      Complex.ofReal_sum, Complex.ofReal_mul, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [heq, norm_neg]
  calc
    _ ≤ ∑ i, ‖(a i : ℂ) *
        (theta (x - y i) - (thetaBranchModel K (branch i) (x - y i) : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, |a i| *
        (thetaTruncationFactor K * (1 + Real.exp (-(x - y i)) / 2)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (thetaBranchModel_error K (branch i) (x - y i) (hbranch i)) (abs_nonneg _)
    _ ≤ ∑ i, |a i| *
        (thetaTruncationFactor K * (1 + Real.exp (-(left - y i)) / 2)) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (thetaTruncationFactor_nonneg K)
      have h := Real.exp_le_exp.mpr (show -(x - y i) ≤ -(left - y i) by linarith)
      linarith
    _ = finiteResidualErrorBudget K a y left := by
      unfold finiteResidualErrorBudget
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem thetaBranchValid_on_Icc {u v y : ℝ} (reflected : Bool)
    (h : if reflected then v - y ≤ -1 else -1 ≤ u - y) :
    ∀ x ∈ Icc u v, thetaBranchValid reflected (x - y) := by
  intro x hx
  cases reflected <;> simp only [thetaBranchValid, Bool.false_eq_true, ↓reduceIte] at * <;>
    linarith [hx.1, hx.2]

/-- The distance-sensitive form retains the linear variation from the midpoint.
Its square can be integrated exactly to obtain a tighter cell certificate than
using the maximum distance everywhere in the cell. -/
theorem norm_residual_le_midpoint_distance_of_finite_model {m : ℕ}
    (K : ℕ) (T : ℝ) (a y : Fin m → ℝ) (branch : Fin m → Bool)
    {u v A D epsilon : ℝ}
    (huv : u ≤ v) (_hA : 0 ≤ A) (_hD : 0 ≤ D) (_hepsilon : 0 ≤ epsilon)
    (hbranch : ∀ i, if branch i then v - y i ≤ -1 else -1 ≤ u - y i)
    (hderiv : ∀ x ∈ Icc u v, |finiteResidualDerivative K T a y branch x| ≤ D)
    (hmid : |finiteResidualModel K T a y branch ((u + v) / 2)| ≤ A)
    (herror : finiteResidualErrorBudget K a y u ≤ epsilon) :
    ∀ x ∈ Icc u v, ‖residual T (fun i => (a i : ℂ)) y x‖ ≤
      A + epsilon + D * |x - (u + v) / 2| := by
  intro x hx
  have hm : (u + v) / 2 ∈ Icc u v := by
    constructor <;> linarith only [huv]
  have hv :
      |finiteResidualModel K T a y branch x -
        finiteResidualModel K T a y branch ((u + v) / 2)| ≤
      D * |x - (u + v) / 2| := by
    simpa only [Real.norm_eq_abs] using
      (Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun t (_ht : t ∈ Icc u v) =>
          (finiteResidualModel_hasDerivAt K T a y branch t).hasDerivWithinAt)
        (fun t ht => (by simpa only [Real.norm_eq_abs] using hderiv t ht))
        (convex_Icc u v) hm hx)
  have hgx : |finiteResidualModel K T a y branch x| ≤
      D * |x - (u + v) / 2| + A := by
    calc
      _ = |(finiteResidualModel K T a y branch x -
          finiteResidualModel K T a y branch ((u + v) / 2)) +
          finiteResidualModel K T a y branch ((u + v) / 2)| := by rw [sub_add_cancel]
      _ ≤ |finiteResidualModel K T a y branch x -
          finiteResidualModel K T a y branch ((u + v) / 2)| +
          |finiteResidualModel K T a y branch ((u + v) / 2)| := abs_add_le _ _
      _ ≤ _ := add_le_add hv hmid
  have he := (finiteResidualModel_error K T a y branch u x hx.1
    (fun i => thetaBranchValid_on_Icc (branch i) (hbranch i) x hx)).trans herror
  have hr : ‖residual T (fun i => (a i : ℂ)) y x‖ ≤
      ‖residual T (fun i => (a i : ℂ)) y x -
        (finiteResidualModel K T a y branch x : ℂ)‖ +
        |finiteResidualModel K T a y branch x| := by
    simpa only [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs] using
      (norm_add_le
        (residual T (fun i => (a i : ℂ)) y x -
          (finiteResidualModel K T a y branch x : ℂ))
        (finiteResidualModel K T a y branch x : ℂ))
  calc
    _ ≤ epsilon + (D * |x - (u + v) / 2| + A) := hr.trans (add_le_add he hgx)
    _ = _ := by ring

/-- An actual-residual cell enclosure. The analytic branch derivatives and
truncation bridge are proved above; applications supply only finite scalar
enclosures and rational endpoint comparisons. -/
theorem norm_residual_le_midpoint_of_finite_model {m : ℕ}
    (K : ℕ) (T : ℝ) (a y : Fin m → ℝ) (branch : Fin m → Bool)
    {u v A D epsilon : ℝ}
    (huv : u ≤ v) (hA : 0 ≤ A) (hD : 0 ≤ D) (hepsilon : 0 ≤ epsilon)
    (hbranch : ∀ i, if branch i then v - y i ≤ -1 else -1 ≤ u - y i)
    (hderiv : ∀ x ∈ Icc u v, |finiteResidualDerivative K T a y branch x| ≤ D)
    (hmid : |finiteResidualModel K T a y branch ((u + v) / 2)| ≤ A)
    (herror : finiteResidualErrorBudget K a y u ≤ epsilon) :
    ∀ x ∈ Icc u v, ‖residual T (fun i => (a i : ℂ)) y x‖ ≤
      A + D * (v - u) / 2 + epsilon := by
  apply norm_le_midpoint_add_error_of_hasDerivAt
    (g := fun x => (finiteResidualModel K T a y branch x : ℂ))
    (g' := fun x => (finiteResidualDerivative K T a y branch x : ℂ))
    huv hA hD hepsilon
  · intro x _
    exact (finiteResidualModel_hasDerivAt K T a y branch x).ofReal_comp
  · simpa only [Complex.norm_real, Real.norm_eq_abs] using hderiv
  · simpa only [Complex.norm_real, Real.norm_eq_abs] using hmid
  · intro x hx
    exact (finiteResidualModel_error K T a y branch u x hx.1
      (fun i => thetaBranchValid_on_Icc (branch i) (hbranch i) x hx)).trans herror

end MasulloRH.Certificates

/- Embedded checked source: Solutions/MidpointEnergyIntegral.lean -/
set_option autoImplicit false

open MeasureTheory Set

namespace MasulloRH.Certificates

private theorem integral_affine_sq (a b p q : ℝ) :
    (∫ x : ℝ in a..b, (p + q*x)^2) =
      p^2*(b-a) + p*q*(b^2-a^2) + q^2*(b^3-a^3)/3 := by
  have h0 : IntervalIntegrable (fun _ : ℝ => p^2) volume a b :=
    continuous_const.intervalIntegrable a b
  have h1 : IntervalIntegrable (fun x : ℝ => (2*p*q)*x) volume a b :=
    (continuous_const.mul continuous_id).intervalIntegrable a b
  have h2 : IntervalIntegrable (fun x : ℝ => q^2*x^2) volume a b :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable a b
  calc
    _ = ∫ x : ℝ in a..b, (p^2 + (2*p*q)*x) + q^2*x^2 := by
      apply intervalIntegral.integral_congr
      intro x hx
      ring
    _ = _ := by
      rw [intervalIntegral.integral_add (h0.add h1) h2,
        intervalIntegral.integral_add h0 h1,
        intervalIntegral.integral_const,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        integral_id, integral_pow]
      norm_num
      ring

/-- The exact integral of the square of a cone centered at the interval midpoint. -/
theorem integral_midpoint_cone_sq (u v A D : ℝ) (huv : u ≤ v) :
    (∫ x : ℝ in Icc u v, (A+D*|x-(u+v)/2|)^2) =
      (v-u)*A^2 + (v-u)^2*A*D/2 + (v-u)^3*D^2/12 := by
  let m : ℝ := (u+v)/2
  have hum : u ≤ m := by dsimp [m]; linarith
  have hmv : m ≤ v := by dsimp [m]; linarith
  have hc : Continuous (fun x : ℝ => (A+D*|x-m|)^2) := by fun_prop
  have hl : (∫ x : ℝ in u..m, (A+D*|x-m|)^2) =
      (A+D*m)^2*(m-u) + (A+D*m)*(-D)*(m^2-u^2) +
        (-D)^2*(m^3-u^3)/3 := by
    calc
      _ = ∫ x : ℝ in u..m, ((A+D*m)+(-D)*x)^2 := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hum] at hx
        dsimp only
        rw [abs_of_nonpos (sub_nonpos.mpr hx.2)]
        ring
      _ = _ := integral_affine_sq u m (A+D*m) (-D)
  have hr : (∫ x : ℝ in m..v, (A+D*|x-m|)^2) =
      (A-D*m)^2*(v-m) + (A-D*m)*D*(v^2-m^2) +
        D^2*(v^3-m^3)/3 := by
    calc
      _ = ∫ x : ℝ in m..v, ((A-D*m)+D*x)^2 := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [uIcc_of_le hmv] at hx
        dsimp only
        rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
        ring
      _ = _ := integral_affine_sq m v (A-D*m) D
  change (∫ x : ℝ in Icc u v, (A+D*|x-m|)^2) = _
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le huv,
    ← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable u m) (hc.intervalIntegrable m v), hl, hr]
  dsimp [m]
  ring

/-- Integrate a pointwise midpoint/derivative envelope instead of multiplying
its maximum by the interval length. Integrability of the actual density is an
explicit premise and must be proved by the caller. -/
theorem weighted_energy_le_integrated_midpoint_envelope
    (r : ℝ → ℂ) (w : ℝ → ℝ) (u v A D epsilon W : ℝ)
    (huv : u ≤ v) (hW : 0 ≤ W)
    (hI : IntegrableOn (fun x => w x * ‖r x‖^2) (Icc u v))
    (hw : ∀ x ∈ Icc u v, w x ≤ W)
    (hr : ∀ x ∈ Icc u v,
      ‖r x‖ ≤ A + epsilon + D*|x-(u+v)/2|) :
    (∫ x : ℝ in Icc u v, w x * ‖r x‖^2) ≤
      W*((v-u)*(A+epsilon)^2 +
        (v-u)^2*(A+epsilon)*D/2 + (v-u)^3*D^2/12) := by
  have hc : Continuous (fun x : ℝ =>
      W*(A+epsilon+D*|x-(u+v)/2|)^2) := by fun_prop
  have henv : IntegrableOn (fun x : ℝ =>
      W*(A+epsilon+D*|x-(u+v)/2|)^2) (Icc u v) :=
    hc.continuousOn.integrableOn_Icc
  calc
    _ ≤ ∫ x : ℝ in Icc u v, W*(A+epsilon+D*|x-(u+v)/2|)^2 := by
      apply setIntegral_mono_on hI henv measurableSet_Icc
      intro x hx
      exact mul_le_mul (hw x hx)
        (pow_le_pow_left₀ (norm_nonneg _) (hr x hx) 2) (sq_nonneg _) hW
    _ = _ := by
      rw [integral_const_mul, integral_midpoint_cone_sq u v (A+epsilon) D huv]

end MasulloRH.Certificates

/- Embedded checked source: Solutions/ThetaFiniteModelCellEnergy.lean -/
/-!
# Actual residual energy on one finite-model cell

The generic theorem combines the proved finite-model derivative/truncation
bridge with exact integration of its midpoint envelope.  Integrability of the
actual weighted residual density is an explicit premise.  The height-two
specialization supplies that premise from the proved actual-residual tail
theorem for the canonical eleven-term witness.

The remaining cell hypotheses are numerical enclosures and endpoint branch
checks.  This file does not assert them for any unverified numerical table.
-/

set_option autoImplicit false
open MeasureTheory Set
open _root_.MasulloRH.GaussianApproximation

namespace MasulloRH.Certificates

/-- A cell-energy bound for the actual canonical residual, obtained by
integrating the square of its distance-sensitive midpoint enclosure. -/
theorem residual_cell_energy_le_of_finite_model {m : ℕ}
    (K : ℕ) (T c b : ℝ) (a y : Fin m → ℝ) (branch : Fin m → Bool)
    {u v A D epsilon W : ℝ}
    (huv : u ≤ v) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hepsilon : 0 ≤ epsilon) (hW : 0 ≤ W)
    (hI : IntegrableOn (fun x : ℝ =>
      Real.exp (2*c*x+2*b*|x|) *
        ‖residual T (fun i => (a i : ℂ)) y x‖^2) (Icc u v))
    (hbranch : ∀ i, if branch i then v - y i ≤ -1 else -1 ≤ u - y i)
    (hderiv : ∀ x ∈ Icc u v, |finiteResidualDerivative K T a y branch x| ≤ D)
    (hmid : |finiteResidualModel K T a y branch ((u + v) / 2)| ≤ A)
    (herror : finiteResidualErrorBudget K a y u ≤ epsilon)
    (hweight : ∀ x ∈ Icc u v, Real.exp (2*c*x+2*b*|x|) ≤ W) :
    (∫ x : ℝ in Icc u v, Real.exp (2*c*x+2*b*|x|) *
      ‖residual T (fun i => (a i : ℂ)) y x‖^2) ≤
      W*((v-u)*(A+epsilon)^2 +
        (v-u)^2*(A+epsilon)*D/2 + (v-u)^3*D^2/12) := by
  exact weighted_energy_le_integrated_midpoint_envelope
    (residual T (fun i => (a i : ℂ)) y)
    (fun x => Real.exp (2*c*x+2*b*|x|)) u v A D epsilon W
    huv hW hI hweight
    (norm_residual_le_midpoint_distance_of_finite_model
      K T a y branch huv hA hD hepsilon hbranch hderiv hmid herror)

/-- The canonical height-two witness is already known to have an integrable
weighted square.  A cell certificate therefore needs only the finite scalar
enclosures and branch comparisons, with no integrability assumption. -/
theorem height_two_cell_energy_le_of_finite_model
    (K : ℕ) (branch : Fin 11 → Bool)
    {u v A D epsilon W : ℝ}
    (huv : u ≤ v) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hepsilon : 0 ≤ epsilon) (hW : 0 ≤ W)
    (hbranch : ∀ i, if branch i then v - HeightTwoWitness.shifts i ≤ -1
      else -1 ≤ u - HeightTwoWitness.shifts i)
    (hderiv : ∀ x ∈ Icc u v,
      |finiteResidualDerivative K 2 (fun i => (HeightTwoWitness.coeffsQ i : ℝ))
        HeightTwoWitness.shifts branch x| ≤ D)
    (hmid :
      |finiteResidualModel K 2 (fun i => (HeightTwoWitness.coeffsQ i : ℝ))
        HeightTwoWitness.shifts branch ((u + v) / 2)| ≤ A)
    (herror : finiteResidualErrorBudget K (fun i => (HeightTwoWitness.coeffsQ i : ℝ))
      HeightTwoWitness.shifts u ≤ epsilon)
    (hweight : ∀ x ∈ Icc u v,
      Real.exp (2*(3/4)*x+2*(11/48)*|x|) ≤ W) :
    (∫ x : ℝ in Icc u v, Real.exp (2*(3/4)*x+2*(11/48)*|x|) *
      ‖residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts x‖^2) ≤
      W*((v-u)*(A+epsilon)^2 +
        (v-u)^2*(A+epsilon)*D/2 + (v-u)^3*D^2/12) := by
  have hcoeff : (fun i : Fin 11 => ((HeightTwoWitness.coeffsQ i : ℝ) : ℂ)) =
      HeightTwoWitness.coeffs := by
    funext i
    simp only [HeightTwoWitness.coeffs, Complex.ofReal_ratCast]
  have hI : IntegrableOn (fun x : ℝ =>
      Real.exp (2*(3/4)*x+2*(11/48)*|x|) *
        ‖residual 2 (fun i => ((HeightTwoWitness.coeffsQ i : ℝ) : ℂ))
          HeightTwoWitness.shifts x‖^2) (Icc u v) := by
    rw [hcoeff]
    exact (_root_.MasulloRH.height_two_residual_exterior_bound.1).integrableOn
  have h := residual_cell_energy_le_of_finite_model K 2 (3/4) (11/48)
    (fun i => (HeightTwoWitness.coeffsQ i : ℝ)) HeightTwoWitness.shifts branch
    huv hA hD hepsilon hW hI hbranch hderiv hmid herror hweight
  simpa only [hcoeff] using h

end MasulloRH.Certificates

end N5CellCertificateRepairProof

theorem solution
    (K : ℕ) (branch : Fin 11 → Bool)
    {u v A D epsilon W : ℝ}
    (huv : u ≤ v) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hepsilon : 0 ≤ epsilon) (hW : 0 ≤ W)
    (hbranch : ∀ i, if branch i then v - HeightTwoWitness.shifts i ≤ -1
      else -1 ≤ u - HeightTwoWitness.shifts i)
    (hderiv : ∀ x ∈ Icc u v,
      |finiteResidualDerivative K 2 (fun i => (HeightTwoWitness.coeffsQ i : ℝ))
        HeightTwoWitness.shifts branch x| ≤ D)
    (hmid :
      |finiteResidualModel K 2 (fun i => (HeightTwoWitness.coeffsQ i : ℝ))
        HeightTwoWitness.shifts branch ((u + v) / 2)| ≤ A)
    (herror : finiteResidualErrorBudget K (fun i => (HeightTwoWitness.coeffsQ i : ℝ))
      HeightTwoWitness.shifts u ≤ epsilon)
    (hweight : ∀ x ∈ Icc u v,
      Real.exp (2*(3/4)*x+2*(11/48)*|x|) ≤ W) :
    (∫ x : ℝ in Icc u v, Real.exp (2*(3/4)*x+2*(11/48)*|x|) *
      ‖residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts x‖^2) ≤
      W*((v-u)*(A+epsilon)^2 +
        (v-u)^2*(A+epsilon)*D/2 + (v-u)^3*D^2/12) := by
  exact N5CellCertificateRepairProof.MasulloRH.Certificates.height_two_cell_energy_le_of_finite_model
    K branch huv hA hD hepsilon hW hbranch hderiv hmid herror hweight

#print axioms solution
