-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Twist.schwartz_logDeriv_linear_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:42:51.293101+00:00
-- url     : https://prove2.me/submissions/ae64484b-de8f-4e58-9763-c79d66750ced

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SchwartzLogDerivLinearGaussian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Twist
namespace GlobalTheory.CompanionTheory.Twist
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f₀ : SchwartzMap V ℂ) (m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ)
    (hm : ∀ a y, fderiv ℝ f₀ y a = m a y * f₀ y) (y : V) :
    f₀ y = f₀ 0 * Complex.exp (m y y / 2) := by
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f₀ (s • y)) ((t : ℂ) * m y y * f₀ (t • y)) t := by
    intro t
    have h1 : HasFDerivAt f₀ (fderiv ℝ f₀ (t • y)) (t • y) := f₀.differentiableAt.hasFDerivAt
    have h2 : HasDerivAt (fun s : ℝ => s • y) y t := by
      simpa using (hasDerivAt_id t).smul_const y
    have h3 : HasDerivAt (fun s : ℝ => f₀ (s • y)) (fderiv ℝ f₀ (t • y) y) t :=
      h1.comp_hasDerivAt t h2
    rw [hm, map_smul, Complex.real_smul] at h3
    exact h3
  have hE : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-((s : ℂ) ^ 2 * m y y / 2)))
      (Complex.exp (-((t : ℂ) ^ 2 * m y y / 2)) * (-((t : ℂ) * m y y))) t := by
    intro t
    have h5 : HasDerivAt (fun z : ℂ => -(z ^ 2 * m y y / 2)) (-((t : ℂ) * m y y)) (t : ℂ) := by
      have h6 := (((hasDerivAt_pow 2 (t : ℂ)).mul_const (m y y)).div_const 2).neg
      refine h6.congr_deriv ?_
      rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
      push_cast
      ring
    exact h5.cexp.comp_ofReal
  have hH : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => f₀ (s • y) * Complex.exp (-((s : ℂ) ^ 2 * m y y / 2))) 0 t := by
    intro t
    refine ((hg t).mul (hE t)).congr_deriv ?_
    ring
  have h10 := is_const_of_deriv_eq_zero (fun t => (hH t).differentiableAt) (fun t => (hH t).deriv) 1 0
  simp only [one_smul, zero_smul, Complex.ofReal_one, Complex.ofReal_zero, one_pow, one_mul,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, zero_div, neg_zero,
    Complex.exp_zero, mul_one] at h10
  calc f₀ y = f₀ y * Complex.exp (-(m y y / 2)) * Complex.exp (m y y / 2) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = f₀ 0 * Complex.exp (m y y / 2) := by rw [h10]
end GlobalTheory.CompanionTheory.Twist
