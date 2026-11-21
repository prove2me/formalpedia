-- Prove2me | solution 1 for MasulloRH.sheared_lift_pairing_jet_integral
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-21T04:34:05.338791+00:00
-- url     : https://prove2.me/submissions/66133a05-9ab4-45d2-87f1-0e3545cce468

import Definitions.Def_MasulloRH_WeightedStripJetSpace

open MeasureTheory MasulloRH

theorem solution (b p h : ℝ) (z : ℂ) (m : ℕ)
    (f g η : Lp ℂ 2 (volume : Measure ℝ))
    (hη : (η : ℝ → ℂ) =ᵐ[volume] fun x : ℝ =>
      (rationalStripWeight b p x : ℂ) * (x : ℂ)^m * Complex.exp ((z-1/2)*x)) :
    (∫ q : ℝ × ℝ,
      inner ℂ (f (q.1+h)) (g (q.1+h)) *
        inner ℂ (η (q.2+h)) (η (q.2+h)) ∂volume.prod volume) =
      inner ℂ f g * ∫ x : ℝ,
        ((|rationalStripWeight b p x| * |x|^m * Real.exp ((z.re-1/2)*x) : ℝ) : ℂ)^2 := by
  rw [integral_prod_mul (fun x : ℝ => inner ℂ (f (x+h)) (g (x+h)))
    (fun y : ℝ => inner ℂ (η (y+h)) (η (y+h)))]
  rw [integral_add_right_eq_self (fun x : ℝ => inner ℂ (f x) (g x)) h,
      integral_add_right_eq_self (fun y : ℝ => inner ℂ (η y) (η y)) h,
      ← L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [hη] with x hx
  rw [inner_self_eq_norm_sq_to_K, hx]
  simp [Complex.norm_exp, Complex.mul_re, Complex.sub_re, Real.norm_eq_abs]
