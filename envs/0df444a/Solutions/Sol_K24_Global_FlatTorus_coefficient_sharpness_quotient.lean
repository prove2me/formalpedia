-- Prove2me | solution 1 for K24.Global.FlatTorus.coefficient_sharpness_quotient
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T18:37:34.073416+00:00
-- url     : https://prove2.me/submissions/c4e38654-68c5-408b-bae3-171c597d42ae

import Definitions.Def_K24GlobalStatement

/-!
A self-contained checked solution of the coefficient two-point quotient from
K24 §5.6. This theorem concerns `expectedDefectCoefficients`; equality with the
actual geometric defect is a separate obligation in the parent K24 theorem.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff NNReal ENNReal Matrix.Norms.Elementwise

namespace K24.Global.FlatTorus.CoefficientSharpness

theorem liftedOscillation_deriv (alpha : ℝ) (n : ℕ) (r : ℝ) :
    deriv (liftedOscillation alpha n) r =
      amplitude alpha n * Real.cos ((n : ℝ) * r) * (n : ℝ) := by
  change deriv (fun s => amplitude alpha n * Real.sin ((n : ℝ) * s)) r = _
  have h := (((hasDerivAt_id r).const_mul (n : ℝ)).sin).const_mul (amplitude alpha n)
  simpa only [liftedOscillation, id_eq, mul_one, mul_assoc] using h.deriv

theorem liftedOscillation_deriv_two (alpha : ℝ) (n : ℕ) (r : ℝ) :
    deriv (deriv (liftedOscillation alpha n)) r =
      -(amplitude alpha n) * (n : ℝ)^2 * Real.sin ((n : ℝ) * r) := by
  have hf : deriv (liftedOscillation alpha n) = fun s =>
      amplitude alpha n * Real.cos ((n : ℝ) * s) * (n : ℝ) := by
    funext s
    exact liftedOscillation_deriv alpha n s
  rw [hf]
  have h := ((((hasDerivAt_id r).const_mul (n : ℝ)).cos).const_mul
    (amplitude alpha n)).mul_const (n : ℝ)
  convert h.deriv using 1 <;> simp only [id_eq, mul_one]; ring

theorem expectedDefect_zero_formula (alpha : ℝ) (n : ℕ) (x : FourSpace) :
    expectedDefectCoefficients alpha n x 0 =
      amplitude alpha n * (1 + (n : ℝ)^2 / 2) * Real.cos (x 1) *
        Real.sin ((n : ℝ) * x 0) := by
  simp only [expectedDefectCoefficients, ↓reduceIte, liftedOscillation,
    liftedOscillation_deriv_two]
  ring

theorem expectedDefect_zero_coordDeriv (alpha : ℝ) (n : ℕ) (x : FourSpace) :
    coordDeriv (fun z => expectedDefectCoefficients alpha n z 0) 0 x =
      amplitude alpha n * (n : ℝ) * (1 + (n : ℝ)^2 / 2) *
        Real.cos (x 1) * Real.cos ((n : ℝ) * x 0) := by
  have h0 : HasFDerivAt (fun z : FourSpace => z 0) (coordProj 0) x :=
    (coordProj 0).hasFDerivAt
  have h1 : HasFDerivAt (fun z : FourSpace => z 1) (coordProj 1) x :=
    (coordProj 1).hasFDerivAt
  have hs := (h0.const_mul (n : ℝ)).sin
  have hc := h1.cos
  have h := (hc.const_mul (amplitude alpha n * (1 + (n : ℝ)^2 / 2))).mul hs
  have hf : (fun z => expectedDefectCoefficients alpha n z 0) =
      fun z : FourSpace =>
        (amplitude alpha n * (1 + (n : ℝ)^2 / 2) * Real.cos (z 1)) *
          Real.sin ((n : ℝ) * z 0) := by
    funext z
    exact expectedDefect_zero_formula alpha n z
  simp only [Pi.mul_def] at h
  rw [coordDeriv, hf, h.fderiv]
  simp [coordProj, basisVector]
  ring

theorem distance_test_points (n : ℕ) (hn : 0 < n) :
    dist (0 : FourSpace) ((Real.pi / (n : ℝ)) • basisVector 0) = Real.pi / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  simp [dist_zero_left, norm_smul, basisVector, abs_of_pos Real.pi_pos]

theorem expectedDefect_derivative_difference (alpha : ℝ) (n : ℕ) (hn : 0 < n) :
    let y : FourSpace := (Real.pi / (n : ℝ)) • basisVector 0
    let d : FourSpace → ℝ := fun x =>
      coordDeriv (fun z => expectedDefectCoefficients alpha n z 0) 0 x
    |d 0 - d y| = amplitude alpha n * (n : ℝ) * (2 + (n : ℝ)^2) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  dsimp only
  rw [expectedDefect_zero_coordDeriv, expectedDefect_zero_coordDeriv]
  have hmul : (n : ℝ) * (Real.pi / (n : ℝ)) = Real.pi := by
    field_simp
  have h10 : (1 : Fin 4) ≠ 0 := by decide
  simp only [basisVector, PiLp.zero_apply, mul_zero, Real.cos_zero,
    mul_one, PiLp.smul_apply, smul_eq_mul, PiLp.single_apply,
    ↓reduceIte, h10, hmul, Real.cos_pi, mul_neg_one, sub_neg_eq_add]
  have ha : 0 ≤ amplitude alpha n := Real.rpow_nonneg (by positivity) _
  rw [abs_of_nonneg (by positivity)]
  ring

theorem amplitude_rpow_cancellation (alpha : ℝ) (n : ℕ) (hn : 0 < n) :
    amplitude alpha n * (n : ℝ) * (2 + (n : ℝ)^2) /
        Real.rpow (Real.pi / (n : ℝ)) alpha =
      (1 + 2 / (n : ℝ)^2) * Real.rpow Real.pi (-alpha) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 := ne_of_gt hnR
  have hna : Real.rpow (n : ℝ) alpha ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hnR _)
  have hpa : Real.rpow Real.pi alpha ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos Real.pi_pos _)
  have ha : amplitude alpha n = ((n : ℝ)^3 * Real.rpow (n : ℝ) alpha)⁻¹ := by
    unfold amplitude
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_neg hnR.le, Real.rpow_add hnR]
    norm_num
  rw [ha]
  simp only [Real.rpow_eq_pow] at *
  rw [Real.div_rpow Real.pi_pos.le hnR.le, Real.rpow_neg Real.pi_pos.le]
  field_simp [hn0, hna, hpa]
  ring

theorem expectedDefect_two_point_quotient (alpha : ℝ) (n : ℕ) (hn : 0 < n) :
    let y : FourSpace := (Real.pi / (n : ℝ)) • basisVector 0
    let d : FourSpace → ℝ := fun x =>
      coordDeriv (fun z => expectedDefectCoefficients alpha n z 0) 0 x
    |d 0 - d y| / Real.rpow (dist (0 : FourSpace) y) alpha =
      (1 + 2 / (n : ℝ)^2) * Real.rpow Real.pi (-alpha) := by
  dsimp only
  rw [expectedDefect_derivative_difference alpha n hn, distance_test_points n hn]
  exact amplitude_rpow_cancellation alpha n hn

end K24.Global.FlatTorus.CoefficientSharpness

open K24.Global K24.Global.FlatTorus

theorem solution (alpha : ℝ) (n : ℕ) (hn : 0 < n) :
    let y : FourSpace := (Real.pi / (n : ℝ)) • basisVector 0
    let d : FourSpace → ℝ := fun x =>
      coordDeriv (fun z => expectedDefectCoefficients alpha n z 0) 0 x
    |d 0 - d y| / Real.rpow (dist (0 : FourSpace) y) alpha =
      (1 + 2 / (n : ℝ)^2) * Real.rpow Real.pi (-alpha) := by
  exact CoefficientSharpness.expectedDefect_two_point_quotient alpha n hn

#print axioms solution
