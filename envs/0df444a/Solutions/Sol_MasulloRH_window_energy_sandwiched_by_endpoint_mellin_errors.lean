-- Prove2me | solution 1 for MasulloRH.window_energy_sandwiched_by_endpoint_mellin_errors
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-27T04:04:20.449292+00:00
-- url     : https://prove2.me/submissions/bb41727b-8d84-4596-befb-3f6561b45f67

import Definitions.Def_MasulloRH_VerticalThetaApproximation
import Theorems.Thm_MasulloRH_exact_laplace_transform_of_gaussian_theta_residual
import Theorems.Thm_MasulloRH_finite_theta_residual_tail_bound
import Theorems.Thm_MellinParseval_integrableOn_and_setIntegral_Ioi_norm_sq_lineIntegral_eq_two_pi_mul_integral_of_memLp_two
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory Set MasulloRH MasulloRH.GaussianApproximation MasulloRH.RationalThetaGrid
open MasulloRH.VerticalThetaApproximation

private theorem weightedIntegrable {m : ℕ} (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ)
    (c b : ℝ) (hl : 0 < c-b) (hu : c+b < 1) :
    Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|) * ‖approximation a y x‖^2) := by
  let R := 1/2 + ∑ i, |(y i:ℝ)-Real.log 2|
  have hsum : 0 ≤ ∑ i, |(y i:ℝ)-Real.log 2| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hR : 1/2 ≤ R := by dsimp [R]; linarith
  have hy (i : Fin m) : |(y i:ℝ)-Real.log 2| ≤ R := by
    have h := Finset.single_le_sum (f := fun j : Fin m => |(y j:ℝ)-Real.log 2|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    dsimp [R]; linarith
  exact (finite_theta_residual_tail_bound m 0 c b R (fun i => asComplex (a i)) (fun i => y i)
    le_rfl hR hl hu hy).1

private theorem lineParseval {m : ℕ} (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ)
    (c : ℝ) (hc : 0 < c) (hc' : c < 1) :
    Integrable (fun t : ℝ => ‖spectrum c a y t‖^2) ∧
    mass c a y = 2*Real.pi*energy c 0 (approximation a y) := by
  let A := fun x : ℝ => Complex.exp ((c:ℂ)*x) * approximation a y x
  have hA : Integrable A :=
    (exact_laplace_transform_of_gaussian_theta_residual (fun i => asComplex (a i)) (fun i => (y i:ℝ))
    (c:ℂ) hc hc').1
  have hNorm (x : ℝ) : ‖A x‖^2 = Real.exp (2*c*x) * ‖approximation a y x‖^2 := by
    dsimp [A]
    rw [norm_mul, mul_pow, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [sq, ← Real.exp_add]
    congr 2
    ring
  have hA2 : MemLp A 2 := by
    apply (memLp_two_iff_integrable_sq_norm hA.aestronglyMeasurable).mpr
    simp_rw [hNorm]
    simpa only [mul_zero, zero_mul, add_zero] using
      weightedIntegrable a y c 0 (by linarith) (by linarith)
  let K := fun v : ℝ => v ^ (-(2*(0:ℝ))) / v *
    ‖∫ x : ℝ, (v:ℂ)^((0:ℂ)+(x:ℂ)*Complex.I)*A x‖^2
  have hK (t : ℝ) : |Real.exp t| • K (Real.exp t) = ‖spectrum c a y t‖^2 := by
    have e (x : ℝ) : ((Real.exp t:ℝ):ℂ)^((0:ℂ)+(x:ℂ)*Complex.I)*A x =
        Complex.exp (pointAt c t*x)*approximation a y x := by
      dsimp [A,pointAt]
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'),
        ← Complex.ofReal_log (Real.exp_nonneg _),Real.log_exp,← mul_assoc,← Complex.exp_add]
      congr 2
      ring
    have hM := (exact_laplace_transform_of_gaussian_theta_residual (fun i => asComplex (a i))
      (fun i => (y i : ℝ)) (pointAt c t) (by simpa [pointAt] using hc) (by simpa [pointAt] using hc')).2
    change (∫ x : ℝ, Complex.exp (pointAt c t*x)*approximation a y x) = spectrum c a y t at hM
    dsimp only [K]
    simp_rw [e]
    rw [hM, abs_of_pos (Real.exp_pos _), smul_eq_mul]
    simp [(Real.exp_pos t).ne']
  have hp := MellinParseval.integrableOn_and_setIntegral_Ioi_norm_sq_lineIntegral_eq_two_pi_mul_integral_of_memLp_two 0 A hA hA2
  change IntegrableOn K (Ioi 0) ∧ (∫ v in Ioi (0:ℝ), K v) = 2*Real.pi*∫ x : ℝ, ‖A x‖^2 at hp
  have hd (x : ℝ) (_ : x ∈ (univ : Set ℝ)) := (Real.hasDerivAt_exp x).hasDerivWithinAt (s:=univ)
  rw [← show Real.exp '' (univ : Set ℝ)=Ioi 0 by rw [image_univ,Real.range_exp],
      integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hd Real.exp_injective.injOn,
      integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd Real.exp_injective.injOn] at hp
  simp only [integrableOn_univ, setIntegral_univ, hK, hNorm] at hp
  simpa only [mass,energy,mul_zero,zero_mul,add_zero] using hp

theorem solution {m : ℕ} (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ) :
    (∀ c : ℝ, 0 < c → c < 1 → Integrable (fun t : ℝ => ‖spectrum c a y t‖^2) ∧
      mass c a y = 2*Real.pi*energy c 0 (approximation a y)) ∧
    (∀ c b : ℝ, 0 ≤ b → 0 < c-b → c+b < 1 →
      Integrable (fun x : ℝ => Real.exp (2*c*x+2*b*|x|) * ‖approximation a y x‖^2) ∧
      max (mass (c-b) a y) (mass (c+b) a y) ≤ 2*Real.pi*energy c b (approximation a y) ∧
      2*Real.pi*energy c b (approximation a y) ≤ mass (c-b) a y + mass (c+b) a y) := by
  refine ⟨lineParseval a y, ?_⟩
  intro c b hb hL hU
  rw [(lineParseval a y (c-b) hL (by linarith)).2,(lineParseval a y (c+b) (by linarith) hU).2]
  let f := approximation a y
  let w := fun p q x : ℝ => Real.exp (2*p*x+2*q*|x|) * ‖f x‖^2
  have il : Integrable (w (c-b) 0) := weightedIntegrable a y _ _ (by linarith) (by linarith)
  have ih : Integrable (w (c+b) 0) := weightedIntegrable a y _ _ (by linarith) (by linarith)
  have iw : Integrable (w c b) := weightedIntegrable a y _ _ hL hU
  have lo (x : ℝ) : w (c-b) 0 x ≤ w c b x := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_left (neg_le_abs x) hb]
  have hi (x : ℝ) : w (c+b) 0 x ≤ w c b x := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_left (le_abs_self x) hb]
  have upper (x : ℝ) : w c b x ≤ w (c-b) 0 x + w (c+b) 0 x := by
    dsimp [w]
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
      rw [show 2*c*x+2*b*x=2*(c+b)*x+2*0*x by ring]
      exact le_add_of_nonneg_left (by positivity)
    · rw [abs_of_neg (lt_of_not_ge hx)]
      rw [show 2*c*x+2*b*(-x)=2*(c-b)*x+2*0*(-x) by ring]
      exact le_add_of_nonneg_right (by positivity)
  have hp := (show (0:ℝ) ≤ 2*Real.pi by positivity)
  refine ⟨iw, max_le (mul_le_mul_of_nonneg_left (integral_mono il iw lo) hp)
    (mul_le_mul_of_nonneg_left (integral_mono ih iw hi) hp),?_⟩
  have h := integral_mono iw (il.add ih) upper
  simp only [Pi.add_apply] at h
  rw [integral_add il ih] at h
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left h hp
