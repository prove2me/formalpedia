-- Prove2me | solution 1 for HighDimProb.RandomProcesses.gaussian_integration_by_parts
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-02T08:05:08.918191+00:00
-- url     : https://prove2.me/submissions/65e07af7-b741-465b-bd3e-d7b3a0104275

import Mathlib


open MeasureTheory ProbabilityTheory Filter

namespace SlepianProof

/-- The standard Gaussian density has derivative `-x ρ(x)`. -/
lemma gaussianPDF_hasDerivAt (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h := ((((hasDerivAt_id x).pow 2).neg.div_const 2).exp).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  have heq : gaussianPDFReal 0 1 = fun y : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
      Real.exp (-(y ^ 2) / 2) := by
    ext y
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [heq]
  convert h using 1 <;> (try simp only [id_eq, Pi.pow_apply, Pi.neg_apply,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]) <;> (first | ring | rfl)


/-- Transfer absolute integrability to the density-weighted Lebesgue integral. -/
lemma gaussian_weight_integrable {f : ℝ → ℝ}
    (hf : Integrable f (gaussianReal 0 1)) :
    Integrable (fun x => gaussianPDFReal 0 1 x * f x) := by
  rw [gaussianReal_of_var_ne_zero _ (one_ne_zero : (1 : NNReal) ≠ 0)] at hf
  have := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1) (ae_of_all _ fun _ => gaussianPDF_lt_top)).mp hf
  simpa only [toReal_gaussianPDF, smul_eq_mul] using this

/-- Gaussian integration by parts, under explicit absolute integrability assumptions.
No unproved boundary-decay hypothesis is used. -/
lemma gaussian_integration_by_parts {f f' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf : Integrable f (gaussianReal 0 1))
    (hf' : Integrable f' (gaussianReal 0 1))
    (hxf : Integrable (fun x => x * f x) (gaussianReal 0 1)) :
    (∫ x, f' x ∂gaussianReal 0 1) =
      ∫ x, x * f x ∂gaussianReal 0 1 := by
  have hi1 : Integrable (fun x => f x * (-x * gaussianPDFReal 0 1 x)) := by
    convert (gaussian_weight_integrable hxf).neg using 1
    ext x
    simp only [Pi.neg_apply]
    ring
  have hi2 : Integrable (fun x => f' x * gaussianPDFReal 0 1 x) := by
    simpa only [mul_comm] using gaussian_weight_integrable hf'
  have hi0 : Integrable (fun x => f x * gaussianPDFReal 0 1 x) := by
    simpa only [mul_comm] using gaussian_weight_integrable hf
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => hderiv x) (fun x _ => gaussianPDF_hasDerivAt x) hi1 hi2 hi0
  rw [integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : NNReal) ≠ 0),
    integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : NNReal) ≠ 0)]
  simp only [smul_eq_mul]
  have h1 : (∫ x : ℝ, f x * (-x * gaussianPDFReal 0 1 x)) =
      -(∫ x : ℝ, gaussianPDFReal 0 1 x * (x * f x)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [h1] at h
  have h2 : (∫ x : ℝ, f' x * gaussianPDFReal 0 1 x) =
      ∫ x : ℝ, gaussianPDFReal 0 1 x * f' x := by
    simp only [mul_comm]
  rw [h2] at h
  linarith

/-- A bounded differentiable function with bounded derivative satisfies Stein's identity. -/
lemma gaussian_integration_by_parts_bounded {f f' : ℝ → ℝ} {C D : ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf' : AEStronglyMeasurable f' (gaussianReal 0 1))
    (hf_bound : ∀ x, ‖f x‖ ≤ C) (hf'_bound : ∀ x, ‖f' x‖ ≤ D) :
    (∫ x, f' x ∂gaussianReal 0 1) =
      ∫ x, x * f x ∂gaussianReal 0 1 := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr fun x => (hderiv x).continuousAt
  have hi : Integrable f (gaussianReal 0 1) := by
    simpa using (integrable_const (1 : ℝ)).bdd_mul hf.aestronglyMeasurable
      (ae_of_all _ hf_bound)
  have hi' : Integrable f' (gaussianReal 0 1) := by
    simpa using (integrable_const (1 : ℝ)).bdd_mul hf'
      (ae_of_all _ hf'_bound)
  exact gaussian_integration_by_parts hderiv hi hi'
    (IsGaussian.integrable_id.mul_bdd hf.aestronglyMeasurable (ae_of_all _ hf_bound))

end SlepianProof

theorem solution {f f' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf : Integrable f (gaussianReal 0 1))
    (hf' : Integrable f' (gaussianReal 0 1))
    (hxf : Integrable (fun x => x * f x) (gaussianReal 0 1)) :
    (∫ x, f' x ∂gaussianReal 0 1) =
      ∫ x, x * f x ∂gaussianReal 0 1 := by
  exact SlepianProof.gaussian_integration_by_parts hderiv hf hf' hxf
