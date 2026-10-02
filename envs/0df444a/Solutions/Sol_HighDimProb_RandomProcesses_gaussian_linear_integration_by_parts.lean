-- Prove2me | solution 1 for HighDimProb.RandomProcesses.gaussian_linear_integration_by_parts
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-02T08:06:33.139782+00:00
-- url     : https://prove2.me/submissions/ccfb7860-f3bc-42ea-a216-58edb56b1508

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


open MeasureTheory ProbabilityTheory Filter

namespace SlepianProof

/-- Coordinatewise Gaussian integration by parts in a finite product. -/
lemma gaussian_pi_integration_by_parts {n : ℕ} (i : Fin (n + 1))
    {f df : (Fin (n + 1) → ℝ) → ℝ}
    (hderiv : ∀ (x : Fin (n + 1) → ℝ) (t : ℝ),
      HasDerivAt (fun y => f (Function.update x i y)) (df (Function.update x i t)) t)
    (hf : Integrable f (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)))
    (hdf : Integrable df (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)))
    (hxf : Integrable (fun x => x i * f x)
      (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1))) :
    (∫ x, df x ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
      ∫ x, x i * f x ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  have hp : MeasurePreserving e
      ((gaussianReal 0 1).prod (Measure.pi (fun _ : Fin n => gaussianReal 0 1)))
      (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) i).symm
  have hfi := (hp.integrable_comp_emb e.measurableEmbedding).mpr hf
  have hdfi := (hp.integrable_comp_emb e.measurableEmbedding).mpr hdf
  have hxfi := (hp.integrable_comp_emb e.measurableEmbedding).mpr hxf
  rw [← hp.integral_comp' df, ← hp.integral_comp' (fun x => x i * f x)]
  simp only [Function.comp_def] at hfi hdfi hxfi
  rw [integral_prod_symm _ hdfi, integral_prod_symm _ hxfi]
  apply integral_congr_ae
  filter_upwards [hfi.prod_left_ae, hdfi.prod_left_ae, hxfi.prod_left_ae]
    with y hy hyd hyx
  have he (t : ℝ) : e (t, y) = i.insertNth t y := rfl
  simp only [Function.comp_def, he, Fin.insertNth_apply_same] at hy hyd hyx ⊢
  apply gaussian_integration_by_parts (f := fun t => f (i.insertNth t y))
    (f' := fun t => df (i.insertNth t y)) _ hy hyd hyx
  intro t
  have h := hderiv (i.insertNth 0 y) t
  simpa only [Fin.update_insertNth] using h

end SlepianProof


open MeasureTheory ProbabilityTheory

namespace SlepianProof

/-- Stein's identity for a smooth bounded function of an arbitrary linear Gaussian image. -/
lemma gaussian_linear_integration_by_parts {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : (Fin (n + 1) → ℝ) →L[ℝ] E) (i : Fin (n + 1))
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) {C D : ℝ}
    (hf_bound : ∀ x, ‖f x‖ ≤ C) (hdf_bound : ∀ x, ‖fderiv ℝ f x‖ ≤ D) :
    (∫ x, fderiv ℝ f (L x) (L (Pi.single i 1))
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
    ∫ x, x i * f (L x)
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  have hfcont : Continuous fun x => f (L x) := hf.continuous.comp L.continuous
  have hdfcont : Continuous fun x => fderiv ℝ f (L x) (L (Pi.single i 1)) :=
    ((hf.continuous_fderiv one_ne_zero).comp L.continuous).clm_apply continuous_const
  have hb : ∀ x : Fin (n + 1) → ℝ,
      ‖fderiv ℝ f (L x) (L (Pi.single i 1))‖ ≤ D * ‖L (Pi.single i 1)‖ := by
    intro x
    exact le_trans ((fderiv ℝ f (L x)).le_opNorm _) <|
      mul_le_mul_of_nonneg_right (hdf_bound _) (norm_nonneg _)
  have hfi : Integrable (fun x => f (L x))
      (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) := by
    simpa using (integrable_const (1 : ℝ)).bdd_mul hfcont.aestronglyMeasurable
      (ae_of_all _ fun x => hf_bound (L x))
  have hdfi : Integrable (fun x => fderiv ℝ f (L x) (L (Pi.single i 1)))
      (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) := by
    simpa using (integrable_const (1 : ℝ)).bdd_mul hdfcont.aestronglyMeasurable
      (ae_of_all _ hb)
  have hxfi : Integrable (fun x => x i * f (L x))
      (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) :=
    (integrable_eval (μ := fun _ : Fin (n + 1) => gaussianReal 0 1)
      IsGaussian.integrable_id).mul_bdd hfcont.aestronglyMeasurable
        (ae_of_all _ fun x => hf_bound (L x))
  apply gaussian_pi_integration_by_parts i _ hfi hdfi hxfi
  intro x t
  exact ((hf.differentiable_one (L (Function.update x i t))).hasFDerivAt).comp_hasDerivAt t
    ((L.hasFDerivAt).comp_hasDerivAt t (hasDerivAt_update x i t))

end SlepianProof

theorem solution {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : (Fin (n + 1) → ℝ) →L[ℝ] E) (i : Fin (n + 1))
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) {C D : ℝ}
    (hf_bound : ∀ x, ‖f x‖ ≤ C) (hdf_bound : ∀ x, ‖fderiv ℝ f x‖ ≤ D) :
    (∫ x, fderiv ℝ f (L x) (L (Pi.single i 1))
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
    ∫ x, x i * f (L x)
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  exact SlepianProof.gaussian_linear_integration_by_parts L i f hf hf_bound hdf_bound
