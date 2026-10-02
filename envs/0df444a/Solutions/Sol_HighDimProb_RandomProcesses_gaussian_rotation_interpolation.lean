-- Prove2me | solution 1 for HighDimProb.RandomProcesses.gaussian_rotation_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-02T08:30:43.396008+00:00
-- url     : https://prove2.me/submissions/de68e1fc-4556-49c2-9364-53848ee91866

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


open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SlepianProof

/-- Differentiation under the Gaussian expectation along a rotation of linear images.
The uniform derivative bound supplies an explicit integrable envelope. -/
lemma gaussian_rotation_hasDerivAt {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L M : (Fin n → ℝ) →L[ℝ] E)
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) {C D : ℝ}
    (hf_bound : ∀ x, ‖f x‖ ≤ C) (hdf_bound : ∀ x, ‖fderiv ℝ f x‖ ≤ D) (θ : ℝ) :
    HasDerivAt
      (fun u => ∫ x, f (Real.cos u • L x + Real.sin u • M x)
        ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      (∫ x, fderiv ℝ f (Real.cos θ • L x + Real.sin θ • M x)
        (-Real.sin θ • L x + Real.cos θ • M x)
        ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) θ := by
  let μ := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let Z (u : ℝ) (x : Fin n → ℝ) := Real.cos u • L x + Real.sin u • M x
  let V (u : ℝ) (x : Fin n → ℝ) := -Real.sin u • L x + Real.cos u • M x
  have hD : 0 ≤ D := le_trans (norm_nonneg _) (hdf_bound 0)
  have hid : Integrable (fun x : Fin n → ℝ => x) μ :=
    Integrable.of_eval fun i => integrable_eval IsGaussian.integrable_id
  have hb : Integrable (fun x => D * (‖L x‖ + ‖M x‖)) μ :=
    ((L.integrable_comp hid).norm.add (M.integrable_comp hid).norm).const_mul D
  have hz (u : ℝ) : Continuous (Z u) :=
    (L.continuous.const_smul _).add (M.continuous.const_smul _)
  have hv (u : ℝ) : Continuous (V u) :=
    (L.continuous.const_smul _).add (M.continuous.const_smul _)
  have hdc (u : ℝ) : Continuous (fun x => fderiv ℝ f (Z u x) (V u x)) :=
    ((hf.continuous_fderiv one_ne_zero).comp (hz u)).clm_apply (hv u)
  have hfi : Integrable (fun x => f (Z θ x)) μ := by
    simpa using (integrable_const (1 : ℝ)).bdd_mul
      (hf.continuous.comp (hz θ)).aestronglyMeasurable (ae_of_all _ fun x => hf_bound _)
  have hbound (u : ℝ) (x : Fin n → ℝ) :
      ‖fderiv ℝ f (Z u x) (V u x)‖ ≤ D * (‖L x‖ + ‖M x‖) := by
    have hV : ‖V u x‖ ≤ ‖L x‖ + ‖M x‖ := by
      dsimp [V]
      apply le_trans (norm_add_le _ _)
      apply add_le_add
      · rw [norm_smul, Real.norm_eq_abs, abs_neg]
        exact (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one u) (norm_nonneg _)).trans_eq
          (one_mul _)
      · rw [norm_smul, Real.norm_eq_abs]
        exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one u) (norm_nonneg _)).trans_eq
          (one_mul _)
    calc ‖fderiv ℝ f (Z u x) (V u x)‖
        ≤ ‖fderiv ℝ f (Z u x)‖ * ‖V u x‖ := (fderiv ℝ f (Z u x)).le_opNorm _
      _ ≤ D * ‖V u x‖ := mul_le_mul_of_nonneg_right (hdf_bound _) (norm_nonneg _)
      _ ≤ D * (‖L x‖ + ‖M x‖) := mul_le_mul_of_nonneg_left hV hD
  have hd (u : ℝ) (x : Fin n → ℝ) : HasDerivAt (fun v => f (Z v x))
      (fderiv ℝ f (Z u x) (V u x)) u := by
    apply ((hf.differentiable_one (Z u x)).hasFDerivAt).comp_hasDerivAt u
    exact ((Real.hasDerivAt_cos u).smul_const (L x)).add
      ((Real.hasDerivAt_sin u).smul_const (M x))
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (s := Set.univ) (F := fun u x => f (Z u x))
    (F' := fun u x => fderiv ℝ f (Z u x) (V u x)) (bound := fun x => D * (‖L x‖ + ‖M x‖))
    (Filter.univ_mem : Set.univ ∈ 𝓝 θ)
    (Eventually.of_forall fun u => (hf.continuous.comp (hz u)).aestronglyMeasurable)
    hfi (hdc θ).aestronglyMeasurable
    (ae_of_all _ fun x u _ => hbound u x) hb (ae_of_all _ fun x u _ => hd u x)
  exact h.2

end SlepianProof


open MeasureTheory ProbabilityTheory

namespace SlepianProof

/-- Gaussian integration by parts for the directional derivative of a smooth function.
Both linear images may be singular and may be correlated. -/
lemma gaussian_directional_integration_by_parts {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L M : (Fin (n + 1) → ℝ) →L[ℝ] E)
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) {D H : ℝ}
    (hdf_bound : ∀ y, ‖fderiv ℝ f y‖ ≤ D)
    (hddf_bound : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H) :
    (∫ x, fderiv ℝ f (L x) (M x)
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
      ∑ i : Fin (n + 1), ∫ x,
        (fderiv ℝ (fderiv ℝ f) (L x) (L (Pi.single i 1))) (M (Pi.single i 1))
        ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  classical
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hgi (i : Fin (n + 1)) : ContDiff ℝ 1
      (fun y => fderiv ℝ f y (M (Pi.single i 1))) :=
    hf1.clm_apply contDiff_const
  have hgderiv (i : Fin (n + 1)) (y : E) : HasFDerivAt
      (fun z => fderiv ℝ f z (M (Pi.single i 1)))
      ((fderiv ℝ (fderiv ℝ f) y).flip (M (Pi.single i 1))) y := by
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using
      (hf1.differentiable_one y).hasFDerivAt.clm_apply
        (hasFDerivAt_const (M (Pi.single i 1)) y)
  have hgb (i : Fin (n + 1)) (y : E) :
      ‖fderiv ℝ f y (M (Pi.single i 1))‖ ≤ D * ‖M (Pi.single i 1)‖ :=
    ((fderiv ℝ f y).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hdf_bound _) (norm_nonneg _))
  have hgdb (i : Fin (n + 1)) (y : E) :
      ‖fderiv ℝ (fun z => fderiv ℝ f z (M (Pi.single i 1))) y‖ ≤
        H * ‖M (Pi.single i 1)‖ := by
    rw [(hgderiv i y).fderiv]
    apply le_trans ((fderiv ℝ (fderiv ℝ f) y).flip.le_opNorm _)
    rw [ContinuousLinearMap.opNorm_flip]
    exact mul_le_mul_of_nonneg_right (hddf_bound _) (norm_nonneg _)
  have hid : Integrable (fun x : Fin (n + 1) → ℝ => x)
      (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) :=
    Integrable.of_eval fun i => integrable_eval IsGaussian.integrable_id
  have hi (i : Fin (n + 1)) : Integrable
      (fun x => x i * fderiv ℝ f (L x) (M (Pi.single i 1)))
      (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) :=
    (hid.eval i).mul_bdd
      (((hf1.continuous.comp L.continuous).clm_apply continuous_const).aestronglyMeasurable)
      (ae_of_all _ fun x => hgb i (L x))
  have hsum (x : Fin (n + 1) → ℝ) :
      fderiv ℝ f (L x) (M x) =
        ∑ i : Fin (n + 1), x i * fderiv ℝ f (L x) (M (Pi.single i 1)) := by
    conv_lhs => arg 2; rw [pi_eq_sum_univ' x]
    simp only [map_sum, map_smul, smul_eq_mul]
  simp_rw [hsum]
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  have h := gaussian_linear_integration_by_parts L i
    (fun y => fderiv ℝ f y (M (Pi.single i 1))) (hgi i) (hgb i) (hgdb i)
  simp_rw [(hgderiv i _).fderiv] at h
  simpa only [ContinuousLinearMap.flip_apply] using h.symm

end SlepianProof


open MeasureTheory ProbabilityTheory

namespace SlepianProof

/-- Gaussian interpolation in a basis-independent Hessian form. -/
lemma gaussian_rotation_interpolation {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L M : (Fin (n + 1) → ℝ) →L[ℝ] E)
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) {C D H : ℝ}
    (hf_bound : ∀ y, ‖f y‖ ≤ C)
    (hdf_bound : ∀ y, ‖fderiv ℝ f y‖ ≤ D)
    (hddf_bound : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H) (θ : ℝ) :
    HasDerivAt
      (fun u => ∫ x, f (Real.cos u • L x + Real.sin u • M x)
        ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1))
      (∑ i : Fin (n + 1), ∫ x,
        (fderiv ℝ (fderiv ℝ f) (Real.cos θ • L x + Real.sin θ • M x)
          (Real.cos θ • L (Pi.single i 1) + Real.sin θ • M (Pi.single i 1)))
          (-Real.sin θ • L (Pi.single i 1) + Real.cos θ • M (Pi.single i 1))
        ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) θ := by
  have hd := gaussian_rotation_hasDerivAt L M f (hf.of_le (by norm_num))
    hf_bound hdf_bound θ
  let Z : (Fin (n + 1) → ℝ) →L[ℝ] E := Real.cos θ • L + Real.sin θ • M
  let V : (Fin (n + 1) → ℝ) →L[ℝ] E := -Real.sin θ • L + Real.cos θ • M
  have h := gaussian_directional_integration_by_parts Z V f hf hdf_bound hddf_bound
  simp only [Z, V, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply] at h
  rw [h] at hd
  exact hd

end SlepianProof

theorem solution {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L M : (Fin (n + 1) → ℝ) →L[ℝ] E)
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) {C D H : ℝ}
    (hf_bound : ∀ y, ‖f y‖ ≤ C)
    (hdf_bound : ∀ y, ‖fderiv ℝ f y‖ ≤ D)
    (hddf_bound : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H) (θ : ℝ) :
    HasDerivAt
      (fun u => ∫ x, f (Real.cos u • L x + Real.sin u • M x)
        ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1))
      (∑ i : Fin (n + 1), ∫ x,
        (fderiv ℝ (fderiv ℝ f) (Real.cos θ • L x + Real.sin θ • M x)
          (Real.cos θ • L (Pi.single i 1) + Real.sin θ • M (Pi.single i 1)))
          (-Real.sin θ • L (Pi.single i 1) + Real.cos θ • M (Pi.single i 1))
        ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) θ := by
  exact SlepianProof.gaussian_rotation_interpolation L M f hf hf_bound hdf_bound hddf_bound θ
