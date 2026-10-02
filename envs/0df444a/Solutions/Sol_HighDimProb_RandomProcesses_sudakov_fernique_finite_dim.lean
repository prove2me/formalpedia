-- Prove2me | solution 1 for HighDimProb.RandomProcesses.sudakov_fernique_finite_dim
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-02T10:40:13.924306+00:00
-- url     : https://prove2.me/submissions/2eaf528f-dfd7-4a38-9f62-8dd3436c9f20

import Mathlib

-- Inlined module: SlepianGaussianRepresentation
section

open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder

namespace SlepianProof

lemma gaussian_eq_multivariate_covariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsGaussian μ] :
    μ = multivariateGaussian (∫ x, x ∂μ)
      (LinearMap.toMatrix₂ (EuclideanSpace.basisFun ι ℝ).toBasis
        (EuclideanSpace.basisFun ι ℝ).toBasis (covarianceBilin μ).toBilinForm) := by
  let b := (EuclideanSpace.basisFun ι ℝ).toBasis
  let S := LinearMap.toMatrix₂ b b (covarianceBilin μ).toBilinForm
  have hS : S.PosSemidef :=
    (LinearMap.isPosSemidef_iff_posSemidef_toMatrix b).mp
      (LinearMap.BilinForm.isPosSemidef_iff.mp (isPosSemidef_covarianceBilin (μ := μ)))
  have hr (z : EuclideanSpace ℝ ι) : (⇑(b.repr z) : ι → ℝ) = z.ofLp := by
    funext i
    simp [b, OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
  apply IsGaussian.ext
  · simp
  · ext x y
    rw [covarianceBilin_multivariateGaussian hS]
    have h := apply_eq_dotProduct_toMatrix₂_mulVec b b
      (covarianceBilin μ).toBilinForm x y
    simpa [S, hr, Function.comp_def] using h

lemma centered_gaussian_eq_map_pi_euclidean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsGaussian μ]
    (hmean : (∫ x, x ∂μ) = 0) :
    ∃ L : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι,
      μ = (Measure.pi (fun _ : ι => gaussianReal 0 1)).map L := by
  let S := LinearMap.toMatrix₂ (EuclideanSpace.basisFun ι ℝ).toBasis
    (EuclideanSpace.basisFun ι ℝ).toBasis (covarianceBilin μ).toBilinForm
  let A := toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)
  let e := (EuclideanSpace.equiv ι ℝ).symm
  refine ⟨A.comp e.toContinuousLinearMap, ?_⟩
  rw [gaussian_eq_multivariate_covariance μ, hmean]
  change (stdGaussian (EuclideanSpace ℝ ι)).map (fun x => 0 + A x) = _
  simp only [zero_add]
  rw [← map_pi_eq_stdGaussian]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma centered_gaussian_eq_map_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) [IsGaussian μ]
    (hmean : (∫ x, x ∂μ) = 0) :
    ∃ L : (ι → ℝ) →L[ℝ] (ι → ℝ),
      μ = (Measure.pi (fun _ : ι => gaussianReal 0 1)).map L := by
  let e := EuclideanSpace.equiv ι ℝ
  let ν := μ.map e.symm
  have hm : (∫ x, x ∂ν) = 0 := by
    change (∫ x, x ∂μ.map e.symm) = 0
    rw [ContinuousLinearEquiv.integral_id_map, hmean, map_zero]
  obtain ⟨A, hA⟩ := centered_gaussian_eq_map_pi_euclidean ν hm
  refine ⟨e.toContinuousLinearMap.comp A, ?_⟩
  have he : ν.map e = μ := by
    change (μ.map e.symm).map e = μ
    rw [Measure.map_map e.continuous.measurable e.symm.continuous.measurable]
    have hc : (⇑e ∘ ⇑e.symm) = id := by
      funext x
      exact e.apply_symm_apply x
    rw [hc, Measure.map_id]
  rw [← he, hA, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

end SlepianProof
end

-- Inlined module: SlepianLinearCovariance
section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace SlepianProof

lemma gaussian_pi_covariance_eval {κ : Type*} [Fintype κ] [DecidableEq κ] (i j : κ) :
    cov[fun x : κ → ℝ => x i, fun x : κ → ℝ => x j;
      Measure.pi (fun _ : κ => gaussianReal 0 1)] = if i = j then 1 else 0 := by
  have hG (k : κ) : MemLp (fun x : κ → ℝ => x k) 2
      (Measure.pi (fun _ : κ => gaussianReal 0 1)) :=
    IsGaussian.memLp_two_id.comp_measurePreserving
      (measurePreserving_eval (fun _ : κ => gaussianReal 0 1) k)
  rw [← covarianceBilin_apply_basisFun hG i j]
  change covarianceBilin ((Measure.pi (fun _ : κ => gaussianReal 0 1)).map (WithLp.toLp 2))
    (EuclideanSpace.basisFun κ ℝ i) (EuclideanSpace.basisFun κ ℝ j) = _
  rw [map_pi_eq_stdGaussian, covarianceBilin_stdGaussian]
  rw [innerSL_apply_apply, EuclideanSpace.basisFun_inner]
  simp

lemma gaussian_pi_covariance_linear {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] (L : (κ → ℝ) →L[ℝ] (ι → ℝ)) (i j : ι) :
    cov[fun x => L x i, fun x => L x j; Measure.pi (fun _ : κ => gaussianReal 0 1)] =
      ∑ k : κ, L (Pi.single k 1) i * L (Pi.single k 1) j := by
  have hG (k : κ) : MemLp (fun x : κ → ℝ => x k) 2
      (Measure.pi (fun _ : κ => gaussianReal 0 1)) :=
    IsGaussian.memLp_two_id.comp_measurePreserving
      (measurePreserving_eval (fun _ : κ => gaussianReal 0 1) k)
  have hL (x : κ → ℝ) (r : ι) : L x r = ∑ k : κ, L (Pi.single k 1) r * x k := by
    have h := congrArg (fun z => L z r) (pi_eq_sum_univ' x)
    simpa [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, mul_comm] using h
  have hfun (r : ι) : (fun x => L x r) =
      (fun x => ∑ k : κ, L (Pi.single k 1) r * x k) := funext (fun x => hL x r)
  rw [hfun i, hfun j]
  rw [covariance_fun_sum_fun_sum (fun k => (hG k).const_mul _)
    (fun k => (hG k).const_mul _)]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right, gaussian_pi_covariance_eval]
  simp

end SlepianProof
end

-- Inlined module: SudakovGaussianIncrement
section

open MeasureTheory ProbabilityTheory

namespace SudakovProof

lemma gaussian_increment_eq_columns {m : ℕ}
    (μ : Measure (Fin m → ℝ)) [IsGaussian μ]
    (hm : (∫ x, x ∂μ) = 0)
    (A : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ))
    (hA : μ = (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).map A)
    (i j : Fin m) :
    (∫ x, (x i - x j) ^ 2 ∂μ) =
      ∑ k : Fin m, (A (Pi.single k 1) i - A (Pi.single k 1) j) ^ 2 := by
  have hG (r : Fin m) : HasGaussianLaw (fun x : Fin m → ℝ => x r) μ :=
    IsGaussian.hasGaussianLaw_id.map
      (ContinuousLinearMap.proj r : (Fin m → ℝ) →L[ℝ] ℝ)
  have hm' (r : Fin m) : (∫ x, x r ∂μ) = 0 := by
    change (∫ x, (ContinuousLinearMap.proj r : (Fin m → ℝ) →L[ℝ] ℝ) x ∂μ) = 0
    rw [(ContinuousLinearMap.proj r : (Fin m → ℝ) →L[ℝ] ℝ).integral_comp_id_comm
      IsGaussian.integrable_id,
      hm, map_zero]
  have hmij : (∫ x, x i - x j ∂μ) = 0 := by
    rw [integral_sub (hG i).integrable (hG j).integrable, hm', hm', sub_self]
  have hv := variance_fun_sub (hG i).memLp_two (hG j).memLp_two
  rw [variance_eq_integral (X := fun x : Fin m → ℝ => x i - x j)
    ((hG i).aemeasurable.sub (hG j).aemeasurable),
    hmij, ← covariance_self (hG i).aemeasurable,
    ← covariance_self (hG j).aemeasurable] at hv
  simp only [sub_zero] at hv
  have hc (r s : Fin m) : cov[fun x => x r, fun x => x s; μ] =
      ∑ k : Fin m, A (Pi.single k 1) r * A (Pi.single k 1) s := by
    rw [hA, covariance_map_fun (measurable_pi_apply r).aestronglyMeasurable
      (measurable_pi_apply s).aestronglyMeasurable A.continuous.measurable.aemeasurable]
    exact SlepianProof.gaussian_pi_covariance_linear A r s
  rw [hc, hc, hc] at hv
  calc
    (∫ x, (x i - x j) ^ 2 ∂μ) = _ := hv
    _ = ∑ k : Fin m, (A (Pi.single k 1) i - A (Pi.single k 1) j) ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring

end SudakovProof
end

-- Inlined module: SudakovSoftmax
section

open MeasureTheory ProbabilityTheory

namespace SudakovProof

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

noncomputable def expSum (β : ℝ) (x : ι → ℝ) : ℝ := ∑ i, Real.exp (β * x i)

noncomputable def expSumGrad (β : ℝ) (x : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, Real.exp (β * x i) • ContinuousLinearMap.proj i

noncomputable def softMax (β : ℝ) (x : ι → ℝ) : ℝ := Real.log (expSum β x) / β

noncomputable def weight (β : ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  Real.exp (β * x i) / expSum β x

noncomputable def softMaxGrad (β : ℝ) (x : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, weight β x i • ContinuousLinearMap.proj i

noncomputable def weightDeriv (β : ℝ) (x : ι → ℝ) (i : ι) : (ι → ℝ) →L[ℝ] ℝ :=
  (β * weight β x i) • (ContinuousLinearMap.proj i - softMaxGrad β x)

noncomputable def softMaxHess (β : ℝ) (x : ι → ℝ) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, (weightDeriv β x i).smulRight (ContinuousLinearMap.proj i)

lemma expSum_pos (β : ℝ) (x : ι → ℝ) : 0 < expSum β x :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

lemma weight_pos (β : ℝ) (x : ι → ℝ) (i : ι) : 0 < weight β x i :=
  div_pos (Real.exp_pos _) (expSum_pos β x)

lemma sum_weight (β : ℝ) (x : ι → ℝ) : ∑ i, weight β x i = 1 := by
  simp only [weight, ← Finset.sum_div]
  change expSum β x / expSum β x = 1
  exact div_self (expSum_pos β x).ne'

lemma weight_le_one (β : ℝ) (x : ι → ℝ) (i : ι) : weight β x i ≤ 1 := by
  rw [weight, div_le_one (expSum_pos β x)]
  exact Finset.single_le_sum (f := fun j => Real.exp (β * x j))
    (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i)

lemma expSumGrad_apply (β : ℝ) (x u : ι → ℝ) :
    expSumGrad β x u = ∑ i, Real.exp (β * x i) * u i := by
  simp [expSumGrad]

lemma softMaxGrad_apply (β : ℝ) (x u : ι → ℝ) :
    softMaxGrad β x u = ∑ i, weight β x i * u i := by
  simp [softMaxGrad]

lemma softMaxGrad_apply_div (β : ℝ) (x u : ι → ℝ) :
    softMaxGrad β x u = expSumGrad β x u / expSum β x := by
  rw [softMaxGrad_apply, expSumGrad_apply, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  simp [weight, div_mul_eq_mul_div]

lemma expSum_contDiff (β : ℝ) : ContDiff ℝ 2 (expSum β : (ι → ℝ) → ℝ) := by
  apply ContDiff.sum
  intro i _
  exact (contDiff_const.mul (contDiff_apply ℝ ℝ i)).exp

lemma softMax_contDiff (β : ℝ) : ContDiff ℝ 2 (softMax β : (ι → ℝ) → ℝ) :=
  ((expSum_contDiff β).log (fun x => (expSum_pos β x).ne')).div_const β

lemma expSum_hasFDerivAt (β : ℝ) (x : ι → ℝ) :
    HasFDerivAt (expSum β) (β • expSumGrad β x) x := by
  have hi (i : ι) : HasFDerivAt (fun y : ι → ℝ => Real.exp (β * y i))
      ((β * Real.exp (β * x i)) •
        (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) x := by
    simpa only [Function.comp_def, Pi.mul_apply, ContinuousLinearMap.proj_apply,
      smul_zero, add_zero, smul_smul, mul_comm] using!
      (Real.hasDerivAt_exp (β * x i)).comp_hasFDerivAt x
        (hasFDerivAt_const β x |>.mul
          (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt)
  have h := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i)
  simpa only [expSum, expSumGrad, Finset.smul_sum, smul_smul] using! h

lemma softMax_hasFDerivAt (β : ℝ) (hβ : β ≠ 0) (x : ι → ℝ) :
    HasFDerivAt (softMax β) (softMaxGrad β x) x := by
  have h := ((expSum_hasFDerivAt β x).log (expSum_pos β x).ne').mul_const β⁻¹
  convert! h using 1
  ext u
  rw [softMaxGrad_apply_div]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp

lemma weight_hasFDerivAt (β : ℝ) (x : ι → ℝ) (i : ι) :
    HasFDerivAt (fun y : ι → ℝ => weight β y i) (weightDeriv β x i) x := by
  have hi : HasFDerivAt (fun y : ι → ℝ => Real.exp (β * y i))
      ((β * Real.exp (β * x i)) •
        (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)) x := by
    simpa only [Function.comp_def, Pi.mul_apply, ContinuousLinearMap.proj_apply,
      smul_zero, add_zero, smul_smul, mul_comm] using!
      (Real.hasDerivAt_exp (β * x i)).comp_hasFDerivAt x
        (hasFDerivAt_const β x |>.mul
          (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt)
  have h := hi.mul ((hasDerivAt_inv (expSum_pos β x).ne').comp_hasFDerivAt x
    (expSum_hasFDerivAt β x))
  convert! h using 1
  ext u
  simp only [weightDeriv, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply, Function.comp_def,
    ContinuousLinearMap.proj_apply, smul_eq_mul, weight, softMaxGrad_apply_div]
  field_simp [(expSum_pos β x).ne']
  <;> ring

lemma softMaxGrad_hasFDerivAt (β : ℝ) (x : ι → ℝ) :
    HasFDerivAt (softMaxGrad β) (softMaxHess β x) x :=
  HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (weight_hasFDerivAt β x i).smul_const
      (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ))

lemma softMax_fderiv (β : ℝ) (hβ : β ≠ 0) (x : ι → ℝ) :
    fderiv ℝ (softMax β) x = softMaxGrad β x := (softMax_hasFDerivAt β hβ x).fderiv

lemma softMax_fderiv_fderiv (β : ℝ) (hβ : β ≠ 0) (x : ι → ℝ) :
    fderiv ℝ (fderiv ℝ (softMax β)) x = softMaxHess β x := by
  have h : fderiv ℝ (softMax β : (ι → ℝ) → ℝ) = softMaxGrad β :=
    funext (softMax_fderiv β hβ)
  rw [h]
  exact (softMaxGrad_hasFDerivAt β x).fderiv

end SudakovProof
end

-- Inlined module: SudakovSoftmaxBounds
section

namespace SudakovProof

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

lemma proj_norm_le_one (i : ι) :
    ‖(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using norm_le_pi_norm x i

lemma softMaxGrad_norm_le_one (β : ℝ) (x : ι → ℝ) : ‖softMaxGrad β x‖ ≤ 1 := by
  unfold softMaxGrad
  calc
    ‖∑ i, weight β x i • ContinuousLinearMap.proj i‖
        ≤ ∑ i, ‖weight β x i • (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, weight β x i := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (weight_pos β x i)]
      simpa using mul_le_mul_of_nonneg_left (proj_norm_le_one i) (weight_pos β x i).le
    _ = 1 := sum_weight β x

lemma weightDeriv_norm_le (β : ℝ) (x : ι → ℝ) (i : ι) :
    ‖weightDeriv β x i‖ ≤ 2 * ‖β‖ := by
  have hp : ‖weight β x i‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (weight_pos β x i)]
    exact weight_le_one β x i
  have hg : ‖(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ) - softMaxGrad β x‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by linarith [proj_norm_le_one i, softMaxGrad_norm_le_one β x])
  unfold weightDeriv
  rw [norm_smul, norm_mul]
  have hb : ‖β‖ * ‖weight β x i‖ ≤ ‖β‖ := by
    simpa using mul_le_mul_of_nonneg_left hp (norm_nonneg β)
  have h := mul_le_mul hb hg (norm_nonneg _) (norm_nonneg β)
  simpa [mul_comm] using h

lemma softMaxHess_norm_le (β : ℝ) (x : ι → ℝ) :
    ‖softMaxHess β x‖ ≤ (Fintype.card ι : ℝ) * (2 * ‖β‖) := by
  unfold softMaxHess
  calc
    ‖∑ i, (weightDeriv β x i).smulRight (ContinuousLinearMap.proj i)‖
        ≤ ∑ i, ‖(weightDeriv β x i).smulRight
          (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, (2 * ‖β‖) := by
      apply Finset.sum_le_sum
      intro i _
      rw [ContinuousLinearMap.norm_smulRight_apply]
      simpa using mul_le_mul (weightDeriv_norm_le β x i) (proj_norm_le_one i)
        (norm_nonneg _) (by positivity : 0 ≤ 2 * ‖β‖)
    _ = (Fintype.card ι : ℝ) * (2 * ‖β‖) := by simp

lemma softMaxHess_apply (β : ℝ) (x u v : ι → ℝ) :
    softMaxHess β x u v = β *
      ((∑ i, weight β x i * u i * v i) -
        (∑ i, weight β x i * u i) * (∑ i, weight β x i * v i)) := by
  have h : softMaxHess β x u v =
      ∑ i, (β * (weight β x i * u i * v i) -
        β * ((∑ j, weight β x j * u j) * (weight β x i * v i))) := by
    simp only [softMaxHess, sum_apply, ContinuousLinearMap.smulRight_apply,
      weightDeriv, smul_apply, sub_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
      softMaxGrad_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h, Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum]
  ring

noncomputable def finiteMax (x : ι → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty x

lemma le_finiteMax (x : ι → ℝ) (i : ι) : x i ≤ finiteMax x :=
  Finset.le_sup' (f := x) (Finset.mem_univ i)

lemma finiteMax_le_softMax (β : ℝ) (hβ : 0 < β) (x : ι → ℝ) :
    finiteMax x ≤ softMax β x := by
  apply Finset.sup'_le
  intro i _
  rw [softMax, le_div_iff₀ hβ]
  apply (Real.le_log_iff_exp_le (expSum_pos β x)).mpr
  simpa only [expSum, mul_comm] using
    (Finset.single_le_sum (f := fun j => Real.exp (β * x j))
      (fun j _ => (Real.exp_pos _).le) (Finset.mem_univ i))

lemma softMax_le_finiteMax_add (β : ℝ) (hβ : 0 < β) (x : ι → ℝ) :
    softMax β x ≤ finiteMax x + Real.log (Fintype.card ι) / β := by
  have hc : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  have hs : expSum β x ≤ (Fintype.card ι : ℝ) * Real.exp (β * finiteMax x) := by
    calc
      expSum β x ≤ ∑ _i : ι, Real.exp (β * finiteMax x) := by
        apply Finset.sum_le_sum
        intro i _
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_finiteMax x i) hβ.le)
      _ = _ := by simp
  have h := Real.log_le_log (expSum_pos β x) hs
  rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp] at h
  rw [softMax, div_le_iff₀ hβ]
  calc
    Real.log (expSum β x) ≤ Real.log (Fintype.card ι) + β * finiteMax x := h
    _ = (finiteMax x + Real.log (Fintype.card ι) / β) * β := by field_simp; ring

end SudakovProof
end

-- Inlined module: SudakovVarianceIdentity
section

namespace SudakovProof

lemma weighted_variance_identity {ι : Type*} [Fintype ι] (p a : ι → ℝ)
    (hp : ∑ i, p i = 1) :
    (∑ i, p i * (a i) ^ 2) - (∑ i, p i * a i) ^ 2 =
      (1 / 2 : ℝ) * ∑ i, ∑ j, p i * p j * (a i - a j) ^ 2 := by
  classical
  have hr (i : ι) : (∑ j, p i * p j * (a i - a j) ^ 2) =
      (p i * (a i) ^ 2) * (∑ j, p j) + p i * (∑ j, p j * (a j) ^ 2) -
        (2 * p i * a i) * (∑ j, p j * a j) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have htwo : (∑ i, 2 * p i * a i) = 2 * (∑ i, p i * a i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [hr, hp, mul_one]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.sum_mul, hp, one_mul, htwo]
  ring

lemma weighted_column_variance_identity {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (hp : ∑ i, p i = 1) (A : κ → ι → ℝ) :
    (∑ k, ((∑ i, p i * (A k i) ^ 2) - (∑ i, p i * A k i) ^ 2)) =
      (1 / 2 : ℝ) * ∑ i, ∑ j, p i * p j * (∑ k, (A k i - A k j) ^ 2) := by
  classical
  simp_rw [weighted_variance_identity p _ hp]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]

lemma weighted_column_variance_comparison {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1) (A B : κ → ι → ℝ)
    (hinc : ∀ i j, (∑ k, (A k i - A k j) ^ 2) ≤ ∑ k, (B k i - B k j) ^ 2) :
    (∑ k, ((∑ i, p i * (A k i) ^ 2) - (∑ i, p i * A k i) ^ 2)) ≤
      ∑ k, ((∑ i, p i * (B k i) ^ 2) - (∑ i, p i * B k i) ^ 2) := by
  rw [weighted_column_variance_identity p hp A, weighted_column_variance_identity p hp B]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact mul_le_mul_of_nonneg_left (hinc i j) (mul_nonneg (hp0 i) (hp0 j))

end SudakovProof
end

-- Inlined module: SudakovInterpolation
section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SudakovProof

lemma integrable_comp_of_bounded_fderiv {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (P : Measure Ω) [IsFiniteMeasure P]
    (f : E → ℝ) (hf : Differentiable ℝ f) {D : ℝ}
    (hdf : ∀ x, ‖fderiv ℝ f x‖ ≤ D) {Z : Ω → E} (hZ : Integrable Z P) :
    Integrable (fun ω => f (Z ω)) P := by
  have hg (z : E) : ‖f z‖ ≤ ‖f 0‖ + D * ‖z‖ := by
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le
      (s := Set.univ) (fun y _ => hf y) (fun y _ => hdf y)
      (convex_univ : Convex ℝ (Set.univ : Set E)) (Set.mem_univ 0) (Set.mem_univ z)
    simp only [sub_zero] at h
    calc
      ‖f z‖ = ‖f 0 + (f z - f 0)‖ := by congr 1; ring
      _ ≤ ‖f 0‖ + ‖f z - f 0‖ := norm_add_le _ _
      _ ≤ ‖f 0‖ + D * ‖z‖ := add_le_add le_rfl h
  exact ((integrable_const ‖f 0‖).add (hZ.norm.const_mul D)).mono'
    (hf.continuous.comp_aestronglyMeasurable hZ.aestronglyMeasurable)
    (ae_of_all _ (fun ω => hg (Z ω)))

/-- Differentiation under the Gaussian expectation along a rotation of linear images.
The uniform derivative bound supplies an explicit integrable envelope. -/
lemma gaussian_rotation_hasDerivAt_boundedDerivative {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L M : (Fin n → ℝ) →L[ℝ] E)
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) {D : ℝ}
    (hdf_bound : ∀ x, ‖fderiv ℝ f x‖ ≤ D) (θ : ℝ) :
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
  have hfi : Integrable (fun x => f (Z θ x)) μ :=
    integrable_comp_of_bounded_fderiv μ f hf.differentiable_one hdf_bound
      (L.integrable_comp hid |>.smul (Real.cos θ) |>.add
        (M.integrable_comp hid |>.smul (Real.sin θ)))
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

end SudakovProof
end

-- Inlined module: SlepianIBP
section

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
end

-- Inlined module: SlepianProductIBP
section

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
end

-- Inlined module: SlepianLinearIBP
section

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
end

-- Inlined module: SlepianSecondOrderIBP
section

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
end

-- Inlined module: SudakovHessianInterpolation
section

open MeasureTheory ProbabilityTheory

namespace SudakovProof

open SlepianProof

/-- Gaussian interpolation in a basis-independent Hessian form. -/
lemma gaussian_rotation_interpolation_boundedDerivative {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L M : (Fin (n + 1) → ℝ) →L[ℝ] E)
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) {D H : ℝ}
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
  have hd := gaussian_rotation_hasDerivAt_boundedDerivative L M f (hf.of_le (by norm_num))
    hdf_bound θ
  let Z : (Fin (n + 1) → ℝ) →L[ℝ] E := Real.cos θ • L + Real.sin θ • M
  let V : (Fin (n + 1) → ℝ) →L[ℝ] E := -Real.sin θ • L + Real.cos θ • M
  have h := gaussian_directional_integration_by_parts Z V f hf hdf_bound hddf_bound
  simp only [Z, V, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply] at h
  rw [h] at hd
  exact hd

end SudakovProof
end

-- Inlined module: SlepianBilinear
section

open MeasureTheory ProbabilityTheory

namespace SlepianProof

lemma bilinear_pi_expansion {m : ℕ}
    (B : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) →L[ℝ] ℝ) (x : Fin m → ℝ) :
    B x x = ∑ i : Fin m, ∑ j : Fin m,
      (x i * x j) * B (Pi.single i 1) (Pi.single j 1) := by
  classical
  have he (A : (Fin m → ℝ) →L[ℝ] ℝ) :
      A x = ∑ j : Fin m, x j * A (Pi.single j 1) := by
    simpa only [map_sum, map_smul, smul_eq_mul] using congrArg A (pi_eq_sum_univ' x)
  have h1 : B x x = ∑ i : Fin m, x i * B (Pi.single i 1) x := by
    simpa only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul] using
        congrArg (fun z => B z x) (pi_eq_sum_univ' x)
  rw [h1]
  simp_rw [he]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Sum of Hessian quadratic forms of the columns is a contraction with the Gram matrix. -/
lemma sum_bilinear_image_eq_gram {m n : ℕ}
    (L : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ))
    (B : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) →L[ℝ] ℝ) :
    (∑ k : Fin n, B (L (Pi.single k 1)) (L (Pi.single k 1))) =
      ∑ i : Fin m, ∑ j : Fin m,
        (∑ k : Fin n, L (Pi.single k 1) i * L (Pi.single k 1) j) *
          B (Pi.single i 1) (Pi.single j 1) := by
  classical
  simp_rw [bilinear_pi_expansion]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]

/-- Equal diagonals and ordered off-diagonal Gram entries order the Hessian contraction. -/
lemma bilinear_gram_comparison {m n : ℕ}
    (L M : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ))
    (B : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) →L[ℝ] ℝ)
    (hdiag : ∀ i : Fin m, (∑ k : Fin n, (L (Pi.single k 1) i) ^ 2) =
      ∑ k : Fin n, (M (Pi.single k 1) i) ^ 2)
    (hcov : ∀ i j : Fin m, (∑ k : Fin n, M (Pi.single k 1) i * M (Pi.single k 1) j) ≤
      ∑ k : Fin n, L (Pi.single k 1) i * L (Pi.single k 1) j)
    (hB : ∀ i j : Fin m, i ≠ j → 0 ≤ B (Pi.single i 1) (Pi.single j 1)) :
    (∑ k : Fin n, B (M (Pi.single k 1)) (M (Pi.single k 1))) ≤
      ∑ k : Fin n, B (L (Pi.single k 1)) (L (Pi.single k 1)) := by
  rw [sum_bilinear_image_eq_gram, sum_bilinear_image_eq_gram]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : i = j
  · subst j
    have h := hdiag i
    simp only [pow_two] at h
    rw [h]
  · exact mul_le_mul_of_nonneg_right (hcov i j) (hB i j hij)

/-- The cross terms vanish when the two linear images use disjoint Gaussian coordinates. -/
lemma bilinear_disjoint_rotation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (a b : E) (c s : ℝ) (hab : a = 0 ∨ b = 0) :
    B (c • a + s • b) (-s • a + c • b) =
      (c * s) * (B b b - B a a) := by
  rcases hab with rfl | rfl <;>
    simp only [smul_zero, zero_add, add_zero, map_zero, zero_apply,
      map_smul, smul_apply, smul_eq_mul] <;> ring

end SlepianProof
end

-- Inlined module: SudakovFunctional
section

open MeasureTheory ProbabilityTheory

namespace SudakovProof

open SlepianProof

/-- Gaussian comparison for a smooth function with bounded derivatives.
The ordering is expressed directly as a comparison of Hessian contractions. -/
lemma gaussian_functional_comparison_linear {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L M : (Fin (n + 1) → ℝ) →L[ℝ] E)
    (hindep : ∀ k : Fin (n + 1), L (Pi.single k 1) = 0 ∨ M (Pi.single k 1) = 0)
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) {D H : ℝ}
    (hdf_bound : ∀ y, ‖fderiv ℝ f y‖ ≤ D)
    (hddf_bound : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H)
    (htrace : ∀ y,
      (∑ k, fderiv ℝ (fderiv ℝ f) y (L (Pi.single k 1)) (L (Pi.single k 1))) ≤
        ∑ k, fderiv ℝ (fderiv ℝ f) y (M (Pi.single k 1)) (M (Pi.single k 1))) :
    (∫ x, f (L x) ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) ≤
      ∫ x, f (M x) ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  classical
  let μ := Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)
  let Z (θ : ℝ) (x : Fin (n + 1) → ℝ) := Real.cos θ • L x + Real.sin θ • M x
  let U (θ : ℝ) (i : Fin (n + 1)) :=
    Real.cos θ • L (Pi.single i 1) + Real.sin θ • M (Pi.single i 1)
  let V (θ : ℝ) (i : Fin (n + 1)) :=
    -Real.sin θ • L (Pi.single i 1) + Real.cos θ • M (Pi.single i 1)
  let B (y : E) := fderiv ℝ (fderiv ℝ f) y
  let g (θ : ℝ) := ∫ x, f (Z θ x) ∂μ
  let Q (θ : ℝ) (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) := B (Z θ x) (U θ i) (V θ i)
  have hz (θ : ℝ) : Continuous (Z θ) := by
    dsimp [Z]
    fun_prop
  have hb : Continuous B := (hf.fderiv_right (by norm_num) :
    ContDiff ℝ 1 (fderiv ℝ f)).continuous_fderiv one_ne_zero
  have hqi (θ : ℝ) (i : Fin (n + 1)) : Integrable (Q θ i) μ := by
    have hc : Continuous (Q θ i) :=
      (((hb.comp (hz θ)).clm_apply continuous_const).clm_apply continuous_const)
    have he (x : Fin (n + 1) → ℝ) :
        ‖Q θ i x‖ ≤ H * ‖U θ i‖ * ‖V θ i‖ := by
      apply le_trans ((B (Z θ x)).le_opNorm₂ (U θ i) (V θ i))
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hddf_bound _) (norm_nonneg _)) (norm_nonneg _)
    simpa using (integrable_const (1 : ℝ)).bdd_mul hc.aestronglyMeasurable (ae_of_all _ he)
  have hd (θ : ℝ) : HasDerivAt g (∑ i : Fin (n + 1), ∫ x, Q θ i x ∂μ) θ :=
    gaussian_rotation_interpolation_boundedDerivative L M f hf hdf_bound hddf_bound θ
  have hnonneg (θ : ℝ) (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
      0 ≤ (∑ i : Fin (n + 1), ∫ x, Q θ i x ∂μ) := by
    rw [← integral_finsetSum Finset.univ (fun i _ => hqi θ i)]
    apply integral_nonneg
    intro x
    have hcs : 0 ≤ Real.cos θ * Real.sin θ := mul_nonneg
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
      (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩)
    have he (i : Fin (n + 1)) : Q θ i x = (Real.cos θ * Real.sin θ) *
        (B (Z θ x) (M (Pi.single i 1)) (M (Pi.single i 1)) -
          B (Z θ x) (L (Pi.single i 1)) (L (Pi.single i 1))) :=
      bilinear_disjoint_rotation (B (Z θ x)) _ _ _ _ (hindep i)
    simp_rw [he]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    exact mul_nonneg hcs (sub_nonneg.mpr (htrace (Z θ x)))
  have hdiff : Differentiable ℝ g := fun θ => (hd θ).differentiableAt
  have hmono := monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) (Real.pi / 2))
    hdiff.continuous.continuousOn hdiff.differentiableOn
    (fun θ hθ => by rw [(hd θ).deriv]; exact hnonneg θ (Set.mem_of_mem_of_subset hθ interior_subset))
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have h := hmono ⟨le_rfl, hpi⟩ ⟨hpi, le_rfl⟩ hpi
  simpa [g, Z] using h

end SudakovProof
end

-- Inlined module: SudakovFunctionalIndex
section

open MeasureTheory ProbabilityTheory

namespace SudakovProof

lemma gaussian_functional_comparison_index {κ : Type*} [Fintype κ] [Nonempty κ]
    [DecidableEq κ] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L M : (κ → ℝ) →L[ℝ] E)
    (hindep : ∀ k : κ, L (Pi.single k 1) = 0 ∨ M (Pi.single k 1) = 0)
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) {D H : ℝ}
    (hdf_bound : ∀ y, ‖fderiv ℝ f y‖ ≤ D)
    (hddf_bound : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H)
    (htrace : ∀ y,
      (∑ k, fderiv ℝ (fderiv ℝ f) y (L (Pi.single k 1)) (L (Pi.single k 1))) ≤
        ∑ k, fderiv ℝ (fderiv ℝ f) y (M (Pi.single k 1)) (M (Pi.single k 1))) :
    (∫ x, f (L x) ∂Measure.pi (fun _ : κ => gaussianReal 0 1)) ≤
      ∫ x, f (M x) ∂Measure.pi (fun _ : κ => gaussianReal 0 1) := by
  let n := Fintype.card κ - 1
  have hc : n + 1 = Fintype.card κ := by
    have := Fintype.card_pos (α := κ)
    dsimp [n]
    omega
  let e : Fin (n + 1) ≃ κ := (finCongr hc).trans (Fintype.equivFin κ).symm
  let A : (Fin (n + 1) → ℝ) →L[ℝ] (κ → ℝ) :=
    { toFun x k := x (e.symm k)
      map_add' x y := rfl
      map_smul' c x := rfl }
  have ha (k : Fin (n + 1)) : A (Pi.single k 1) = Pi.single (e k) 1 := by
    ext j
    simp [A, Pi.single_apply, e.symm_apply_eq]
  have ht (y : E) :
      (∑ k, fderiv ℝ (fderiv ℝ f) y ((L.comp A) (Pi.single k 1))
        ((L.comp A) (Pi.single k 1))) ≤
      ∑ k, fderiv ℝ (fderiv ℝ f) y ((M.comp A) (Pi.single k 1))
        ((M.comp A) (Pi.single k 1)) := by
    simp only [ContinuousLinearMap.comp_apply, ha]
    rw [e.sum_comp (fun k => fderiv ℝ (fderiv ℝ f) y (L (Pi.single k 1))
        (L (Pi.single k 1))),
      e.sum_comp (fun k => fderiv ℝ (fderiv ℝ f) y (M (Pi.single k 1))
        (M (Pi.single k 1)))]
    exact htrace y
  have h := gaussian_functional_comparison_linear (L.comp A) (M.comp A)
    (fun k => by simpa only [ContinuousLinearMap.comp_apply, ha] using hindep (e k))
    f hf hdf_bound hddf_bound ht
  have hp := measurePreserving_piCongrLeft (fun _ : κ => gaussianReal 0 1) e
  have heA : (⇑(MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e)) = ⇑A := by
    ext x k
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply, A]
  have hM := hp.integral_comp' (fun x => f (M x))
  have hL := hp.integral_comp' (fun x => f (L x))
  rw [heA] at hM hL
  change (∫ x, f (M (A x)) ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) = _ at hM
  change (∫ x, f (L (A x)) ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) = _ at hL
  simpa only [ContinuousLinearMap.comp_apply, hM, hL] using h

end SudakovProof
end

-- Inlined module: SudakovIndependentCopies
section

open MeasureTheory ProbabilityTheory

namespace SudakovProof

lemma gaussian_functional_comparison_independent_copies {κ : Type*} [Fintype κ] [Nonempty κ]
    [DecidableEq κ] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A B : (κ → ℝ) →L[ℝ] E)
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) {D H : ℝ}
    (hdf_bound : ∀ y, ‖fderiv ℝ f y‖ ≤ D)
    (hddf_bound : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H)
    (htrace : ∀ y,
      (∑ k, fderiv ℝ (fderiv ℝ f) y (A (Pi.single k 1)) (A (Pi.single k 1))) ≤
        ∑ k, fderiv ℝ (fderiv ℝ f) y (B (Pi.single k 1)) (B (Pi.single k 1))) :
    (∫ x, f (A x) ∂Measure.pi (fun _ : κ => gaussianReal 0 1)) ≤
      ∫ x, f (B x) ∂Measure.pi (fun _ : κ => gaussianReal 0 1) := by
  let p : ((κ ⊕ κ) → ℝ) →L[ℝ] (κ → ℝ) :=
    { toFun x i := x (Sum.inl i)
      map_add' x y := rfl
      map_smul' c x := rfl }
  let q : ((κ ⊕ κ) → ℝ) →L[ℝ] (κ → ℝ) :=
    { toFun x i := x (Sum.inr i)
      map_add' x y := rfl
      map_smul' c x := rfl }
  let L := A.comp p
  let M := B.comp q
  have hpl (k : κ) : p (Pi.single (Sum.inl k) 1) = Pi.single k 1 := by
    ext i
    simp [p, Pi.single_apply]
  have hpr (k : κ) : p (Pi.single (Sum.inr k) 1) = 0 := by
    ext i
    simp [p, Pi.single_apply]
  have hql (k : κ) : q (Pi.single (Sum.inl k) 1) = 0 := by
    ext i
    simp [q, Pi.single_apply]
  have hqr (k : κ) : q (Pi.single (Sum.inr k) 1) = Pi.single k 1 := by
    ext i
    simp [q, Pi.single_apply]
  have hindep (k : κ ⊕ κ) : L (Pi.single k 1) = 0 ∨ M (Pi.single k 1) = 0 := by
    cases k with
    | inl k => right; simp [M, hql]
    | inr k => left; simp [L, hpr]
  have ht (y : E) :
      (∑ k : κ ⊕ κ, fderiv ℝ (fderiv ℝ f) y (L (Pi.single k 1))
        (L (Pi.single k 1))) ≤
      ∑ k : κ ⊕ κ, fderiv ℝ (fderiv ℝ f) y (M (Pi.single k 1))
        (M (Pi.single k 1)) := by
    simpa [L, M, Fintype.sum_sum_type, hpl, hpr, hql, hqr] using htrace y
  have h := gaussian_functional_comparison_index L M hindep f hf
    hdf_bound hddf_bound ht
  let e := (MeasurableEquiv.sumPiEquivProdPi (fun _ : κ ⊕ κ => ℝ)).symm
  have hp := measurePreserving_sumPiEquivProdPi_symm (fun _ : κ ⊕ κ => gaussianReal 0 1)
  have hi (T : ((κ ⊕ κ) → ℝ) →L[ℝ] E) :
      Integrable (fun x => f (T x)) (Measure.pi (fun _ : κ ⊕ κ => gaussianReal 0 1)) := by
    have hid : Integrable (fun x : (κ ⊕ κ) → ℝ => x)
        (Measure.pi (fun _ : κ ⊕ κ => gaussianReal 0 1)) :=
      Integrable.of_eval fun i => integrable_eval IsGaussian.integrable_id
    exact integrable_comp_of_bounded_fderiv _ f
      (hf.differentiable (by norm_num)) hdf_bound (T.integrable_comp hid)
  have heL (x : (κ → ℝ) × (κ → ℝ)) : L (e x) = A x.1 := rfl
  have heM (x : (κ → ℝ) × (κ → ℝ)) : M (e x) = B x.2 := rfl
  have hL := hp.integral_comp' (fun x => f (L x))
  have hM := hp.integral_comp' (fun x => f (M x))
  have hiL := (hp.integrable_comp_emb e.measurableEmbedding).mpr (hi L)
  have hiM := (hp.integrable_comp_emb e.measurableEmbedding).mpr (hi M)
  simp only [Function.comp_def] at hiL hiM
  change (∫ x, f (L (e x)) ∂(Measure.pi (fun _ : κ => gaussianReal 0 1)).prod
    (Measure.pi (fun _ : κ => gaussianReal 0 1))) = _ at hL
  change (∫ x, f (M (e x)) ∂(Measure.pi (fun _ : κ => gaussianReal 0 1)).prod
    (Measure.pi (fun _ : κ => gaussianReal 0 1))) = _ at hM
  rw [integral_prod _ hiL] at hL
  rw [integral_prod _ hiM] at hM
  change (∫ x, ∫ _y, f (A x) ∂Measure.pi (fun _ : κ => gaussianReal 0 1)
    ∂Measure.pi (fun _ : κ => gaussianReal 0 1)) = _ at hL
  change (∫ _x, ∫ y, f (B y) ∂Measure.pi (fun _ : κ => gaussianReal 0 1)
    ∂Measure.pi (fun _ : κ => gaussianReal 0 1)) = _ at hM
  simp only [integral_const, probReal_univ, one_smul] at hL hM
  rw [← hM, ← hL] at h
  exact h

end SudakovProof
end

-- Inlined module: SudakovSoftmaxComparison
section

open MeasureTheory ProbabilityTheory

namespace SudakovProof

variable {κ ι : Type*} [Fintype κ] [Nonempty κ] [DecidableEq κ]
    [Fintype ι] [Nonempty ι] [DecidableEq ι]

lemma softMax_hessian_contraction (β : ℝ) (x : ι → ℝ)
    (A : (κ → ℝ) →L[ℝ] (ι → ℝ)) :
    (∑ k, softMaxHess β x (A (Pi.single k 1)) (A (Pi.single k 1))) =
      β * ∑ k, ((∑ i, weight β x i * (A (Pi.single k 1) i) ^ 2) -
        (∑ i, weight β x i * A (Pi.single k 1) i) ^ 2) := by
  simp_rw [softMaxHess_apply, pow_two, mul_assoc]
  rw [Finset.mul_sum]

lemma softMax_hessian_comparison (β : ℝ) (hβ : 0 ≤ β) (x : ι → ℝ)
    (A B : (κ → ℝ) →L[ℝ] (ι → ℝ))
    (hinc : ∀ i j,
      (∑ k, (A (Pi.single k 1) i - A (Pi.single k 1) j) ^ 2) ≤
        ∑ k, (B (Pi.single k 1) i - B (Pi.single k 1) j) ^ 2) :
    (∑ k, softMaxHess β x (A (Pi.single k 1)) (A (Pi.single k 1))) ≤
      ∑ k, softMaxHess β x (B (Pi.single k 1)) (B (Pi.single k 1)) := by
  rw [softMax_hessian_contraction, softMax_hessian_contraction]
  exact mul_le_mul_of_nonneg_left
    (weighted_column_variance_comparison (weight β x) (fun i => (weight_pos β x i).le)
      (sum_weight β x) (fun k i => A (Pi.single k 1) i)
      (fun k i => B (Pi.single k 1) i) hinc) hβ

lemma gaussian_softMax_comparison_linear (β : ℝ) (hβ : 0 < β)
    (A B : (κ → ℝ) →L[ℝ] (ι → ℝ))
    (hinc : ∀ i j,
      (∑ k, (A (Pi.single k 1) i - A (Pi.single k 1) j) ^ 2) ≤
        ∑ k, (B (Pi.single k 1) i - B (Pi.single k 1) j) ^ 2) :
    (∫ x, softMax β (A x) ∂Measure.pi (fun _ : κ => gaussianReal 0 1)) ≤
      ∫ x, softMax β (B x) ∂Measure.pi (fun _ : κ => gaussianReal 0 1) := by
  apply gaussian_functional_comparison_independent_copies A B (softMax β)
    (softMax_contDiff β)
    (D := 1) (H := (Fintype.card ι : ℝ) * (2 * ‖β‖))
  · intro y
    rw [softMax_fderiv β hβ.ne']
    exact softMaxGrad_norm_le_one β y
  · intro y
    rw [softMax_fderiv_fderiv β hβ.ne']
    exact softMaxHess_norm_le β y
  · intro y
    simp_rw [softMax_fderiv_fderiv β hβ.ne']
    exact softMax_hessian_comparison β hβ.le y A B hinc

end SudakovProof
end

-- Inlined module: SudakovGaussianComparison
section

open MeasureTheory ProbabilityTheory

namespace SudakovProof

lemma gaussian_softMax_comparison {m : ℕ} [Nonempty (Fin m)]
    (μ ν : Measure (Fin m → ℝ)) [IsGaussian μ] [IsGaussian ν]
    (hmμ : (∫ x, x ∂μ) = 0) (hmν : (∫ x, x ∂ν) = 0)
    (hinc : ∀ i j, (∫ x, (x i - x j) ^ 2 ∂μ) ≤ ∫ x, (x i - x j) ^ 2 ∂ν)
    (β : ℝ) (hβ : 0 < β) :
    (∫ x, softMax β x ∂μ) ≤ ∫ x, softMax β x ∂ν := by
  obtain ⟨A, hA⟩ := SlepianProof.centered_gaussian_eq_map_pi μ hmμ
  obtain ⟨B, hB⟩ := SlepianProof.centered_gaussian_eq_map_pi ν hmν
  have hi (i j : Fin m) :
      (∑ k, (A (Pi.single k 1) i - A (Pi.single k 1) j) ^ 2) ≤
        ∑ k, (B (Pi.single k 1) i - B (Pi.single k 1) j) ^ 2 := by
    simpa only [gaussian_increment_eq_columns μ hmμ A hA,
      gaussian_increment_eq_columns ν hmν B hB] using hinc i j
  have h := gaussian_softMax_comparison_linear β hβ A B hi
  rw [hA, hB, integral_map (by fun_prop) (softMax_contDiff β).continuous.aestronglyMeasurable,
    integral_map (by fun_prop) (softMax_contDiff β).continuous.aestronglyMeasurable]
  exact h

end SudakovProof
end

-- Inlined module: SudakovProcessBasics
section

open MeasureTheory ProbabilityTheory

namespace SudakovProof

lemma hasGaussianLaw_finite {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (X : ι → Ω → ℝ) (hXG : IsGaussianProcess X P) :
    HasGaussianLaw (fun ω i => X i ω) P := by
  let L : (↥(Finset.univ : Finset ι) → ℝ) →L[ℝ] (ι → ℝ) :=
    { toFun x i := x ⟨i, Finset.mem_univ i⟩
      map_add' x y := rfl
      map_smul' c x := rfl }
  exact (hXG.hasGaussianLaw Finset.univ).map L


lemma integrable_finset_sup' {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (s : Finset ι) (hs : s.Nonempty) (X : ι → Ω → ℝ)
    (hX : ∀ i ∈ s, Integrable (X i) P) :
    Integrable (fun ω => s.sup' hs (fun i => X i ω)) P := by
  have hi : Integrable (s.sup' hs X) P :=
    Finset.sup'_induction hs X (p := fun Z : Ω → ℝ => Integrable Z P)
      (fun _ hf _ hg => hf.sup hg) hX
  convert hi using 1
  funext ω
  exact (Finset.sup'_apply hs X ω).symm


end SudakovProof
end

-- Inlined module: SudakovProcessComparison
section

open MeasureTheory ProbabilityTheory

namespace SudakovProof

lemma gaussian_softMax_comparison_process {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    [Nonempty (Fin m)] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Fin m → Ω → ℝ)
    (hXG : IsGaussianProcess X P) (hYG : IsGaussianProcess Y P)
    (hXmean : ∀ i, ∫ ω, X i ω ∂P = 0) (hYmean : ∀ i, ∫ ω, Y i ω ∂P = 0)
    (hinc : ∀ i j, ∫ ω, (X i ω - X j ω) ^ 2 ∂P ≤
      ∫ ω, (Y i ω - Y j ω) ^ 2 ∂P)
    (β : ℝ) (hβ : 0 < β) :
    (∫ ω, softMax β (fun i => X i ω) ∂P) ≤
      ∫ ω, softMax β (fun i => Y i ω) ∂P := by
  let x : Ω → (Fin m → ℝ) := fun ω i => X i ω
  let y : Ω → (Fin m → ℝ) := fun ω i => Y i ω
  have hx := hasGaussianLaw_finite P X hXG
  have hy := hasGaussianLaw_finite P Y hYG
  let μ := P.map x
  let ν := P.map y
  haveI : IsGaussian μ := hx.isGaussian_map
  haveI : IsGaussian ν := hy.isGaussian_map
  have hmμ : (∫ z, z ∂μ) = 0 := by
    change (∫ z, id z ∂P.map x) = 0
    rw [integral_map hx.aemeasurable aestronglyMeasurable_id]
    ext i
    change (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ) (∫ ω, x ω ∂P) = 0
    rw [← ContinuousLinearMap.integral_comp_comm _ hx.integrable]
    exact hXmean i
  have hmν : (∫ z, z ∂ν) = 0 := by
    change (∫ z, id z ∂P.map y) = 0
    rw [integral_map hy.aemeasurable aestronglyMeasurable_id]
    ext i
    change (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ) (∫ ω, y ω ∂P) = 0
    rw [← ContinuousLinearMap.integral_comp_comm _ hy.integrable]
    exact hYmean i
  have hi (i j : Fin m) :
      (∫ z, (z i - z j) ^ 2 ∂μ) ≤ ∫ z, (z i - z j) ^ 2 ∂ν := by
    rw [integral_map hx.aemeasurable (by fun_prop :
        AEStronglyMeasurable (fun z : Fin m → ℝ => (z i - z j) ^ 2) μ),
      integral_map hy.aemeasurable (by fun_prop :
        AEStronglyMeasurable (fun z : Fin m → ℝ => (z i - z j) ^ 2) ν)]
    exact hinc i j
  have h := gaussian_softMax_comparison μ ν hmμ hmν hi β hβ
  rw [integral_map hx.aemeasurable (softMax_contDiff β).continuous.aestronglyMeasurable,
    integral_map hy.aemeasurable (softMax_contDiff β).continuous.aestronglyMeasurable] at h
  exact h

end SudakovProof
end

-- Inlined module: SudakovFinite
section

open MeasureTheory ProbabilityTheory

namespace SudakovProof

lemma sudakov_fernique_finite_fin {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    [Nonempty (Fin m)] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Fin m → Ω → ℝ)
    (hXG : IsGaussianProcess X P) (hYG : IsGaussianProcess Y P)
    (hXmean : ∀ i, ∫ ω, X i ω ∂P = 0) (hYmean : ∀ i, ∫ ω, Y i ω ∂P = 0)
    (hinc : ∀ i j, ∫ ω, (X i ω - X j ω) ^ 2 ∂P ≤
      ∫ ω, (Y i ω - Y j ω) ^ 2 ∂P) :
    (∫ ω, finiteMax (fun i => X i ω) ∂P) ≤
      ∫ ω, finiteMax (fun i => Y i ω) ∂P := by
  have hiX : Integrable (fun ω => finiteMax (fun i => X i ω)) P :=
    integrable_finset_sup' P Finset.univ Finset.univ_nonempty X
      (fun i _ => (hXG.hasGaussianLaw_eval i).integrable)
  have hiY : Integrable (fun ω => finiteMax (fun i => Y i ω)) P :=
    integrable_finset_sup' P Finset.univ Finset.univ_nonempty Y
      (fun i _ => (hYG.hasGaussianLaw_eval i).integrable)
  have his (Z : Fin m → Ω → ℝ) (hZG : IsGaussianProcess Z P)
      (β : ℝ) (hβ : 0 < β) : Integrable (fun ω => softMax β (fun i => Z i ω)) P := by
    apply integrable_comp_of_bounded_fderiv P (softMax β)
      ((softMax_contDiff β).differentiable (by norm_num)) (D := 1)
    · intro x
      rw [softMax_fderiv β hβ.ne']
      exact softMaxGrad_norm_le_one β x
    · exact (hasGaussianLaw_finite P Z hZG).integrable
  apply le_of_forall_pos_le_add
  intro ε hε
  let a : ℝ := Real.log (Fintype.card (Fin m))
  have ha : 0 ≤ a := Real.log_nonneg (by
    exact_mod_cast Fintype.card_pos (α := Fin m))
  let β : ℝ := (a + 1) / ε
  have hβ : 0 < β := div_pos (by linarith) hε
  have hβε : β * ε = a + 1 := by
    dsimp [β]
    field_simp
  have herr : a / β ≤ ε := by
    apply (div_le_iff₀ hβ).mpr
    nlinarith [hβε]
  calc
    (∫ ω, finiteMax (fun i => X i ω) ∂P) ≤
        ∫ ω, softMax β (fun i => X i ω) ∂P :=
      integral_mono hiX (his X hXG β hβ) (fun ω => finiteMax_le_softMax β hβ _)
    _ ≤ ∫ ω, softMax β (fun i => Y i ω) ∂P :=
      gaussian_softMax_comparison_process P X Y hXG hYG hXmean hYmean hinc β hβ
    _ ≤ ∫ ω, (finiteMax (fun i => Y i ω) + a / β) ∂P :=
      integral_mono (his Y hYG β hβ) (hiY.add (integrable_const _))
        (fun ω => softMax_le_finiteMax_add β hβ _)
    _ = (∫ ω, finiteMax (fun i => Y i ω) ∂P) + a / β := by
      rw [integral_add hiY (integrable_const _), integral_const, probReal_univ, one_smul]
    _ ≤ (∫ ω, finiteMax (fun i => Y i ω) ∂P) + ε := add_le_add le_rfl herr

theorem sudakov_fernique_finite {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : ι → Ω → ℝ)
    (hXG : IsGaussianProcess X P) (hYG : IsGaussianProcess Y P)
    (hXmean : ∀ i, ∫ ω, X i ω ∂P = 0) (hYmean : ∀ i, ∫ ω, Y i ω ∂P = 0)
    (hinc : ∀ i j, ∫ ω, (X i ω - X j ω) ^ 2 ∂P ≤
      ∫ ω, (Y i ω - Y j ω) ^ 2 ∂P) :
    (∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) ∂P) ≤
      ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => Y i ω) ∂P := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  letI : Nonempty (Fin (Fintype.card ι)) := ⟨e.symm (Classical.ofNonempty)⟩
  have h := sudakov_fernique_finite_fin P (fun i => X (e i)) (fun i => Y (e i))
    (hXG.comp_right e) (hYG.comp_right e)
    (fun i => hXmean (e i)) (fun i => hYmean (e i)) (fun i j => hinc (e i) (e j))
  have he (Z : ι → Ω → ℝ) (ω : Ω) : finiteMax (fun i => Z (e i) ω) =
      Finset.univ.sup' Finset.univ_nonempty (fun i => Z i ω) := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro i _
      exact Finset.le_sup' (f := fun i => Z i ω) (Finset.mem_univ (e i))
    · apply Finset.sup'_le
      intro i _
      have hi := le_finiteMax (fun j => Z (e j) ω) (e.symm i)
      simpa using hi
  simpa only [he] using h

end SudakovProof
end

open MeasureTheory ProbabilityTheory

theorem solution :
∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      {ι : Type} [Fintype ι] [Nonempty ι] (X Y : ι → Ω → ℝ)
      (hXG : IsGaussianProcess X P) (hYG : IsGaussianProcess Y P)
      (hXmean : ∀ i, ∫ ω, X i ω ∂P = 0) (hYmean : ∀ i, ∫ ω, Y i ω ∂P = 0)
      (hinc : ∀ i j, ∫ ω, (X i ω - X j ω) ^ 2 ∂P ≤ ∫ ω, (Y i ω - Y j ω) ^ 2 ∂P),
      ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) ∂P ≤
        ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => Y i ω) ∂P := by
  intro Ω _ P _ ι _ _ X Y hXG hYG hXmean hYmean hinc
  exact SudakovProof.sudakov_fernique_finite P X Y hXG hYG hXmean hYmean hinc
