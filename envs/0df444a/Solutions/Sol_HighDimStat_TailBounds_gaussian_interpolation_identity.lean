-- Prove2me | solution 1 for HighDimStat.TailBounds.gaussian_interpolation_identity
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-02T18:18:31.130654+00:00
-- url     : https://prove2.me/submissions/a7f568d4-33f1-4687-b85f-d0c3f25a5d64

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 2000000

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

section

open MeasureTheory ProbabilityTheory

namespace GaussianConcentration

set_option maxHeartbeats 800000

/-- The native coordinate assumptions determine the standard Gaussian law, including n=0.
No measurability or integrability hypotheses beyond HasGaussianLaw are added. -/
lemma gaussian_map_eq_standard {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {Prob : Measure Ω} [IsProbabilityMeasure Prob]
    (X : Ω → EuclideanSpace ℝ (Fin n)) (hX : HasGaussianLaw X Prob)
    (hm : ∀ i, ∫ ω, X ω i ∂Prob = 0)
    (hc : ∀ i j, ∫ ω, X ω i * X ω j ∂Prob = if i = j then 1 else 0) :
    Prob.map X = stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  classical
  let μ := Prob.map X
  haveI : IsGaussian μ := hX.isGaussian_map
  let p (i : Fin n) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap
  have hmean : (∫ x, x ∂μ) = 0 := by
    ext i
    change p i (∫ x, x ∂μ) = 0
    rw [← (p i).integral_comp_id_comm IsGaussian.integrable_id,
      integral_map hX.aemeasurable (p i).continuous.aestronglyMeasurable]
    exact hm i
  have hmoment (i : Fin n) : MemLp (fun ω => X ω i) 2 Prob :=
    (hX.map (p i)).memLp_two
  have hcov (i j : Fin n) : cov[fun ω => X ω i, fun ω => X ω j; Prob] =
      if i = j then 1 else 0 := by
    rw [covariance_eq_sub (hmoment i) (hmoment j), hm, hm, mul_zero, sub_zero]
    exact hc i j
  have hrepr : (fun ω => WithLp.toLp 2 (fun i => X ω i)) = X := rfl
  have hmat : LinearMap.toMatrix₂ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis (covarianceBilin μ).toBilinForm =
        (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp only [LinearMap.toMatrix₂_apply, Matrix.one_apply]
    change covarianceBilin μ (EuclideanSpace.basisFun (Fin n) ℝ i)
      (EuclideanSpace.basisFun (Fin n) ℝ j) = if i = j then 1 else 0
    have h := covarianceBilin_apply_basisFun hmoment i j
    rw [hrepr] at h
    exact h.trans (hcov i j)
  change μ = stdGaussian (EuclideanSpace ℝ (Fin n))
  rw [SlepianProof.gaussian_eq_multivariate_covariance μ, hmean, hmat,
    multivariateGaussian_zero_one]

end GaussianConcentration

end

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

section

open MeasureTheory ProbabilityTheory

namespace GaussianConcentration

set_option maxHeartbeats 1200000

noncomputable section

lemma gaussian_pi_isGaussian {κ : Type*} [Fintype κ] :
    IsGaussian (Measure.pi (fun _ : κ => gaussianReal 0 1)) := by
  let e := EuclideanSpace.equiv κ ℝ
  have hback : (Measure.pi (fun _ : κ => gaussianReal 0 1)).map e.symm =
      stdGaussian (EuclideanSpace ℝ κ) := map_pi_eq_stdGaussian
  have hm : (stdGaussian (EuclideanSpace ℝ κ)).map e =
      Measure.pi (fun _ : κ => gaussianReal 0 1) := by
    rw [← hback, Measure.map_map e.continuous.measurable e.symm.continuous.measurable]
    have he : (⇑e ∘ ⇑e.symm) = id := by funext x; exact e.apply_symm_apply x
    rw [he, Measure.map_id]
  rw [← hm]
  infer_instance

lemma gaussian_pi_integral_id {κ : Type*} [Fintype κ] :
    (∫ x : κ → ℝ, x ∂Measure.pi (fun _ : κ => gaussianReal 0 1)) = 0 := by
  let e := EuclideanSpace.equiv κ ℝ
  have hback : (Measure.pi (fun _ : κ => gaussianReal 0 1)).map e.symm =
      stdGaussian (EuclideanSpace ℝ κ) := map_pi_eq_stdGaussian
  have hm : (stdGaussian (EuclideanSpace ℝ κ)).map e =
      Measure.pi (fun _ : κ => gaussianReal 0 1) := by
    rw [← hback, Measure.map_map e.continuous.measurable e.symm.continuous.measurable]
    have he : (⇑e ∘ ⇑e.symm) = id := by funext x; exact e.apply_symm_apply x
    rw [he, Measure.map_id]
  rw [← hm, ContinuousLinearEquiv.integral_id_map, integral_id_stdGaussian, map_zero]

/-- A Gaussian linear image with identity Gram matrix is standard, also in dimension zero. -/
lemma gaussian_linear_map_eq_standard_of_gram {κ : Type*} [Fintype κ] [DecidableEq κ]
    {n : ℕ} (L : (κ → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hgram : ∀ i j, ∑ k : κ, L (Pi.single k 1) i * L (Pi.single k 1) j =
      if i = j then 1 else 0) :
    (Measure.pi (fun _ : κ => gaussianReal 0 1)).map L =
      stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  let μ := Measure.pi (fun _ : κ => gaussianReal 0 1)
  haveI : IsGaussian μ := gaussian_pi_isGaussian
  have hL : HasGaussianLaw L μ := by
    simpa only [Function.comp_def, id_eq] using IsGaussian.hasGaussianLaw_id.map L
  let p (i : Fin n) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp (EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap
  have hm (i : Fin n) : (∫ x, L x i ∂μ) = 0 := by
    change (∫ x, (p i).comp L x ∂μ) = 0
    rw [((p i).comp L).integral_comp_id_comm IsGaussian.integrable_id,
      gaussian_pi_integral_id, map_zero]
  have hc (i j : Fin n) : (∫ x, L x i * L x j ∂μ) = if i = j then 1 else 0 := by
    have h := SlepianProof.gaussian_pi_covariance_linear
      ((EuclideanSpace.equiv (Fin n) ℝ).toContinuousLinearMap.comp L) i j
    change cov[fun x => L x i, fun x => L x j; μ] = _ at h
    have hi : MemLp (fun x => L x i) 2 μ := (hL.map (p i)).memLp_two
    have hj : MemLp (fun x => L x j) 2 μ := (hL.map (p j)).memLp_two
    rw [covariance_eq_sub hi hj, hm, hm, mul_zero, sub_zero] at h
    exact h.trans (hgram i j)
  exact gaussian_map_eq_standard L hL hm hc

abbrev TripleIndex (n : ℕ) := Fin n ⊕ (Fin n ⊕ Fin n)

def gaussianBlock0 (n : ℕ) : (TripleIndex n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.comp
    ({ toFun x i := x (Sum.inl i)
       map_add' _ _ := rfl
       map_smul' _ _ := rfl } : (TripleIndex n → ℝ) →L[ℝ] (Fin n → ℝ))

def gaussianBlock1 (n : ℕ) : (TripleIndex n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.comp
    ({ toFun x i := x (Sum.inr (Sum.inl i))
       map_add' _ _ := rfl
       map_smul' _ _ := rfl } : (TripleIndex n → ℝ) →L[ℝ] (Fin n → ℝ))

def gaussianBlock2 (n : ℕ) : (TripleIndex n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.comp
    ({ toFun x i := x (Sum.inr (Sum.inr i))
       map_add' _ _ := rfl
       map_smul' _ _ := rfl } : (TripleIndex n → ℝ) →L[ℝ] (Fin n → ℝ))

@[simp] lemma gaussianBlock0_single0 {n : ℕ} (i : Fin n) :
    gaussianBlock0 n (Pi.single (Sum.inl i) 1) = EuclideanSpace.basisFun (Fin n) ℝ i := by
  ext j; simp [gaussianBlock0, EuclideanSpace.basisFun_apply, Pi.single_apply]
@[simp] lemma gaussianBlock0_single1 {n : ℕ} (i : Fin n) :
    gaussianBlock0 n (Pi.single (Sum.inr (Sum.inl i)) 1) = 0 := by
  ext j; simp [gaussianBlock0, Pi.single_apply]
@[simp] lemma gaussianBlock0_single2 {n : ℕ} (i : Fin n) :
    gaussianBlock0 n (Pi.single (Sum.inr (Sum.inr i)) 1) = 0 := by
  ext j; simp [gaussianBlock0, Pi.single_apply]
@[simp] lemma gaussianBlock1_single0 {n : ℕ} (i : Fin n) :
    gaussianBlock1 n (Pi.single (Sum.inl i) 1) = 0 := by
  ext j; simp [gaussianBlock1, Pi.single_apply]
@[simp] lemma gaussianBlock1_single1 {n : ℕ} (i : Fin n) :
    gaussianBlock1 n (Pi.single (Sum.inr (Sum.inl i)) 1) = EuclideanSpace.basisFun (Fin n) ℝ i := by
  ext j; simp [gaussianBlock1, EuclideanSpace.basisFun_apply, Pi.single_apply]
@[simp] lemma gaussianBlock1_single2 {n : ℕ} (i : Fin n) :
    gaussianBlock1 n (Pi.single (Sum.inr (Sum.inr i)) 1) = 0 := by
  ext j; simp [gaussianBlock1, Pi.single_apply]
@[simp] lemma gaussianBlock2_single0 {n : ℕ} (i : Fin n) :
    gaussianBlock2 n (Pi.single (Sum.inl i) 1) = 0 := by
  ext j; simp [gaussianBlock2, Pi.single_apply]
@[simp] lemma gaussianBlock2_single1 {n : ℕ} (i : Fin n) :
    gaussianBlock2 n (Pi.single (Sum.inr (Sum.inl i)) 1) = 0 := by
  ext j; simp [gaussianBlock2, Pi.single_apply]
@[simp] lemma gaussianBlock2_single2 {n : ℕ} (i : Fin n) :
    gaussianBlock2 n (Pi.single (Sum.inr (Sum.inr i)) 1) = EuclideanSpace.basisFun (Fin n) ℝ i := by
  ext j; simp [gaussianBlock2, EuclideanSpace.basisFun_apply, Pi.single_apply]

lemma gaussianBlock0_map {n : ℕ} :
    (Measure.pi (fun _ : TripleIndex n => gaussianReal 0 1)).map (gaussianBlock0 n) =
      stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  apply gaussian_linear_map_eq_standard_of_gram
  intro i j
  simp [Fintype.sum_sum_type, EuclideanSpace.basisFun_apply, Pi.single_apply]

lemma gaussianBlock1_map {n : ℕ} :
    (Measure.pi (fun _ : TripleIndex n => gaussianReal 0 1)).map (gaussianBlock1 n) =
      stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  apply gaussian_linear_map_eq_standard_of_gram
  intro i j
  simp [Fintype.sum_sum_type, EuclideanSpace.basisFun_apply, Pi.single_apply]

lemma gaussianBlock2_map {n : ℕ} :
    (Measure.pi (fun _ : TripleIndex n => gaussianReal 0 1)).map (gaussianBlock2 n) =
      stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  apply gaussian_linear_map_eq_standard_of_gram
  intro i j
  simp [Fintype.sum_sum_type, EuclideanSpace.basisFun_apply, Pi.single_apply]

lemma gaussianBlock_rotation_map {n : ℕ} (θ : ℝ) :
    (Measure.pi (fun _ : TripleIndex n => gaussianReal 0 1)).map
      (Real.cos θ • gaussianBlock0 n + Real.sin θ • gaussianBlock1 n) =
      stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  apply gaussian_linear_map_eq_standard_of_gram
  intro i j
  simp only [Fintype.sum_sum_type, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, gaussianBlock0_single0, gaussianBlock0_single1,
    gaussianBlock0_single2, gaussianBlock1_single0, gaussianBlock1_single1,
    gaussianBlock1_single2, smul_zero, add_zero, zero_add]
  by_cases hij : i = j
  · subst j
    simpa [EuclideanSpace.basisFun_apply, Pi.single_apply, mul_ite, ite_mul, pow_two] using
      Real.cos_sq_add_sin_sq θ
  · simp [EuclideanSpace.basisFun_apply, Pi.single_apply, mul_ite, ite_mul, hij]

end

end GaussianConcentration

end

section

open MeasureTheory ProbabilityTheory

namespace GaussianConcentration

set_option maxHeartbeats 1200000

lemma gaussian_map_eq_standard_fintype {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : Type*} [MeasurableSpace Ω]
    {Prob : Measure Ω} [IsProbabilityMeasure Prob]
    (X : Ω → EuclideanSpace ℝ ι) (hX : HasGaussianLaw X Prob)
    (hm : ∀ i, ∫ ω, X ω i ∂Prob = 0)
    (hc : ∀ i j, ∫ ω, X ω i * X ω j ∂Prob = if i = j then 1 else 0) :
    Prob.map X = stdGaussian (EuclideanSpace ℝ ι) := by
  classical
  let μ := Prob.map X
  haveI : IsGaussian μ := hX.isGaussian_map
  let p (i : ι) : EuclideanSpace ℝ ι →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp (EuclideanSpace.equiv ι ℝ).toContinuousLinearMap
  have hmean : (∫ x, x ∂μ) = 0 := by
    ext i
    change p i (∫ x, x ∂μ) = 0
    rw [← (p i).integral_comp_id_comm IsGaussian.integrable_id,
      integral_map hX.aemeasurable (p i).continuous.aestronglyMeasurable]
    exact hm i
  have hmoment (i : ι) : MemLp (fun ω => X ω i) 2 Prob :=
    (hX.map (p i)).memLp_two
  have hcov (i j : ι) : cov[fun ω => X ω i, fun ω => X ω j; Prob] =
      if i = j then 1 else 0 := by
    rw [covariance_eq_sub (hmoment i) (hmoment j), hm, hm, mul_zero, sub_zero]
    exact hc i j
  have hrepr : (fun ω => WithLp.toLp 2 (fun i => X ω i)) = X := rfl
  have hmat : LinearMap.toMatrix₂ (EuclideanSpace.basisFun ι ℝ).toBasis
      (EuclideanSpace.basisFun ι ℝ).toBasis (covarianceBilin μ).toBilinForm =
        (1 : Matrix ι ι ℝ) := by
    ext i j
    simp only [LinearMap.toMatrix₂_apply, Matrix.one_apply]
    change covarianceBilin μ (EuclideanSpace.basisFun ι ℝ i)
      (EuclideanSpace.basisFun ι ℝ j) = if i = j then 1 else 0
    have h := covarianceBilin_apply_basisFun hmoment i j
    rw [hrepr] at h
    exact h.trans (hcov i j)
  change μ = stdGaussian (EuclideanSpace ℝ ι)
  rw [SlepianProof.gaussian_eq_multivariate_covariance μ, hmean, hmat,
    multivariateGaussian_zero_one]


lemma gaussian_linear_map_eq_standard_of_gram_fintype {κ : Type*} [Fintype κ] [DecidableEq κ]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (L : (κ → ℝ) →L[ℝ] EuclideanSpace ℝ ι)
    (hgram : ∀ i j, ∑ k : κ, L (Pi.single k 1) i * L (Pi.single k 1) j =
      if i = j then 1 else 0) :
    (Measure.pi (fun _ : κ => gaussianReal 0 1)).map L =
      stdGaussian (EuclideanSpace ℝ ι) := by
  let μ := Measure.pi (fun _ : κ => gaussianReal 0 1)
  haveI : IsGaussian μ := gaussian_pi_isGaussian
  have hL : HasGaussianLaw L μ := by
    simpa only [Function.comp_def, id_eq] using IsGaussian.hasGaussianLaw_id.map L
  let p (i : ι) : EuclideanSpace ℝ ι →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp (EuclideanSpace.equiv ι ℝ).toContinuousLinearMap
  have hm (i : ι) : (∫ x, L x i ∂μ) = 0 := by
    change (∫ x, (p i).comp L x ∂μ) = 0
    rw [((p i).comp L).integral_comp_id_comm IsGaussian.integrable_id,
      gaussian_pi_integral_id, map_zero]
  have hc (i j : ι) : (∫ x, L x i * L x j ∂μ) = if i = j then 1 else 0 := by
    have h := SlepianProof.gaussian_pi_covariance_linear
      ((EuclideanSpace.equiv ι ℝ).toContinuousLinearMap.comp L) i j
    change cov[fun x => L x i, fun x => L x j; μ] = _ at h
    have hi : MemLp (fun x => L x i) 2 μ := (hL.map (p i)).memLp_two
    have hj : MemLp (fun x => L x j) 2 μ := (hL.map (p j)).memLp_two
    rw [covariance_eq_sub hi hj, hm, hm, mul_zero, sub_zero] at h
    exact h.trans (hgram i j)
  exact gaussian_map_eq_standard_fintype L hL hm hc


end GaussianConcentration

end

section

open MeasureTheory ProbabilityTheory

namespace GaussianConcentration

set_option maxHeartbeats 1200000

noncomputable section

abbrev GaussianPairIndex (n : ℕ) := Fin n ⊕ Fin n

def gaussianPairRotation (n : ℕ) (θ : ℝ) :
    (GaussianPairIndex n → ℝ) →L[ℝ] (GaussianPairIndex n → ℝ) where
  toFun x := Sum.elim
    (fun i => Real.cos θ * x (Sum.inl i) + Real.sin θ * x (Sum.inr i))
    (fun i => -Real.sin θ * x (Sum.inl i) + Real.cos θ * x (Sum.inr i))
  map_add' x y := by ext i; cases i <;> simp [mul_add] <;> ring
  map_smul' c x := by ext i; cases i <;> simp [smul_eq_mul] <;> ring
  cont := by
    apply continuous_pi
    intro i
    cases i <;> dsimp <;> fun_prop

lemma gaussianPairRotation_measurePreserving (n : ℕ) (θ : ℝ) :
    MeasurePreserving (gaussianPairRotation n θ)
      (Measure.pi (fun _ : GaussianPairIndex n => gaussianReal 0 1))
      (Measure.pi (fun _ : GaussianPairIndex n => gaussianReal 0 1)) := by
  let e := EuclideanSpace.equiv (GaussianPairIndex n) ℝ
  let L := e.symm.toContinuousLinearMap.comp (gaussianPairRotation n θ)
  have hg (i j : GaussianPairIndex n) :
      (∑ k : GaussianPairIndex n, L (Pi.single k 1) i * L (Pi.single k 1) j) =
        if i = j then 1 else 0 := by
    change (∑ k : GaussianPairIndex n, gaussianPairRotation n θ (Pi.single k 1) i *
      gaussianPairRotation n θ (Pi.single k 1) j) = if i = j then 1 else 0
    rcases i with i | i <;> rcases j with j | j <;> by_cases hij : i = j
    all_goals simp [gaussianPairRotation, Fintype.sum_sum_type, Pi.single_apply,
      mul_ite, ite_mul, hij]
    all_goals nlinarith [Real.cos_sq_add_sin_sq θ]
  have hL := gaussian_linear_map_eq_standard_of_gram_fintype L hg
  have he : (stdGaussian (EuclideanSpace ℝ (GaussianPairIndex n))).map e =
      Measure.pi (fun _ : GaussianPairIndex n => gaussianReal 0 1) := by
    have hback : (Measure.pi (fun _ : GaussianPairIndex n => gaussianReal 0 1)).map e.symm =
        stdGaussian (EuclideanSpace ℝ (GaussianPairIndex n)) := map_pi_eq_stdGaussian
    rw [← hback, Measure.map_map e.continuous.measurable e.symm.continuous.measurable]
    have heq : (⇑e ∘ ⇑e.symm) = id := by funext x; exact e.apply_symm_apply x
    rw [heq, Measure.map_id]
  refine ⟨(gaussianPairRotation n θ).continuous.measurable, ?_⟩
  have hafter := congrArg (fun μ => μ.map e) hL
  rw [Measure.map_map e.continuous.measurable L.continuous.measurable] at hafter
  have heq : (⇑e ∘ ⇑L) = ⇑(gaussianPairRotation n θ) := by
    funext x
    exact e.apply_symm_apply (gaussianPairRotation n θ x)
  rw [heq, he] at hafter
  exact hafter

def gaussianPairMap (n : ℕ) (x : GaussianPairIndex n → ℝ) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
  ((EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => x (Sum.inl i)),
   (EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => x (Sum.inr i)))

lemma gaussianPairMap_measurePreserving (n : ℕ) :
    MeasurePreserving (gaussianPairMap n)
      (Measure.pi (fun _ : GaussianPairIndex n => gaussianReal 0 1))
      ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
  let e := (EuclideanSpace.equiv (Fin n) ℝ).symm
  have he : MeasurePreserving e (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := ⟨e.continuous.measurable, map_pi_eq_stdGaussian⟩
  exact (he.prod he).comp (measurePreserving_sumPiEquivProdPi
    (fun _ : GaussianPairIndex n => gaussianReal 0 1))

def gaussianProductRotation (n : ℕ) (θ : ℝ)
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
  (Real.cos θ • p.1 + Real.sin θ • p.2,
   -Real.sin θ • p.1 + Real.cos θ • p.2)

lemma gaussianProductRotation_measurePreserving (n : ℕ) (θ : ℝ) :
    MeasurePreserving (gaussianProductRotation n θ)
      ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin n))))
      ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
  have hp := gaussianPairMap_measurePreserving n
  have hr := gaussianPairRotation_measurePreserving n θ
  have ht : Continuous (gaussianProductRotation n θ) := by
    unfold gaussianProductRotation
    fun_prop
  have he : gaussianProductRotation n θ ∘ gaussianPairMap n =
      gaussianPairMap n ∘ gaussianPairRotation n θ := by
    funext x
    apply Prod.ext
    · ext i
      simp [gaussianProductRotation, gaussianPairMap, gaussianPairRotation]
    · ext i
      simp [gaussianProductRotation, gaussianPairMap, gaussianPairRotation]
  refine ⟨ht.measurable, ?_⟩
  rw [← hp.map_eq, Measure.map_map ht.measurable hp.measurable, he,
    ← Measure.map_map hp.measurable hr.measurable, hr.map_eq, hp.map_eq]

end

end GaussianConcentration

end

section

open MeasureTheory

namespace GaussianConcentration

set_option maxHeartbeats 1000000

lemma convex_nonconstant_exists_gt_at_zero {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) (hn : ¬ ∀ x, φ x = φ 0) :
    ∃ a, φ 0 < φ a := by
  by_contra! h
  apply hn
  intro x
  have hm := hφ.2 (Set.mem_univ x) (Set.mem_univ (-x))
    (show (0 : ℝ) ≤ 1/2 by norm_num) (show (0 : ℝ) ≤ 1/2 by norm_num)
    (show (1 : ℝ)/2 + 1/2 = 1 by norm_num)
  simp only [smul_eq_mul] at hm
  have he : (1 : ℝ)/2*x + 1/2*(-x) = 0 := by ring
  rw [he] at hm
  have hx := h x
  have hnx := h (-x)
  linarith

lemma convex_positive_point_abs_bound {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) {a : ℝ} (ha : 0 < a) (hpa : φ 0 < φ a) :
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧
      ∀ x, |x| ≤ A * (|φ x| + |φ (-x)|) + B := by
  let d := φ a - φ 0
  have hd : 0 < d := sub_pos.mpr hpa
  refine ⟨a/d, a + a/d * |φ 0|, div_pos ha hd, by positivity, ?_⟩
  intro x
  have hp : φ |x| ≤ |φ x| + |φ (-x)| := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
      linarith [le_abs_self (φ x), abs_nonneg (φ (-x))]
    · rw [abs_of_neg (lt_of_not_ge hx)]
      linarith [le_abs_self (φ (-x)), abs_nonneg (φ x)]
  by_cases hx : |x| ≤ a
  · have h₁ : 0 ≤ a/d * (|φ x| + |φ (-x)|) := by positivity
    have h₂ : 0 ≤ a/d * |φ 0| := by positivity
    linarith
  · have hs := hφ.secant_mono_aux1 (Set.mem_univ (0 : ℝ)) (Set.mem_univ |x|)
      ha (lt_of_not_ge hx)
    simp only [sub_zero] at hs
    have hp' := mul_le_mul_of_nonneg_left hp ha.le
    have hzero := le_abs_self (-φ 0)
    rw [abs_neg] at hzero
    have hz := mul_le_mul_of_nonneg_left hzero ha.le
    have hg : |x| * d ≤ a * (|φ x| + |φ (-x)| + |φ 0|) := by
      dsimp [d]
      nlinarith
    calc
      |x| ≤ a * (|φ x| + |φ (-x)| + |φ 0|) / d := (le_div_iff₀ hd).mpr hg
      _ = a/d * (|φ x| + |φ (-x)|) + a/d * |φ 0| := by ring
      _ ≤ a/d * (|φ x| + |φ (-x)|) + (a + a/d * |φ 0|) := by linarith

/-- Every nonconstant convex test controls absolute magnitude when tested in both signs. -/
lemma convex_nonconstant_abs_bound {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) (hn : ¬ ∀ x, φ x = φ 0) :
    ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧
      ∀ x, |x| ≤ A * (|φ x| + |φ (-x)|) + B := by
  obtain ⟨a, ha⟩ := convex_nonconstant_exists_gt_at_zero hφ hn
  have hne : a ≠ 0 := by intro h; simpa [h] using ha
  rcases lt_or_gt_of_ne hne with han | hap
  · let ψ := fun x => φ (-x)
    have hψ : ConvexOn ℝ Set.univ ψ := by
      simpa only [Set.preimage_univ, Function.comp_def, LinearMap.neg_apply, LinearMap.id_apply]
        using hφ.comp_linearMap (-(LinearMap.id : ℝ →ₗ[ℝ] ℝ))
    have hp : ψ 0 < ψ (-a) := by simpa [ψ] using ha
    obtain ⟨A, B, hA, hB, h⟩ := convex_positive_point_abs_bound hψ (neg_pos.mpr han) hp
    refine ⟨A, B, hA, hB, ?_⟩
    intro x
    simpa only [ψ, neg_neg, add_comm] using h x
  · exact convex_positive_point_abs_bound hφ hap ha

/-- In the Gaussian application, reflection of the independent Gaussian direction supplies
integrability of the negative-sign test from the native positive-sign test. -/
lemma integrable_of_two_convex_tests {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hm : AEStronglyMeasurable Z μ) {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) (hn : ¬ ∀ x, φ x = φ 0)
    (hp : Integrable (fun ω => φ (Z ω)) μ)
    (hnint : Integrable (fun ω => φ (-Z ω)) μ) : Integrable Z μ := by
  obtain ⟨A, B, hA, hB, hbound⟩ := convex_nonconstant_abs_bound hφ hn
  apply (((hp.norm.add hnint.norm).const_mul A).add (integrable_const B)).mono' hm
  filter_upwards [] with ω
  simpa only [Pi.add_apply, Pi.mul_apply, Pi.ofNat_apply, Real.norm_eq_abs] using hbound (Z ω)

end GaussianConcentration

end

section

open MeasureTheory ProbabilityTheory

namespace GaussianConcentration

set_option maxHeartbeats 1200000

lemma gaussian_direction_integrable_of_convex_test {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) (hn : ¬ ∀ x, φ x = φ 0)
    (hi : Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        φ (Real.pi / 2 * fderiv ℝ f p.1 p.2))
      ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin n))))) :
    Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        fderiv ℝ f p.1 p.2)
      ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let Z := fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
    Real.pi / 2 * fderiv ℝ f p.1 p.2
  have hm : Measurable Z :=
    (ContinuousLinearMap.measurable_apply₂.comp
      (((measurable_fderiv ℝ f).comp measurable_fst).prodMk measurable_snd)).const_mul _
  have hneg : MeasurePreserving (fun x : EuclideanSpace ℝ (Fin n) => -x) γ γ :=
    ⟨continuous_neg.measurable, stdGaussian_map (LinearIsometryEquiv.neg ℝ)⟩
  have hid : MeasurePreserving (id : EuclideanSpace ℝ (Fin n) → _) γ γ :=
    ⟨measurable_id, Measure.map_id⟩
  have hflip := hid.prod hneg
  have hnint : Integrable (fun p => φ (-Z p)) (γ.prod γ) := by
    have h := hflip.integrable_comp_of_integrable hi
    simpa only [Function.comp_def, Prod.map, id_eq, Z, map_neg, mul_neg] using h
  have hZI := integrable_of_two_convex_tests (γ.prod γ) hm.aestronglyMeasurable
    hφ hn hi hnint
  have hc : Real.pi / 2 ≠ 0 := ne_of_gt (by positivity)
  simpa only [Z, mul_div_cancel_left₀ _ hc] using hZI.div_const (Real.pi/2)

/-- The whole Gaussian pair is invariant under rotation, including joint directional tests. -/
lemma gaussian_direction_rotation_integral {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : ℝ → ℝ) (θ : ℝ)
    (hi : Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        g (fderiv ℝ f p.1 p.2))
      ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin n))))) :
    (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      g (fderiv ℝ f (Real.cos θ • p.1 + Real.sin θ • p.2)
        (-Real.sin θ • p.1 + Real.cos θ • p.2))
      ∂((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin n))))) =
    ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      g (fderiv ℝ f p.1 p.2)
      ∂((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let H := fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
    g (fderiv ℝ f p.1 p.2)
  have hR := gaussianProductRotation_measurePreserving n θ
  have hm : AEStronglyMeasurable H ((γ.prod γ).map (gaussianProductRotation n θ)) := by
    rw [hR.map_eq]
    exact hi.aestronglyMeasurable
  have he := integral_map (μ := γ.prod γ) hR.measurable.aemeasurable hm
  rw [hR.map_eq] at he
  exact he.symm

end GaussianConcentration

end

section

open MeasureTheory Filter
open scoped Topology

namespace GaussianConcentration

/-- Integrability of independent differences entails integrability of the observable itself.
This removes an implicit integrability requirement in the native interpolation milestone. -/
lemma integrable_of_integrable_independent_difference {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ}
    (hd : Integrable (fun p : α × α => f p.1 - f p.2) (μ.prod μ)) :
    Integrable f μ := by
  obtain ⟨y, hy⟩ := hd.prod_left_ae.exists
  have h := hy.add (integrable_const (f y) (μ := μ))
  change Integrable (fun x => (f x - f y) + f y) μ at h
  simpa only [sub_add_cancel] using h

/-- Jensen over an independent copy compares a centered observable with its difference.
The product integrability premise will be obtained from the rotation inequality, rather
than added to the final native interpolation theorem. -/
lemma convex_symmetrization {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ} (hf : Integrable f μ)
    {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ)
    (hc : Integrable (fun x => φ (f x - ∫ y, f y ∂μ)) μ)
    (hd : Integrable (fun p : α × α => φ (f p.1 - f p.2)) (μ.prod μ)) :
    (∫ x, φ (f x - ∫ y, f y ∂μ) ∂μ) ≤
      ∫ p : α × α, φ (f p.1 - f p.2) ∂(μ.prod μ) := by
  rw [integral_prod _ hd]
  apply integral_mono_ae hc hd.integral_prod_left
  filter_upwards [hd.prod_right_ae] with x hx
  have hmean : (∫ y, f x - f y ∂μ) = f x - ∫ y, f y ∂μ := by
    rw [integral_sub (integrable_const _) hf]
    simp
  have hj := hφ.map_integral_le (hφ.continuousOn isOpen_univ) isClosed_univ
    (ae_of_all μ fun _ => Set.mem_univ _) ((integrable_const (f x)).sub hf) hx
  change φ (∫ y, f x - f y ∂μ) ≤ ∫ y, φ (f x - f y) ∂μ at hj
  rw [hmean] at hj
  exact hj

end GaussianConcentration

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace GaussianConcentration

set_option maxHeartbeats 1400000

lemma differentiable_rotation_hasDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : Differentiable ℝ f) (x y : E) (θ : ℝ) :
    HasDerivAt (fun t => f (Real.cos t • x + Real.sin t • y))
      (fderiv ℝ f (Real.cos θ • x + Real.sin θ • y)
        (-Real.sin θ • x + Real.cos θ • y)) θ := by
  exact (hf _).hasFDerivAt.comp_hasDerivAt θ
    (((Real.hasDerivAt_cos θ).smul_const x).add ((Real.hasDerivAt_sin θ).smul_const y))

/-- Only differentiability and integrability of the directional derivative are needed;
no continuous derivative hypothesis replaces the native milestone's hypothesis. -/
lemma differentiable_rotation_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : Differentiable ℝ f) (x y : E)
    (hi : IntervalIntegrable (fun θ => fderiv ℝ f (Real.cos θ • x + Real.sin θ • y)
      (-Real.sin θ • x + Real.cos θ • y)) volume 0 (Real.pi/2)) :
    (∫ θ in (0 : ℝ)..Real.pi/2, fderiv ℝ f (Real.cos θ • x + Real.sin θ • y)
      (-Real.sin θ • x + Real.cos θ • y)) = f y - f x := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => differentiable_rotation_hasDerivAt hf x y θ) hi
  simpa only [Real.cos_pi_div_two, Real.sin_pi_div_two, zero_smul, one_smul,
    zero_add, Real.cos_zero, Real.sin_zero, add_zero] using h

/-- Rotation and Fubini derive Gaussian integrability of f from that of its derivative.
This is a conclusion, not a new assumption on the final interpolation theorem. -/
lemma gaussian_differentiable_integrable_of_direction_integrable {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Differentiable ℝ f)
    (hd : Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        fderiv ℝ f p.1 p.2)
      ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin n))))) :
    Integrable f (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let σ := γ.prod γ
  let ν := volume.restrict (Set.Icc (0 : ℝ) (Real.pi/2))
  have hpi : 0 ≤ Real.pi/2 := by positivity
  haveI : IsFiniteMeasure ν := by
    constructor
    simp [ν, Real.volume_Icc]
  let F := fun q : ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
    fderiv ℝ f (Real.cos q.1 • q.2.1 + Real.sin q.1 • q.2.2)
      (-Real.sin q.1 • q.2.1 + Real.cos q.1 • q.2.2)
  have hm : Measurable F := by
    have hx : Continuous (fun q : ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
        Real.cos q.1 • q.2.1 + Real.sin q.1 • q.2.2) := by fun_prop
    have hy : Continuous (fun q : ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
        -Real.sin q.1 • q.2.1 + Real.cos q.1 • q.2.2) := by fun_prop
    exact ContinuousLinearMap.measurable_apply₂.comp
      (((measurable_fderiv ℝ f).comp hx.measurable).prodMk hy.measurable)
  have hsection (θ : ℝ) : Integrable (fun p => F (θ, p)) σ :=
    (gaussianProductRotation_measurePreserving n θ).integrable_comp_of_integrable hd
  have hnorm (θ : ℝ) : (∫ p, ‖F (θ, p)‖ ∂σ) =
      ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        ‖fderiv ℝ f p.1 p.2‖ ∂σ := gaussian_direction_rotation_integral f norm θ hd.norm
  have hF : Integrable F (ν.prod σ) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ hsection, ?_⟩
    simpa only [hnorm] using integrable_const
      (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        ‖fderiv ℝ f p.1 p.2‖ ∂σ) (μ := ν)
  have he : (fun p => ∫ θ, F (θ, p) ∂ν) =ᵐ[σ] (fun p => f p.2 - f p.1) := by
    filter_upwards [hF.prod_left_ae] with p hp
    have hint : IntervalIntegrable (fun θ => F (θ, p)) volume 0 (Real.pi/2) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hpi).mpr hp
    have h := differentiable_rotation_integral hf p.1 p.2 hint
    rw [intervalIntegral.integral_of_le hpi, ← integral_Icc_eq_integral_Ioc] at h
    exact h
  have hdiff : Integrable (fun p => f p.1 - f p.2) σ := by
    have h := (hF.integral_prod_right.congr he).neg
    change Integrable (fun p => -(f p.2 - f p.1)) σ at h
    simpa only [neg_sub] using h
  exact integrable_of_integrable_independent_difference γ hdiff

end GaussianConcentration

end

section

open MeasureTheory ProbabilityTheory

namespace GaussianConcentration

set_option maxHeartbeats 1200000

/-- Rotation makes every directional test's absolute integral constant in the angle.
Fubini therefore applies on any finite angle measure. -/
lemma gaussian_rotation_test_integrable {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (g : ℝ → ℝ) (hg : Measurable g)
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hi : Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        g (fderiv ℝ f p.1 p.2))
      ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin n))))) :
    Integrable
      (fun q : ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
        g (fderiv ℝ f (Real.cos q.1 • q.2.1 + Real.sin q.1 • q.2.2)
          (-Real.sin q.1 • q.2.1 + Real.cos q.1 • q.2.2)))
      (ν.prod ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin n))))) := by
  let σ := (stdGaussian (EuclideanSpace ℝ (Fin n))).prod
    (stdGaussian (EuclideanSpace ℝ (Fin n)))
  let F := fun q : ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
    g (fderiv ℝ f (Real.cos q.1 • q.2.1 + Real.sin q.1 • q.2.2)
      (-Real.sin q.1 • q.2.1 + Real.cos q.1 • q.2.2))
  have hm : Measurable F := by
    have hx : Continuous (fun q : ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
        Real.cos q.1 • q.2.1 + Real.sin q.1 • q.2.2) := by fun_prop
    have hy : Continuous (fun q : ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
        -Real.sin q.1 • q.2.1 + Real.cos q.1 • q.2.2) := by fun_prop
    exact hg.comp (ContinuousLinearMap.measurable_apply₂.comp
      (((measurable_fderiv ℝ f).comp hx.measurable).prodMk hy.measurable))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun θ =>
    (gaussianProductRotation_measurePreserving n θ).integrable_comp_of_integrable hi), ?_⟩
  have hn (θ : ℝ) : (∫ p, ‖F (θ, p)‖ ∂σ) =
      ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        ‖g (fderiv ℝ f p.1 p.2)‖ ∂σ :=
    gaussian_direction_rotation_integral f (fun x => ‖g x‖) θ hi.norm
  change Integrable (fun θ => ∫ p, ‖F (θ, p)‖ ∂σ) ν
  simpa only [hn] using integrable_const
    (∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      ‖g (fderiv ℝ f p.1 p.2)‖ ∂σ) (μ := ν)

end GaussianConcentration

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace GaussianConcentration

set_option maxHeartbeats 1600000

noncomputable def gaussianAngleMeasure : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) (Real.pi/2))

instance : IsFiniteMeasure gaussianAngleMeasure := by
  constructor
  simp [gaussianAngleMeasure, Real.volume_Icc]

@[simp] lemma gaussianAngleMeasure_real_univ : gaussianAngleMeasure.real Set.univ = Real.pi/2 := by
  simp [gaussianAngleMeasure, measureReal_def, Real.volume_Icc,
    ENNReal.toReal_ofReal (show 0 ≤ Real.pi/2 by positivity)]

instance : NeZero gaussianAngleMeasure := by
  constructor
  intro h
  have hz : gaussianAngleMeasure.real Set.univ = 0 := by rw [h]; simp
  rw [gaussianAngleMeasure_real_univ] at hz
  linarith [Real.pi_pos]

/-- The angle Jensen inequality supplies an integrable upper bound for a difference test.
Its expectation is exactly the native directional-test expectation. -/
lemma gaussian_rotation_jensen_upper {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Differentiable ℝ f) {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ)
    (hd : Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => fderiv ℝ f p.1 p.2)
      ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod (stdGaussian (EuclideanSpace ℝ (Fin n)))))
    (hi : Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        φ (Real.pi/2 * fderiv ℝ f p.1 p.2))
      ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod (stdGaussian (EuclideanSpace ℝ (Fin n))))) :
    ∃ U : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ,
      Integrable U ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin n)))) ∧
      (∀ᵐ p ∂((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin n)))), φ (f p.2 - f p.1) ≤ U p) ∧
      (∫ p, U p ∂((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin n))))) =
      ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        φ (Real.pi/2 * fderiv ℝ f p.1 p.2)
        ∂((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
          (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
  let σ := (stdGaussian (EuclideanSpace ℝ (Fin n))).prod
    (stdGaussian (EuclideanSpace ℝ (Fin n)))
  let c := Real.pi/2
  let ν := gaussianAngleMeasure
  let D := fun θ (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
    fderiv ℝ f (Real.cos θ • p.1 + Real.sin θ • p.2)
      (-Real.sin θ • p.1 + Real.cos θ • p.2)
  let H := fun q : ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
    φ (c * D q.1 q.2)
  let U := fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
    ⨍ θ, φ (c * D θ p) ∂ν
  have hc : 0 < c := by positivity
  have hD : Integrable (fun q : ℝ × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) =>
      D q.1 q.2) (ν.prod σ) :=
    gaussian_rotation_test_integrable f id measurable_id ν hd
  have hφm : Measurable (fun t : ℝ => φ (c*t)) :=
    ((continuousOn_univ.mp (hφ.continuousOn isOpen_univ)).comp
      (continuous_const.mul continuous_id)).measurable
  have hH : Integrable H (ν.prod σ) := gaussian_rotation_test_integrable f _ hφm ν hi
  have hUeq : U = fun p => c⁻¹ * ∫ θ, H (θ, p) ∂ν := by
    funext p
    dsimp only [U]
    rw [average_eq, gaussianAngleMeasure_real_univ]
    rfl
  have hUi : Integrable U σ := by
    rw [hUeq]
    exact hH.integral_prod_right.const_mul _
  refine ⟨U, hUi, ?_, ?_⟩
  · filter_upwards [hD.prod_left_ae, hH.prod_left_ae] with p hDp hHp
    have hint : IntervalIntegrable (fun θ => D θ p) volume 0 (Real.pi/2) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hc.le).mpr hDp
    have hFTC := differentiable_rotation_integral hf p.1 p.2 hint
    rw [intervalIntegral.integral_of_le hc.le, ← integral_Icc_eq_integral_Ioc] at hFTC
    have he : (∫ θ, D θ p ∂ν) = f p.2 - f p.1 := hFTC
    have hmean : (⨍ θ, c * D θ p ∂ν) = f p.2 - f p.1 := by
      rw [average_eq, gaussianAngleMeasure_real_univ, integral_const_mul, smul_eq_mul]
      change c⁻¹ * (c * ∫ θ, D θ p ∂ν) = _
      rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul, he]
    have hj := hφ.map_average_le (hφ.continuousOn isOpen_univ) isClosed_univ
      (ae_of_all ν fun _ => Set.mem_univ _) (hDp.const_mul c) hHp
    change φ (⨍ θ, c * D θ p ∂ν) ≤ U p at hj
    rw [hmean] at hj
    exact hj
  · change (∫ p, U p ∂σ) = _
    rw [hUeq, integral_const_mul, ← integral_integral_swap hH]
    have hr (θ : ℝ) : (∫ p, H (θ, p) ∂σ) =
        ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          φ (c * fderiv ℝ f p.1 p.2) ∂σ :=
      gaussian_direction_rotation_integral f (fun t => φ (c*t)) θ hi
    simp_rw [hr]
    rw [integral_const, gaussianAngleMeasure_real_univ, smul_eq_mul]
    change c⁻¹ * (c * _) = _
    rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

end GaussianConcentration

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace GaussianConcentration

set_option maxHeartbeats 1600000

lemma convex_abs_le_of_two_upper_bounds {φ : ℝ → ℝ}
    (hφ : ConvexOn ℝ Set.univ φ) {z A B : ℝ}
    (hA : φ z ≤ A) (hB : φ (-z) ≤ B) :
    |φ z| ≤ |A| + |B| + 2 * |φ 0| := by
  have hm := hφ.2 (Set.mem_univ z) (Set.mem_univ (-z))
    (show (0 : ℝ) ≤ 1/2 by norm_num) (show (0 : ℝ) ≤ 1/2 by norm_num)
    (show (1 : ℝ)/2 + 1/2 = 1 by norm_num)
  simp only [smul_eq_mul] at hm
  have he : (1 : ℝ)/2*z + 1/2*(-z) = 0 := by ring
  rw [he] at hm
  apply abs_le.mpr
  constructor <;> linarith [le_abs_self A, le_abs_self B, neg_abs_le (φ 0),
    abs_nonneg A, abs_nonneg B, abs_nonneg (φ 0)]

lemma convex_difference_integrable_of_upper {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] {f : α → ℝ} (hf : Measurable f)
    {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) {U : α × α → ℝ}
    (hU : Integrable U (μ.prod μ))
    (hu : ∀ᵐ p ∂(μ.prod μ), φ (f p.2 - f p.1) ≤ U p) :
    Integrable (fun p : α × α => φ (f p.2 - f p.1)) (μ.prod μ) ∧
      Integrable (fun p : α × α => φ (f p.1 - f p.2)) (μ.prod μ) := by
  have hs := Measure.measurePreserving_swap (μ := μ) (ν := μ)
  have hUs := hs.integrable_comp_of_integrable hU
  have hus := hs.quasiMeasurePreserving.ae hu
  have hc : Continuous φ := continuousOn_univ.mp (hφ.continuousOn isOpen_univ)
  have hm : Measurable (fun p : α × α => φ (f p.2 - f p.1)) :=
    hc.measurable.comp ((hf.comp measurable_snd).sub (hf.comp measurable_fst))
  have hi : Integrable (fun p : α × α => φ (f p.2 - f p.1)) (μ.prod μ) := by
    apply ((hU.norm.add hUs.norm).add (integrable_const (2*|φ 0|))).mono' hm.aestronglyMeasurable
    filter_upwards [hu, hus] with p hp hps
    change ‖φ (f p.2 - f p.1)‖ ≤ ‖U p‖ + ‖U (Prod.swap p)‖ + 2 * |φ 0|
    have hb : φ (-(f p.2 - f p.1)) ≤ U (Prod.swap p) := by
      simpa only [Prod.swap, neg_sub] using hps
    simpa only [Real.norm_eq_abs] using convex_abs_le_of_two_upper_bounds hφ hp hb
  refine ⟨hi, ?_⟩
  have h := hs.integrable_comp_of_integrable hi
  exact h

/-- The exact convex Gaussian interpolation inequality on standard Gaussian measure.
All integrability of f and of independent differences is derived from the test assumptions. -/
lemma gaussian_convex_interpolation_standard {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Differentiable ℝ f)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ)
    (hc : Integrable (fun x => φ (f x - ∫ y, f y ∂stdGaussian (EuclideanSpace ℝ (Fin n))))
      (stdGaussian (EuclideanSpace ℝ (Fin n))))
    (hi : Integrable
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        φ (Real.pi/2 * fderiv ℝ f p.1 p.2))
      ((stdGaussian (EuclideanSpace ℝ (Fin n))).prod (stdGaussian (EuclideanSpace ℝ (Fin n))))) :
    (∫ x, φ (f x - ∫ y, f y ∂stdGaussian (EuclideanSpace ℝ (Fin n)))
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
    ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      φ (Real.pi/2 * fderiv ℝ f p.1 p.2)
      ∂((stdGaussian (EuclideanSpace ℝ (Fin n))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin n)))) := by
  by_cases hn : ∀ x, φ x = φ 0
  · simp only [hn]
    simp
  · let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
    have hd := gaussian_direction_integrable_of_convex_test f hφ hn hi
    have hfi := gaussian_differentiable_integrable_of_direction_integrable f hf hd
    obtain ⟨U, hUi, hu, hmean⟩ := gaussian_rotation_jensen_upper f hf hφ hd hi
    obtain ⟨hr, hl⟩ := convex_difference_integrable_of_upper γ hf.continuous.measurable hφ hUi hu
    have hs := convex_symmetrization γ hfi hφ hc hl
    calc
      _ ≤ ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          φ (f p.1 - f p.2) ∂γ.prod γ := hs
      _ = ∫ p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
          φ (f p.2 - f p.1) ∂γ.prod γ := by
        exact integral_prod_swap (μ := γ) (ν := γ) (fun p => φ (f p.2 - f p.1))
      _ ≤ ∫ p, U p ∂γ.prod γ := integral_mono_ae hr hUi hu
      _ = _ := hmean

end GaussianConcentration

end

open MeasureTheory ProbabilityTheory

theorem solution {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω}
    [IsProbabilityMeasure Prob] (X Y : Ω → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Differentiable ℝ f)
    (hXGauss : HasGaussianLaw X Prob) (hYGauss : HasGaussianLaw Y Prob)
    (hIndep : IndepFun X Y Prob)
    (hXmean : ∀ i, ∫ ω, X ω i ∂Prob = 0) (hYmean : ∀ i, ∫ ω, Y ω i ∂Prob = 0)
    (hXcov : ∀ i j, ∫ ω, X ω i * X ω j ∂Prob = if i = j then 1 else 0)
    (hYcov : ∀ i j, ∫ ω, Y ω i * Y ω j ∂Prob = if i = j then 1 else 0)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ)
    (hInt1 : Integrable (fun ω => φ (f (X ω) - ∫ ω', f (X ω') ∂Prob)) Prob)
    (hInt2 : Integrable (fun ω => φ (Real.pi / 2 * fderiv ℝ f (X ω) (Y ω))) Prob) :
    ∫ ω, φ (f (X ω) - ∫ ω', f (X ω') ∂Prob) ∂Prob ≤
      ∫ ω, φ (Real.pi / 2 * fderiv ℝ f (X ω) (Y ω)) ∂Prob := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  have hXL := GaussianConcentration.gaussian_map_eq_standard X hXGauss hXmean hXcov
  have hYL := GaussianConcentration.gaussian_map_eq_standard Y hYGauss hYmean hYcov
  have hpair : Prob.map (fun ω => (X ω, Y ω)) = γ.prod γ := by
    simpa only [hXL, hYL] using
      hIndep.map_prod_eq_prod_map_map hXGauss.aemeasurable hYGauss.aemeasurable
  have hpairm : AEMeasurable (fun ω => (X ω, Y ω)) Prob :=
    hXGauss.aemeasurable.prodMk hYGauss.aemeasurable
  have hmean : (∫ ω, f (X ω) ∂Prob) = ∫ x, f x ∂γ := by
    have h := integral_map (μ := Prob) hXGauss.aemeasurable hf.continuous.aestronglyMeasurable
    rw [hXL] at h
    exact h.symm
  have hφc : Continuous φ := continuousOn_univ.mp (hφ.continuousOn isOpen_univ)
  let C := fun x => φ (f x - ∫ y, f y ∂γ)
  have hC : Continuous C := hφc.comp (hf.continuous.sub continuous_const)
  have hCi : Integrable C (Prob.map X) :=
    (integrable_map_measure hC.aestronglyMeasurable hXGauss.aemeasurable).mpr
      (by simpa only [C, Function.comp_def, hmean] using hInt1)
  have hcγ : Integrable C γ := by simpa only [hXL] using hCi
  let G := fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
    φ (Real.pi/2 * fderiv ℝ f p.1 p.2)
  have hG : Measurable G := hφc.measurable.comp
    ((ContinuousLinearMap.measurable_apply₂.comp
      (((measurable_fderiv ℝ f).comp measurable_fst).prodMk measurable_snd)).const_mul _)
  have hGi : Integrable G (Prob.map (fun ω => (X ω, Y ω))) :=
    (integrable_map_measure hG.aestronglyMeasurable hpairm).mpr
      (by simpa only [G, Function.comp_def] using hInt2)
  have hiγ : Integrable G (γ.prod γ) := by rw [← hpair]; exact hGi
  have heC := integral_map (μ := Prob) hXGauss.aemeasurable hC.aestronglyMeasurable
  rw [hXL] at heC
  have heG := integral_map (μ := Prob) hpairm hG.aestronglyMeasurable
  rw [hpair] at heG
  rw [hmean]
  change (∫ ω, C (X ω) ∂Prob) ≤ ∫ ω, G (X ω, Y ω) ∂Prob
  calc
    _ = ∫ x, C x ∂γ := heC.symm
    _ ≤ ∫ p, G p ∂γ.prod γ :=
      GaussianConcentration.gaussian_convex_interpolation_standard f hf φ hφ hcγ hiγ
    _ = _ := heG

#print axioms solution
