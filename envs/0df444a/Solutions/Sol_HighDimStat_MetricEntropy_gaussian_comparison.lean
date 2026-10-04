-- Prove2me | solution 1 for HighDimStat.MetricEntropy.gaussian_comparison
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-02T14:15:00.537972+00:00
-- url     : https://prove2.me/submissions/7a5c9e96-3747-466f-bac4-38493aad0d9a

import Mathlib


open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

namespace SlepianProof

open Matrix

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


open scoped BigOperators

namespace DudleyProof

/-- The regression-direction monotonicity step requires differentiability of the derivative,
but no continuity or uniform bound on the second derivative. -/
lemma monotone_partial_along_direction {N : ℕ}
    (F : (Fin N → ℝ) → ℝ) (hF2 : Differentiable ℝ (fderiv ℝ F))
    (w v : Fin N → ℝ) (j : Fin N)
    (hdir : ∀ u, 0 ≤ fderiv ℝ (fderiv ℝ F) u v (Pi.single j 1)) :
    Monotone (fun t : ℝ => fderiv ℝ F (w + t • v) (Pi.single j 1)) := by
  have hline (t : ℝ) : HasDerivAt (fun t : ℝ => w + t • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add w
  have hd (t : ℝ) : HasDerivAt
      (fun t : ℝ => fderiv ℝ F (w + t • v) (Pi.single j 1))
      (fderiv ℝ (fderiv ℝ F) (w + t • v) v (Pi.single j 1)) t := by
    have hc := (hF2 (w + t • v)).hasFDerivAt.comp_hasDerivAt t (hline t)
    simpa using hc.clm_apply (hasDerivAt_const t (Pi.single j (1 : ℝ)))
  exact monotone_of_hasDerivAt_nonneg hd (fun t => hdir (w + t • v))

lemma monotone_partial_signed_direction {N : ℕ}
    (F : (Fin N → ℝ) → ℝ) (hF2 : Differentiable ℝ (fderiv ℝ F))
    (A B : Finset (Fin N × Fin N))
    (hFA : ∀ p ∈ A, ∀ u, 0 ≤ iteratedFDeriv ℝ 2 F u ![Pi.single p.1 (1 : ℝ), Pi.single p.2 1])
    (hFB : ∀ p ∈ B, ∀ u, iteratedFDeriv ℝ 2 F u ![Pi.single p.1 (1 : ℝ), Pi.single p.2 1] ≤ 0)
    (w v : Fin N → ℝ) (j : Fin N)
    (hVA : ∀ i, (i, j) ∈ A → 0 ≤ v i)
    (hVB : ∀ i, (i, j) ∈ B → v i ≤ 0)
    (hVeq : ∀ i, (i, j) ∉ A ∪ B → v i = 0) :
    Monotone (fun t : ℝ => fderiv ℝ F (w + t • v) (Pi.single j 1)) := by
  apply monotone_partial_along_direction F hF2 w v j
  intro u
  have hexp : fderiv ℝ (fderiv ℝ F) u v (Pi.single j 1) =
      ∑ i : Fin N, v i * fderiv ℝ (fderiv ℝ F) u (Pi.single i 1) (Pi.single j 1) := by
    simpa only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul] using
      congrArg (fun z => fderiv ℝ (fderiv ℝ F) u z (Pi.single j 1)) (pi_eq_sum_univ' v)
  rw [hexp]
  apply Finset.sum_nonneg
  intro i hi
  by_cases hpa : (i, j) ∈ A
  · apply mul_nonneg (hVA i hpa)
    simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      using hFA (i, j) hpa u
  · by_cases hpb : (i, j) ∈ B
    · apply mul_nonneg_of_nonpos_of_nonpos (hVB i hpb)
      simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
        using hFB (i, j) hpb u
    · rw [hVeq i (by simpa only [Finset.mem_union, not_or] using And.intro hpa hpb), zero_mul]

end DudleyProof



open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace

namespace DudleyProof

lemma mul_sub_monotone_nonneg (g : ℝ → ℝ) (hg : Monotone g) (s : ℝ) :
    0 ≤ s * (g s - g (-s)) := by
  by_cases hs : 0 ≤ s
  · exact mul_nonneg hs (sub_nonneg.mpr (hg (by linarith)))
  · exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hs)
      (sub_nonpos.mpr (hg (by linarith)))

section Reflection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

lemma hyperplane_reflection_apply (a x : E) :
    (ℝ ∙ a)ᗮ.reflection x = x - (2 * (⟪a, x⟫ / ‖a‖ ^ 2)) • a := by
  rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  simp [neg_sub, two_smul, two_mul, add_smul]

/-- Reflection across the regression hyperplane pairs the derivative into a nonnegative
quantity. This is pointwise and requires no integrability or derivative bounds. -/
lemma partial_reflection_pair_nonneg {N : ℕ}
    (Z : E →L[ℝ] (Fin N → ℝ)) (a x : E) (j : Fin N)
    (F : (Fin N → ℝ) → ℝ) (hF2 : Differentiable ℝ (fderiv ℝ F))
    (hdir : ∀ u, 0 ≤ fderiv ℝ (fderiv ℝ F) u (Z a) (Pi.single j 1)) :
    0 ≤ ⟪a, x⟫ * fderiv ℝ F (Z x) (Pi.single j 1) +
      ⟪a, (ℝ ∙ a)ᗮ.reflection x⟫ *
        fderiv ℝ F (Z ((ℝ ∙ a)ᗮ.reflection x)) (Pi.single j 1) := by
  by_cases ha : a = 0
  · simp [ha]
  have ha2 : ‖a‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr ha)
  let s : ℝ := ⟪a, x⟫
  let v := (‖a‖ ^ 2)⁻¹ • Z a
  let w := Z x - s • v
  have hdirv (u) : 0 ≤ fderiv ℝ (fderiv ℝ F) u v (Pi.single j 1) := by
    dsimp [v]
    simp only [map_smul, smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr (sq_nonneg ‖a‖)) (hdir u)
  have hg := monotone_partial_along_direction F hF2 w v j hdirv
  have hplus : w + s • v = Z x := by simp [w]
  have hminus : w + (-s) • v = Z ((ℝ ∙ a)ᗮ.reflection x) := by
    rw [hyperplane_reflection_apply, map_sub, map_smul]
    dsimp [w, v, s]
    simp only [smul_smul, div_eq_mul_inv, neg_smul]
    module
  have hsneg : ⟪a, (ℝ ∙ a)ᗮ.reflection x⟫ = -s := by
    rw [hyperplane_reflection_apply, inner_sub_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    dsimp [s]
    field_simp
    <;> ring
  have h := mul_sub_monotone_nonneg
    (fun t => fderiv ℝ F (w + t • v) (Pi.single j 1)) hg s
  rw [hplus, hminus] at h
  rw [hsneg]
  dsimp [s] at h ⊢
  nlinarith [h]

end Reflection

section GaussianBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Radial truncation preserves Gaussian reflection symmetry. Compactness supplies all
integrability needed here, even when the derivatives of F have arbitrary growth. -/
lemma gaussian_ball_partial_nonneg {N : ℕ}
    (Z : E →L[ℝ] (Fin N → ℝ)) (a : E) (j : Fin N) (R : ℝ)
    (F : (Fin N → ℝ) → ℝ) (hF2 : Differentiable ℝ (fderiv ℝ F))
    (hdir : ∀ u, 0 ≤ fderiv ℝ (fderiv ℝ F) u (Z a) (Pi.single j 1)) :
    0 ≤ ∫ x in Metric.closedBall (0 : E) R,
      ⟪a, x⟫ * fderiv ℝ F (Z x) (Pi.single j 1) ∂stdGaussian E := by
  let r := (ℝ ∙ a)ᗮ.reflection
  let q (x : E) := ⟪a, x⟫ * fderiv ℝ F (Z x) (Pi.single j 1)
  have hqc : Continuous q := by
    dsimp [q]
    exact (continuous_const.inner continuous_id).mul
      ((hF2.continuous.comp Z.continuous).clm_apply continuous_const)
  have hqrc : Continuous (fun x => q (r x)) := hqc.comp r.continuous
  have hqi : IntegrableOn q (Metric.closedBall (0 : E) R) (stdGaussian E) :=
    hqc.continuousOn.integrableOn_compact (isCompact_closedBall 0 R)
  have hqri : IntegrableOn (fun x => q (r x))
      (Metric.closedBall (0 : E) R) (stdGaussian E) :=
    hqrc.continuousOn.integrableOn_compact (isCompact_closedBall 0 R)
  have hmp : MeasurePreserving r (stdGaussian E) (stdGaussian E) :=
    ⟨r.continuous.measurable, stdGaussian_map r⟩
  have hpre : r ⁻¹' Metric.closedBall (0 : E) R = Metric.closedBall (0 : E) R := by
    ext x
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, r.norm_map]
  have he := hmp.setIntegral_preimage_emb
    r.toHomeomorph.measurableEmbedding q (Metric.closedBall (0 : E) R)
  rw [hpre] at he
  have hpos : 0 ≤ ∫ x in Metric.closedBall (0 : E) R, (q x + q (r x))
      ∂stdGaussian E := by
    apply integral_nonneg
    intro x
    exact partial_reflection_pair_nonneg Z a x j F hF2 hdir
  rw [integral_add hqi hqri, he] at hpos
  change 0 ≤ ∫ x in Metric.closedBall (0 : E) R, q x ∂stdGaussian E
  linarith

end GaussianBall

end DudleyProof



open MeasureTheory ProbabilityTheory InnerProductSpace Filter
open scoped RealInnerProductSpace Topology BigOperators

namespace DudleyProof

noncomputable section

section Maps

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def rotationMap (L M : E →L[ℝ] G) (θ : ℝ) : E →L[ℝ] G :=
  Real.cos θ • L + Real.sin θ • M

def rotationVelocity (L M : E →L[ℝ] G) (θ : ℝ) : E →L[ℝ] G :=
  -Real.sin θ • L + Real.cos θ • M

lemma rotation_norm_le (L M : E →L[ℝ] G) (θ : ℝ) (x : E) :
    ‖rotationMap L M θ x‖ ≤ (‖L‖ + ‖M‖) * ‖x‖ := by
  calc
    ‖rotationMap L M θ x‖ ≤ ‖L x‖ + ‖M x‖ := by
      dsimp [rotationMap]
      apply le_trans (norm_add_le _ _)
      apply add_le_add
      · change ‖Real.cos θ • L x‖ ≤ ‖L x‖
        rw [norm_smul, Real.norm_eq_abs]
        exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one θ) (norm_nonneg _)).trans_eq
          (one_mul _)
      · change ‖Real.sin θ • M x‖ ≤ ‖M x‖
        rw [norm_smul, Real.norm_eq_abs]
        exact (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one θ) (norm_nonneg _)).trans_eq
          (one_mul _)
    _ ≤ ‖L‖ * ‖x‖ + ‖M‖ * ‖x‖ := add_le_add (L.le_opNorm x) (M.le_opNorm x)
    _ = _ := by ring

lemma rotation_velocity_norm_le (L M : E →L[ℝ] G) (θ : ℝ) (x : E) :
    ‖rotationVelocity L M θ x‖ ≤ (‖L‖ + ‖M‖) * ‖x‖ := by
  calc
    ‖rotationVelocity L M θ x‖ ≤ ‖L x‖ + ‖M x‖ := by
      dsimp [rotationVelocity]
      apply le_trans (norm_add_le _ _)
      apply add_le_add
      · change ‖-Real.sin θ • L x‖ ≤ ‖L x‖
        rw [norm_smul, Real.norm_eq_abs, abs_neg]
        exact (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one θ) (norm_nonneg _)).trans_eq
          (one_mul _)
      · change ‖Real.cos θ • M x‖ ≤ ‖M x‖
        rw [norm_smul, Real.norm_eq_abs]
        exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one θ) (norm_nonneg _)).trans_eq
          (one_mul _)
    _ ≤ ‖L‖ * ‖x‖ + ‖M‖ * ‖x‖ := add_le_add (L.le_opNorm x) (M.le_opNorm x)
    _ = _ := by ring

end Maps

section Riesz

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def rieszRow {N : ℕ} (Z : E →L[ℝ] (Fin N → ℝ)) (j : Fin N) : E :=
  (toDual ℝ E).symm ((ContinuousLinearMap.proj j).comp Z)

lemma rieszRow_inner {N : ℕ} (Z : E →L[ℝ] (Fin N → ℝ)) (j : Fin N) (x : E) :
    ⟪rieszRow Z j, x⟫ = Z x j := by
  exact toDual_symm_apply

end Riesz

section Interpolation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A compact truncation of the input supplies a uniform derivative envelope.
No global growth bound on F or its derivatives is assumed. -/
lemma gaussian_ball_rotation_hasDerivAt {N : ℕ}
    (L M : E →L[ℝ] (Fin N → ℝ))
    (F : (Fin N → ℝ) → ℝ) (hF1 : Differentiable ℝ F)
    (hF2 : Differentiable ℝ (fderiv ℝ F)) (R : ℝ) (hR : 0 ≤ R) (θ : ℝ) :
    HasDerivAt
      (fun t => ∫ x in Metric.closedBall (0 : E) R, F (rotationMap L M t x) ∂stdGaussian E)
      (∫ x in Metric.closedBall (0 : E) R,
        fderiv ℝ F (rotationMap L M θ x) (rotationVelocity L M θ x) ∂stdGaussian E) θ := by
  let S := (‖L‖ + ‖M‖) * R
  let K := Metric.closedBall (0 : Fin N → ℝ) S
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : Fin N → ℝ) S).image
    hF2.continuous).isBounded.exists_norm_le
  have hZK (t : ℝ) (x : E) (hx : x ∈ Metric.closedBall (0 : E) R) :
      rotationMap L M t x ∈ K := by
    simp only [K, Metric.mem_closedBall, dist_zero_right]
    exact (rotation_norm_le L M t x).trans (mul_le_mul_of_nonneg_left
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
      (add_nonneg (norm_nonneg _) (norm_nonneg _)))
  have hDF (t : ℝ) (x : E) (hx : x ∈ Metric.closedBall (0 : E) R) :
      ‖fderiv ℝ F (rotationMap L M t x)‖ ≤ max C 0 :=
    (hC _ (Set.mem_image_of_mem _ (hZK t x hx))).trans (le_max_left _ _)
  have hbound (t : ℝ) (x : E) (hx : x ∈ Metric.closedBall (0 : E) R) :
      ‖fderiv ℝ F (rotationMap L M t x) (rotationVelocity L M t x)‖ ≤ max C 0 * S := by
    calc
      _ ≤ ‖fderiv ℝ F (rotationMap L M t x)‖ * ‖rotationVelocity L M t x‖ :=
        (fderiv ℝ F (rotationMap L M t x)).le_opNorm _
      _ ≤ max C 0 * ‖rotationVelocity L M t x‖ :=
        mul_le_mul_of_nonneg_right (hDF t x hx) (norm_nonneg _)
      _ ≤ max C 0 * S := mul_le_mul_of_nonneg_left
        ((rotation_velocity_norm_le L M t x).trans (mul_le_mul_of_nonneg_left
          (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
          (add_nonneg (norm_nonneg _) (norm_nonneg _)))) (le_max_right _ _)
  have hfc (t) : Continuous (fun x => F (rotationMap L M t x)) :=
    hF1.continuous.comp (rotationMap L M t).continuous
  have hdc (t) : Continuous (fun x => fderiv ℝ F (rotationMap L M t x)
      (rotationVelocity L M t x)) :=
    (hF2.continuous.comp (rotationMap L M t).continuous).clm_apply
      (rotationVelocity L M t).continuous
  have hfi : IntegrableOn (fun x => F (rotationMap L M θ x))
      (Metric.closedBall (0 : E) R) (stdGaussian E) :=
    (hfc θ).continuousOn.integrableOn_compact (isCompact_closedBall (0 : E) R)
  have hd (t : ℝ) (x : E) : HasDerivAt (fun u => F (rotationMap L M u x))
      (fderiv ℝ F (rotationMap L M t x) (rotationVelocity L M t x)) t := by
    apply (hF1 (rotationMap L M t x)).hasFDerivAt.comp_hasDerivAt t
    exact ((Real.hasDerivAt_cos t).smul_const (L x)).add
      ((Real.hasDerivAt_sin t).smul_const (M x))
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (stdGaussian E).restrict (Metric.closedBall (0 : E) R))
    (s := Set.univ) (F := fun t x => F (rotationMap L M t x))
    (F' := fun t x => fderiv ℝ F (rotationMap L M t x) (rotationVelocity L M t x))
    (bound := fun _ => max C 0 * S) (Filter.univ_mem : Set.univ ∈ 𝓝 θ)
    (Eventually.of_forall fun t => (hfc t).aestronglyMeasurable) hfi
    (hdc θ).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
      exact fun t _ => hbound t x hx)
    (integrable_const _) (ae_of_all _ fun x t _ => hd t x)
  exact h.2

lemma gaussian_ball_rotation_comparison {N : ℕ}
    (L M : E →L[ℝ] (Fin N → ℝ))
    (F : (Fin N → ℝ) → ℝ) (hF1 : Differentiable ℝ F)
    (hF2 : Differentiable ℝ (fderiv ℝ F))
    (hdir : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2), ∀ j u,
      0 ≤ fderiv ℝ (fderiv ℝ F) u
        (rotationMap L M θ (rieszRow (rotationVelocity L M θ) j)) (Pi.single j 1))
    (R : ℝ) (hR : 0 ≤ R) :
    (∫ x in Metric.closedBall (0 : E) R, F (L x) ∂stdGaussian E) ≤
      ∫ x in Metric.closedBall (0 : E) R, F (M x) ∂stdGaussian E := by
  let g (θ : ℝ) := ∫ x in Metric.closedBall (0 : E) R,
    F (rotationMap L M θ x) ∂stdGaussian E
  let dg (θ : ℝ) := ∫ x in Metric.closedBall (0 : E) R,
    fderiv ℝ F (rotationMap L M θ x) (rotationVelocity L M θ x) ∂stdGaussian E
  have hd (θ : ℝ) : HasDerivAt g (dg θ) θ :=
    gaussian_ball_rotation_hasDerivAt L M F hF1 hF2 R hR θ
  have hnonneg (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) : 0 ≤ dg θ := by
    have hexp (x : E) :
        fderiv ℝ F (rotationMap L M θ x) (rotationVelocity L M θ x) =
          ∑ j, rotationVelocity L M θ x j *
            fderiv ℝ F (rotationMap L M θ x) (Pi.single j 1) := by
      simpa only [map_sum, map_smul, smul_eq_mul] using
        congrArg (fun v => fderiv ℝ F (rotationMap L M θ x) v)
          (pi_eq_sum_univ' (rotationVelocity L M θ x))
    have hqi (j : Fin N) : IntegrableOn
        (fun x => rotationVelocity L M θ x j *
          fderiv ℝ F (rotationMap L M θ x) (Pi.single j 1))
        (Metric.closedBall (0 : E) R) (stdGaussian E) := by
      apply ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : E) R)
      exact (((continuous_apply j).comp (rotationVelocity L M θ).continuous).mul
        ((hF2.continuous.comp (rotationMap L M θ).continuous).clm_apply continuous_const)).continuousOn
    dsimp [dg]
    simp_rw [hexp]
    rw [integral_finsetSum Finset.univ (fun j _ => hqi j)]
    apply Finset.sum_nonneg
    intro j hj
    simpa only [rieszRow_inner] using gaussian_ball_partial_nonneg
      (rotationMap L M θ) (rieszRow (rotationVelocity L M θ) j) j R F hF2
      (hdir θ hθ j)
  have hdiff : Differentiable ℝ g := fun θ => (hd θ).differentiableAt
  have hm := monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) (Real.pi / 2))
    hdiff.continuous.continuousOn hdiff.differentiableOn
    (fun θ hθ => by rw [(hd θ).deriv]; exact hnonneg θ (interior_subset hθ))
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have h := hm ⟨le_rfl, hpi⟩ ⟨hpi, le_rfl⟩ hpi
  simpa [g, rotationMap] using h

/-- The truncation limit uses only the two endpoint integrability hypotheses. -/
lemma gaussian_rotation_comparison {N : ℕ}
    (L M : E →L[ℝ] (Fin N → ℝ))
    (F : (Fin N → ℝ) → ℝ) (hF1 : Differentiable ℝ F)
    (hF2 : Differentiable ℝ (fderiv ℝ F))
    (hdir : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2), ∀ j u,
      0 ≤ fderiv ℝ (fderiv ℝ F) u
        (rotationMap L M θ (rieszRow (rotationVelocity L M θ) j)) (Pi.single j 1))
    (hFL : Integrable (fun x => F (L x)) (stdGaussian E))
    (hFM : Integrable (fun x => F (M x)) (stdGaussian E)) :
    (∫ x, F (L x) ∂stdGaussian E) ≤ ∫ x, F (M x) ∂stdGaussian E := by
  have ht (T : E →L[ℝ] (Fin N → ℝ))
      (hi : Integrable (fun x => F (T x)) (stdGaussian E)) :
      Tendsto (fun n : ℕ => ∫ x in Metric.closedBall (0 : E) n, F (T x) ∂stdGaussian E)
        atTop (𝓝 (∫ x, F (T x) ∂stdGaussian E)) := by
    have h := tendsto_setIntegral_of_monotone
      (μ := stdGaussian E) (f := fun x => F (T x))
      (s := fun n : ℕ => Metric.closedBall (0 : E) (n : ℝ))
      (fun n : ℕ => measurableSet_closedBall (x := (0 : E)) (ε := (n : ℝ)))
      (fun n m hnm => Metric.closedBall_subset_closedBall (by exact_mod_cast hnm))
      (by simpa [Metric.iUnion_closedBall_nat] using hi)
    simpa [Metric.iUnion_closedBall_nat] using h
  exact le_of_tendsto_of_tendsto' (ht L hFL) (ht M hFM)
    (fun n => gaussian_ball_rotation_comparison L M F hF1 hF2 hdir n (Nat.cast_nonneg n))

end Interpolation

end

end DudleyProof



open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace BigOperators

namespace DudleyProof

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

lemma rotation_row_image_eq_gram {κ : Type*} [Fintype κ] {N : ℕ}
    (b : OrthonormalBasis κ ℝ E) (L M : E →L[ℝ] (Fin N → ℝ))
    (hindep : ∀ k, L (b k) = 0 ∨ M (b k) = 0) (θ : ℝ) (i j : Fin N) :
    rotationMap L M θ (rieszRow (rotationVelocity L M θ) j) i =
      (Real.cos θ * Real.sin θ) *
        ((∑ k, M (b k) i * M (b k) j) - ∑ k, L (b k) i * L (b k) j) := by
  have hexp : rotationMap L M θ (rieszRow (rotationVelocity L M θ) j) i =
      ∑ k, rotationMap L M θ (b k) i * rotationVelocity L M θ (b k) j := by
    rw [← b.sum_repr' (rieszRow (rotationVelocity L M θ) j), map_sum]
    simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [real_inner_comm, rieszRow_inner]
    ring
  rw [hexp]
  have he (k : κ) : rotationMap L M θ (b k) i * rotationVelocity L M θ (b k) j =
      (Real.cos θ * Real.sin θ) * (M (b k) i * M (b k) j - L (b k) i * L (b k) j) := by
    rcases hindep k with hL | hM
    · simp [rotationMap, rotationVelocity, hL]
      <;> ring
    · simp [rotationMap, rotationVelocity, hM]
      <;> ring
  simp_rw [he]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]

lemma signed_rotation_hessian_nonneg {κ : Type*} [Fintype κ] {N : ℕ}
    (b : OrthonormalBasis κ ℝ E) (L M : E →L[ℝ] (Fin N → ℝ))
    (hindep : ∀ k, L (b k) = 0 ∨ M (b k) = 0)
    (A B : Finset (Fin N × Fin N))
    (hCovA : ∀ p ∈ A, (∑ k, L (b k) p.1 * L (b k) p.2) ≤
      ∑ k, M (b k) p.1 * M (b k) p.2)
    (hCovB : ∀ p ∈ B, (∑ k, M (b k) p.1 * M (b k) p.2) ≤
      ∑ k, L (b k) p.1 * L (b k) p.2)
    (hCovEq : ∀ p, p ∉ A ∪ B → (∑ k, L (b k) p.1 * L (b k) p.2) =
      ∑ k, M (b k) p.1 * M (b k) p.2)
    (F : (Fin N → ℝ) → ℝ)
    (hFA : ∀ p ∈ A, ∀ u, 0 ≤ iteratedFDeriv ℝ 2 F u ![Pi.single p.1 (1 : ℝ), Pi.single p.2 1])
    (hFB : ∀ p ∈ B, ∀ u, iteratedFDeriv ℝ 2 F u ![Pi.single p.1 (1 : ℝ), Pi.single p.2 1] ≤ 0)
    (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) (j : Fin N) (u : Fin N → ℝ) :
    0 ≤ fderiv ℝ (fderiv ℝ F) u
      (rotationMap L M θ (rieszRow (rotationVelocity L M θ) j)) (Pi.single j 1) := by
  let v := rotationMap L M θ (rieszRow (rotationVelocity L M θ) j)
  have hcs : 0 ≤ Real.cos θ * Real.sin θ := mul_nonneg
    (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
    (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩)
  have hv (i : Fin N) : v i = (Real.cos θ * Real.sin θ) *
      ((∑ k, M (b k) i * M (b k) j) - ∑ k, L (b k) i * L (b k) j) :=
    rotation_row_image_eq_gram b L M hindep θ i j
  have hexp : fderiv ℝ (fderiv ℝ F) u v (Pi.single j 1) =
      ∑ i, v i * fderiv ℝ (fderiv ℝ F) u (Pi.single i 1) (Pi.single j 1) := by
    simpa only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul] using
      congrArg (fun z => fderiv ℝ (fderiv ℝ F) u z (Pi.single j 1)) (pi_eq_sum_univ' v)
  change 0 ≤ fderiv ℝ (fderiv ℝ F) u v (Pi.single j 1)
  rw [hexp]
  apply Finset.sum_nonneg
  intro i hi
  rw [hv]
  by_cases hpa : (i, j) ∈ A
  · apply mul_nonneg (mul_nonneg hcs (sub_nonneg.mpr (hCovA (i, j) hpa)))
    simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      using hFA (i, j) hpa u
  · by_cases hpb : (i, j) ∈ B
    · apply mul_nonneg_of_nonpos_of_nonpos
        (mul_nonpos_of_nonneg_of_nonpos hcs (sub_nonpos.mpr (hCovB (i, j) hpb)))
      simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
        using hFB (i, j) hpb u
    · rw [hCovEq (i, j) (by simpa only [Finset.mem_union, not_or] using And.intro hpa hpb)]
      simp

/-- Full endpoint-integrable comparison of independent linear Gaussian images.
The function has exactly the native differentiability and mixed derivative hypotheses. -/
lemma gaussian_comparison_signed_rows {κ : Type*} [Fintype κ] {N : ℕ}
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (b : OrthonormalBasis κ ℝ E) (L M : E →L[ℝ] (Fin N → ℝ))
    (hindep : ∀ k, L (b k) = 0 ∨ M (b k) = 0)
    (A B : Finset (Fin N × Fin N))
    (hCovA : ∀ p ∈ A, (∑ k, L (b k) p.1 * L (b k) p.2) ≤
      ∑ k, M (b k) p.1 * M (b k) p.2)
    (hCovB : ∀ p ∈ B, (∑ k, M (b k) p.1 * M (b k) p.2) ≤
      ∑ k, L (b k) p.1 * L (b k) p.2)
    (hCovEq : ∀ p, p ∉ A ∪ B → (∑ k, L (b k) p.1 * L (b k) p.2) =
      ∑ k, M (b k) p.1 * M (b k) p.2)
    (F : (Fin N → ℝ) → ℝ) (hF1 : Differentiable ℝ F)
    (hF2 : Differentiable ℝ (fderiv ℝ F))
    (hFA : ∀ p ∈ A, ∀ u, 0 ≤ iteratedFDeriv ℝ 2 F u ![Pi.single p.1 (1 : ℝ), Pi.single p.2 1])
    (hFB : ∀ p ∈ B, ∀ u, iteratedFDeriv ℝ 2 F u ![Pi.single p.1 (1 : ℝ), Pi.single p.2 1] ≤ 0)
    (hFL : Integrable (fun x => F (L x)) (stdGaussian E))
    (hFM : Integrable (fun x => F (M x)) (stdGaussian E)) :
    (∫ x, F (L x) ∂stdGaussian E) ≤ ∫ x, F (M x) ∂stdGaussian E :=
  gaussian_rotation_comparison L M F hF1 hF2
    (fun θ hθ j u => signed_rotation_hessian_nonneg b L M hindep A B
      hCovA hCovB hCovEq F hFA hFB θ hθ j u) hFL hFM

end

end DudleyProof



open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace DudleyProof

noncomputable section

lemma gaussian_secondMoment_eq_gram {N : ℕ}
    (μ : Measure (Fin N → ℝ)) [IsGaussian μ] (hm : (∫ x, x ∂μ) = 0)
    (L : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))
    (hL : μ = (Measure.pi (fun _ : Fin N => gaussianReal 0 1)).map L) (i j : Fin N) :
    (∫ x, x i * x j ∂μ) = ∑ k, L (Pi.single k 1) i * L (Pi.single k 1) j := by
  have hG (r : Fin N) : HasGaussianLaw (fun x : Fin N → ℝ => x r) μ :=
    IsGaussian.hasGaussianLaw_id.map
      (ContinuousLinearMap.proj r : (Fin N → ℝ) →L[ℝ] ℝ)
  have hm' (r : Fin N) : (∫ x, x r ∂μ) = 0 := by
    change (∫ x, (ContinuousLinearMap.proj r : (Fin N → ℝ) →L[ℝ] ℝ) x ∂μ) = 0
    rw [(ContinuousLinearMap.proj r : (Fin N → ℝ) →L[ℝ] ℝ).integral_comp_id_comm
      IsGaussian.integrable_id, hm, map_zero]
  have hc : cov[fun x => x i, fun x => x j; μ] =
      ∑ k, L (Pi.single k 1) i * L (Pi.single k 1) j := by
    rw [hL, covariance_map_fun (measurable_pi_apply i).aestronglyMeasurable
      (measurable_pi_apply j).aestronglyMeasurable L.continuous.measurable.aemeasurable]
    exact SlepianProof.gaussian_pi_covariance_linear L i j
  rw [covariance_eq_sub (hG i).memLp_two (hG j).memLp_two, hm', hm', mul_zero, sub_zero] at hc
  exact hc

/-- The full comparison on Gaussian laws, including singular laws and empty index types.
Only endpoint integrability and the native two differentiability assumptions are used. -/
lemma gaussian_comparison_laws {N : ℕ}
    (μ ν : Measure (Fin N → ℝ)) [IsGaussian μ] [IsGaussian ν]
    (hmμ : (∫ x, x ∂μ) = 0) (hmν : (∫ x, x ∂ν) = 0)
    (A B : Finset (Fin N × Fin N))
    (hCovA : ∀ p ∈ A, (∫ x, x p.1 * x p.2 ∂μ) ≤ ∫ x, x p.1 * x p.2 ∂ν)
    (hCovB : ∀ p ∈ B, (∫ x, x p.1 * x p.2 ∂ν) ≤ ∫ x, x p.1 * x p.2 ∂μ)
    (hCovEq : ∀ p, p ∉ A ∪ B → (∫ x, x p.1 * x p.2 ∂μ) = ∫ x, x p.1 * x p.2 ∂ν)
    (F : (Fin N → ℝ) → ℝ) (hF1 : Differentiable ℝ F)
    (hF2 : Differentiable ℝ (fderiv ℝ F))
    (hFA : ∀ p ∈ A, ∀ u, 0 ≤ iteratedFDeriv ℝ 2 F u ![Pi.single p.1 (1 : ℝ), Pi.single p.2 1])
    (hFB : ∀ p ∈ B, ∀ u, iteratedFDeriv ℝ 2 F u ![Pi.single p.1 (1 : ℝ), Pi.single p.2 1] ≤ 0)
    (hFμ : Integrable F μ) (hFν : Integrable F ν) :
    (∫ x, F x ∂μ) ≤ ∫ x, F x ∂ν := by
  classical
  obtain ⟨P, hP⟩ := SlepianProof.centered_gaussian_eq_map_pi μ hmμ
  obtain ⟨Q, hQ⟩ := SlepianProof.centered_gaussian_eq_map_pi ν hmν
  let g := Measure.pi (fun _ : Fin N => gaussianReal 0 1)
  let g₂ := Measure.pi (fun _ : Fin N ⊕ Fin N => gaussianReal 0 1)
  let p : ((Fin N ⊕ Fin N) → ℝ) →L[ℝ] (Fin N → ℝ) :=
    { toFun x i := x (Sum.inl i)
      map_add' x y := rfl
      map_smul' c x := rfl }
  let q : ((Fin N ⊕ Fin N) → ℝ) →L[ℝ] (Fin N → ℝ) :=
    { toFun x i := x (Sum.inr i)
      map_add' x y := rfl
      map_smul' c x := rfl }
  let e := EuclideanSpace.equiv (Fin N ⊕ Fin N) ℝ
  let L := (P.comp p).comp e.toContinuousLinearMap
  let M := (Q.comp q).comp e.toContinuousLinearMap
  let b := EuclideanSpace.basisFun (Fin N ⊕ Fin N) ℝ
  have heb (k : Fin N ⊕ Fin N) : e (b k) = Pi.single k 1 := by
    ext i
    simp [e, b, EuclideanSpace.basisFun_apply, Pi.single_apply]
  have hpl (k : Fin N) : p (Pi.single (Sum.inl k) 1) = Pi.single k 1 := by
    ext i; simp [p, Pi.single_apply]
  have hpr (k : Fin N) : p (Pi.single (Sum.inr k) 1) = 0 := by
    ext i; simp [p, Pi.single_apply]
  have hql (k : Fin N) : q (Pi.single (Sum.inl k) 1) = 0 := by
    ext i; simp [q, Pi.single_apply]
  have hqr (k : Fin N) : q (Pi.single (Sum.inr k) 1) = Pi.single k 1 := by
    ext i; simp [q, Pi.single_apply]
  have hLb (k : Fin N) : L (b (Sum.inl k)) = P (Pi.single k 1) := by simp [L, heb, hpl]
  have hLb' (k : Fin N) : L (b (Sum.inr k)) = 0 := by simp [L, heb, hpr]
  have hMb (k : Fin N) : M (b (Sum.inr k)) = Q (Pi.single k 1) := by simp [M, heb, hqr]
  have hMb' (k : Fin N) : M (b (Sum.inl k)) = 0 := by simp [M, heb, hql]
  have hindep (k : Fin N ⊕ Fin N) : L (b k) = 0 ∨ M (b k) = 0 := by
    cases k with
    | inl k => exact Or.inr (hMb' k)
    | inr k => exact Or.inl (hLb' k)
  have hGL (i j : Fin N) : (∑ k, L (b k) i * L (b k) j) = ∫ x, x i * x j ∂μ := by
    rw [gaussian_secondMoment_eq_gram μ hmμ P hP]
    simp [Fintype.sum_sum_type, hLb, hLb']
  have hGM (i j : Fin N) : (∑ k, M (b k) i * M (b k) j) = ∫ x, x i * x j ∂ν := by
    rw [gaussian_secondMoment_eq_gram ν hmν Q hQ]
    simp [Fintype.sum_sum_type, hMb, hMb']
  have heback : g₂.map e.symm = stdGaussian (EuclideanSpace ℝ (Fin N ⊕ Fin N)) :=
    map_pi_eq_stdGaussian
  have hemap : (stdGaussian (EuclideanSpace ℝ (Fin N ⊕ Fin N))).map e = g₂ := by
    rw [← heback, Measure.map_map e.continuous.measurable e.symm.continuous.measurable]
    have heid : (⇑e ∘ ⇑e.symm) = id := by funext x; exact e.apply_symm_apply x
    rw [heid, Measure.map_id]
  have hep : MeasurePreserving e (stdGaussian (EuclideanSpace ℝ (Fin N ⊕ Fin N))) g₂ :=
    ⟨e.continuous.measurable, hemap⟩
  have hpair := measurePreserving_sumPiEquivProdPi (fun _ : Fin N ⊕ Fin N => gaussianReal 0 1)
  have hp : MeasurePreserving p g₂ g := by
    exact (measurePreserving_fst (μ := g) (ν := g)).comp hpair
  have hq : MeasurePreserving q g₂ g := by
    exact (measurePreserving_snd (μ := g) (ν := g)).comp hpair
  have hpE := hp.comp hep
  have hqE := hq.comp hep
  have hPi : Integrable (fun x => F (P x)) g := by
    have hi : Integrable F (g.map P) := by
      change Integrable F ((Measure.pi (fun _ : Fin N => gaussianReal 0 1)).map P)
      rw [← hP]
      exact hFμ
    exact hi.comp_measurable P.continuous.measurable
  have hQi : Integrable (fun x => F (Q x)) g := by
    have hi : Integrable F (g.map Q) := by
      change Integrable F ((Measure.pi (fun _ : Fin N => gaussianReal 0 1)).map Q)
      rw [← hQ]
      exact hFν
    exact hi.comp_measurable Q.continuous.measurable
  have hLi : Integrable (fun x => F (L x)) (stdGaussian (EuclideanSpace ℝ (Fin N ⊕ Fin N))) :=
    hpE.integrable_comp_of_integrable hPi
  have hMi : Integrable (fun x => F (M x)) (stdGaussian (EuclideanSpace ℝ (Fin N ⊕ Fin N))) :=
    hqE.integrable_comp_of_integrable hQi
  have h := gaussian_comparison_signed_rows b L M hindep A B
    (fun p hp => by simpa only [hGL, hGM] using hCovA p hp)
    (fun p hp => by simpa only [hGL, hGM] using hCovB p hp)
    (fun p hp => by simpa only [hGL, hGM] using hCovEq p hp)
    F hF1 hF2 hFA hFB hLi hMi
  have heL := integral_map (μ := stdGaussian (EuclideanSpace ℝ (Fin N ⊕ Fin N)))
    hpE.measurable.aemeasurable (hF1.continuous.comp P.continuous).aestronglyMeasurable
  have heM := integral_map (μ := stdGaussian (EuclideanSpace ℝ (Fin N ⊕ Fin N)))
    hqE.measurable.aemeasurable (hF1.continuous.comp Q.continuous).aestronglyMeasurable
  rw [hpE.map_eq] at heL
  rw [hqE.map_eq] at heM
  change (∫ x, F (P x) ∂g) = ∫ x, F (L x) ∂stdGaussian _ at heL
  change (∫ x, F (Q x) ∂g) = ∫ x, F (M x) ∂stdGaussian _ at heM
  rw [← heL, ← heM] at h
  rw [hP, hQ, integral_map P.continuous.measurable.aemeasurable hF1.continuous.aestronglyMeasurable,
    integral_map Q.continuous.measurable.aemeasurable hF1.continuous.aestronglyMeasurable]
  exact h

end

end DudleyProof



open MeasureTheory ProbabilityTheory


/-- **Theorem 5.25** (Gaussian comparison principle), Wainwright, *High-Dimensional Statistics*
(2019), p. 144. Let `X, Y : Ω → Fin N → ℝ` be a pair of centered Gaussian random vectors (each
with law `HasGaussianLaw` and coordinatewise mean zero), and suppose there exist disjoint subsets
`A` and `B` of `Fin N × Fin N` such that `E[XᵢXⱼ] ≤ E[YᵢYⱼ]` for `(i,j) ∈ A`, `E[XᵢXⱼ] ≥ E[YᵢYⱼ]`
for `(i,j) ∈ B`, and `E[XᵢXⱼ] = E[YᵢYⱼ]` for `(i,j) ∉ A ∪ B`. Let `F : (Fin N → ℝ) → ℝ` be twice differentiable (not necessarily with a
*continuous* second derivative: `F` itself differentiable everywhere, and its derivative map
`fderiv ℝ F` itself differentiable everywhere), with mixed second partial
`∂²F/∂uᵢ∂uⱼ(u) ≥ 0` for `(i,j) ∈ A` and `≤ 0` for `(i,j) ∈ B` (realized as the iterated Fréchet
derivative applied to the two standard basis vectors). Then `E[F(X)] ≤ E[F(Y)]`. -/
theorem solution {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω}
    [IsProbabilityMeasure Prob] {N : ℕ} (X Y : Ω → Fin N → ℝ)
    (hXGauss : HasGaussianLaw X Prob) (hYGauss : HasGaussianLaw Y Prob)
    (hXmean : ∀ i, ∫ ω, X ω i ∂Prob = 0) (hYmean : ∀ i, ∫ ω, Y ω i ∂Prob = 0)
    (hXint : ∀ i j, Integrable (fun ω => X ω i * X ω j) Prob)
    (hYint : ∀ i j, Integrable (fun ω => Y ω i * Y ω j) Prob)
    (A B : Finset (Fin N × Fin N)) (hAB : Disjoint A B)
    (hCovA : ∀ p ∈ A, ∫ ω, X ω p.1 * X ω p.2 ∂Prob ≤ ∫ ω, Y ω p.1 * Y ω p.2 ∂Prob)
    (hCovB : ∀ p ∈ B, ∫ ω, Y ω p.1 * Y ω p.2 ∂Prob ≤ ∫ ω, X ω p.1 * X ω p.2 ∂Prob)
    (hCovEq : ∀ p : Fin N × Fin N, p ∉ A ∪ B →
      ∫ ω, X ω p.1 * X ω p.2 ∂Prob = ∫ ω, Y ω p.1 * Y ω p.2 ∂Prob)
    (F : (Fin N → ℝ) → ℝ) (hF1 : Differentiable ℝ F) (hF2 : Differentiable ℝ (fderiv ℝ F))
    (hFA : ∀ p ∈ A, ∀ u, 0 ≤ iteratedFDeriv ℝ 2 F u ![Pi.single p.1 (1 : ℝ), Pi.single p.2 1])
    (hFB : ∀ p ∈ B, ∀ u, iteratedFDeriv ℝ 2 F u ![Pi.single p.1 (1 : ℝ), Pi.single p.2 1] ≤ 0)
    (hFXint : Integrable (fun ω => F (X ω)) Prob) (hFYint : Integrable (fun ω => F (Y ω)) Prob) :
    ∫ ω, F (X ω) ∂Prob ≤ ∫ ω, F (Y ω) ∂Prob := by
  let μ := Prob.map X
  let ν := Prob.map Y
  haveI : IsGaussian μ := hXGauss.isGaussian_map
  haveI : IsGaussian ν := hYGauss.isGaussian_map
  have hmμ (i : Fin N) : (∫ x, x i ∂μ) = 0 := by
    rw [integral_map hXGauss.aemeasurable (measurable_pi_apply i).aestronglyMeasurable]
    exact hXmean i
  have hmν (i : Fin N) : (∫ x, x i ∂ν) = 0 := by
    rw [integral_map hYGauss.aemeasurable (measurable_pi_apply i).aestronglyMeasurable]
    exact hYmean i
  have hmeanμ : (∫ x, x ∂μ) = 0 := by
    ext i
    change (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ) (∫ x, x ∂μ) = 0
    rw [← (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ).integral_comp_id_comm
      IsGaussian.integrable_id]
    exact hmμ i
  have hmeanν : (∫ x, x ∂ν) = 0 := by
    ext i
    change (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ) (∫ x, x ∂ν) = 0
    rw [← (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ).integral_comp_id_comm
      IsGaussian.integrable_id]
    exact hmν i
  have hcovμ (i j : Fin N) : (∫ x, x i * x j ∂μ) = ∫ ω, X ω i * X ω j ∂Prob :=
    integral_map hXGauss.aemeasurable
      ((measurable_pi_apply i).mul (measurable_pi_apply j)).aestronglyMeasurable
  have hcovν (i j : Fin N) : (∫ x, x i * x j ∂ν) = ∫ ω, Y ω i * Y ω j ∂Prob :=
    integral_map hYGauss.aemeasurable
      ((measurable_pi_apply i).mul (measurable_pi_apply j)).aestronglyMeasurable
  have hFμ : Integrable F μ :=
    (integrable_map_measure hF1.continuous.aestronglyMeasurable hXGauss.aemeasurable).mpr hFXint
  have hFν : Integrable F ν :=
    (integrable_map_measure hF1.continuous.aestronglyMeasurable hYGauss.aemeasurable).mpr hFYint
  have h := DudleyProof.gaussian_comparison_laws μ ν hmeanμ hmeanν A B
    (fun p hp => by simpa only [hcovμ, hcovν] using hCovA p hp)
    (fun p hp => by simpa only [hcovμ, hcovν] using hCovB p hp)
    (fun p hp => by simpa only [hcovμ, hcovν] using hCovEq p hp)
    F hF1 hF2 hFA hFB hFμ hFν
  rwa [integral_map hXGauss.aemeasurable hF1.continuous.aestronglyMeasurable,
    integral_map hYGauss.aemeasurable hF1.continuous.aestronglyMeasurable] at h




#print axioms solution
