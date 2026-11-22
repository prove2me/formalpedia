-- Prove2me | solution 1 for IteratedLP.Gaussian.proposition_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-22T20:34:00.805864+00:00
-- url     : https://prove2.me/submissions/5b9380c5-fbd8-4f26-b36d-bf5e0f55fbd2

import Mathlib

open MeasureTheory ProbabilityTheory Matrix

namespace IteratedLP_Gaussian_proposition_3_3_aux

lemma toEuclideanLin_mul_apply {n d l : ℕ} (B : Matrix (Fin n) (Fin d) ℝ)
    (C : Matrix (Fin d) (Fin l) ℝ) (x : EuclideanSpace ℝ (Fin l)) :
    toEuclideanLin (B * C) x = toEuclideanLin B (toEuclideanLin C x) := by
  simp [toEuclideanLin_apply, mulVec_mulVec]

lemma inner_toEuclideanLin' {n d : ℕ} (B : Matrix (Fin n) (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (u : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (toEuclideanLin B x) u = inner ℝ x (toEuclideanLin Bᵀ u) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, ofLp_toEuclideanLin_apply, star_trivial]
  rw [dotProduct_mulVec, mulVec_transpose]

/-- The continuous linear map of a matrix acting on Euclidean spaces. -/
noncomputable abbrev clm {n d : ℕ} (B : Matrix (Fin n) (Fin d) ℝ) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap (toEuclideanLin B)

lemma clm_adjoint_apply {n d : ℕ} (B : Matrix (Fin n) (Fin d) ℝ) (u : EuclideanSpace ℝ (Fin n)) :
    (clm B).adjoint u = toEuclideanLin Bᵀ u := by
  refine ext_inner_left ℝ fun v => ?_
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact inner_toEuclideanLin' B v u

/-- Affine image of a multivariate Gaussian. -/
lemma map_affine {n d : ℕ} (μ : EuclideanSpace ℝ (Fin d)) (S : Matrix (Fin d) (Fin d) ℝ)
    (hS : S.PosSemidef) (B : Matrix (Fin n) (Fin d) ℝ) (c : EuclideanSpace ℝ (Fin n)) :
    (multivariateGaussian μ S).map (fun z => c + toEuclideanLin B z) =
      multivariateGaussian (c + toEuclideanLin B μ) (B * S * Bᵀ) := by
  have hf : (fun z => c + toEuclideanLin B z) = (fun x => c + x) ∘ (clm B) := rfl
  rw [hf, ← Measure.map_map (measurable_const_add c) (clm B).measurable]
  have hBS : (B * S * Bᵀ).PosSemidef := by
    simpa using hS.mul_mul_conjTranspose_same B
  apply IsGaussian.ext
  · rw [integral_id_multivariateGaussian']
    rw [integral_map (measurable_const_add c).aemeasurable aestronglyMeasurable_id]
    simp only [id]
    rw [integral_add (integrable_const _) IsGaussian.integrable_fun_id, integral_const,
      probReal_univ, one_smul,
      ContinuousLinearMap.integral_id_map IsGaussian.integrable_id,
      integral_id_multivariateGaussian]
    simp
  · rw [covarianceBilin_map_const_add]
    ext u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id, covarianceBilin_multivariateGaussian hS,
      covarianceBilin_multivariateGaussian hBS, clm_adjoint_apply, clm_adjoint_apply]
    simp only [ofLp_toEuclideanLin_apply]
    rw [mulVec_transpose B u.ofLp, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec u.ofLp B]

/-- Pushing a product measure through `(y, w) ↦ (y, w + f y)` gives a composition product. -/
lemma map_prod_shift {k d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin k))) [SFinite μ]
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ν]
    (f : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin d)) (hf : Measurable f)
    (κ : Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d)))
    (hκ : ∀ b, κ b = ν.map (fun w => w + f b)) :
    (μ.prod ν).map (fun p => (p.1, p.2 + f p.1)) = μ ⊗ₘ κ := by
  have : IsMarkovKernel κ :=
    ⟨fun b => by rw [hκ b]; exact Measure.isProbabilityMeasure_map (by fun_prop)⟩
  have hF : Measurable (fun p : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin d) =>
      (p.1, p.2 + f p.1)) := by fun_prop
  ext s hs
  rw [Measure.map_apply hF hs, Measure.compProd_apply hs, Measure.prod_apply (hF hs)]
  congr 1
  funext b
  rw [hκ b, Measure.map_apply (by fun_prop) (measurable_prodMk_left hs)]
  rfl

lemma posDef_M {d k : ℕ} (Sig : Matrix (Fin d) (Fin d) ℝ) (hSig : Sig.PosDef)
    (T : Matrix (Fin k) (Fin d) ℝ) (hT : T.rank = k) : (T * Sig * Tᵀ).PosDef := by
  have h1 : Tᵀ.rank = k := by rw [rank_transpose, hT]
  have h2 := LinearMap.finrank_range_add_finrank_ker (Tᵀ.mulVecLin)
  have h3 : Module.finrank ℝ (LinearMap.range Tᵀ.mulVecLin) = k := h1
  rw [h3] at h2
  simp only [Module.finrank_fin_fun] at h2
  have hker : LinearMap.ker Tᵀ.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
  have hinj : Function.Injective T.vecMul := by
    have := LinearMap.ker_eq_bot.mp hker
    intro x y hxy
    apply this
    simp only [mulVecLin_apply, mulVec_transpose]
    exact hxy
  simpa using hSig.mul_mul_conjTranspose_same hinj

section mats
variable {d k : ℕ} (Sig : Matrix (Fin d) (Fin d) ℝ) (T : Matrix (Fin k) (Fin d) ℝ)

lemma hMX (hdet : IsUnit (T * Sig * Tᵀ).det) {n : ℕ} (X : Matrix (Fin k) (Fin n) ℝ) :
    T * (Sig * (Tᵀ * ((T * Sig * Tᵀ)⁻¹ * X))) = X := by
  calc T * (Sig * (Tᵀ * ((T * Sig * Tᵀ)⁻¹ * X))) = (T * Sig * Tᵀ * (T * Sig * Tᵀ)⁻¹) * X := by
        simp only [Matrix.mul_assoc]
    _ = X := by rw [mul_nonsing_inv _ hdet, Matrix.one_mul]

lemma I1 (hdet : IsUnit (T * Sig * Tᵀ).det) :
    T * (Sig * Tᵀ * (T * Sig * Tᵀ)⁻¹) = 1 := by
  have := hMX Sig T hdet (1 : Matrix (Fin k) (Fin k) ℝ)
  simpa [Matrix.mul_assoc] using this

lemma At (hSig : Sig.PosDef) (hM : (T * Sig * Tᵀ).PosDef) :
    (Sig * Tᵀ * (T * Sig * Tᵀ)⁻¹)ᵀ = (T * Sig * Tᵀ)⁻¹ * T * Sig := by
  have hS : Sigᵀ = Sig := by
    have := hSig.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hMt : (T * Sig * Tᵀ)ᵀ = T * Sig * Tᵀ := by
    have := hM.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  rw [transpose_mul, transpose_nonsing_inv, hMt, transpose_mul, hS, transpose_transpose]
  simp only [Matrix.mul_assoc]

lemma I3 (hSig : Sig.PosDef) (hM : (T * Sig * Tᵀ).PosDef) :
    T * Sig * (1 - Sig * Tᵀ * (T * Sig * Tᵀ)⁻¹ * T)ᵀ = 0 := by
  have hdet : IsUnit (T * Sig * Tᵀ).det := (isUnit_iff_isUnit_det _).mp hM.isUnit
  rw [transpose_sub, transpose_one, transpose_mul, At Sig T hSig hM, Matrix.mul_sub,
    Matrix.mul_one]
  have := hMX Sig T hdet (T * Sig)
  simp only [Matrix.mul_assoc] at this ⊢
  rw [this, sub_self]

lemma I4 (hSig : Sig.PosDef) (hM : (T * Sig * Tᵀ).PosDef) :
    (1 - Sig * Tᵀ * (T * Sig * Tᵀ)⁻¹ * T) * Sig * (1 - Sig * Tᵀ * (T * Sig * Tᵀ)⁻¹ * T)ᵀ =
      Sig - Sig * Tᵀ * (T * Sig * Tᵀ)⁻¹ * T * Sig := by
  have e : (1 - Sig * Tᵀ * (T * Sig * Tᵀ)⁻¹ * T) * Sig * (1 - Sig * Tᵀ * (T * Sig * Tᵀ)⁻¹ * T)ᵀ
      = Sig * (1 - Sig * Tᵀ * (T * Sig * Tᵀ)⁻¹ * T)ᵀ - (Sig * Tᵀ * (T * Sig * Tᵀ)⁻¹) *
        (T * Sig * (1 - Sig * Tᵀ * (T * Sig * Tᵀ)⁻¹ * T)ᵀ) := by
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  rw [e, I3 Sig T hSig hM, Matrix.mul_zero, sub_zero, transpose_sub, transpose_one,
    transpose_mul, At Sig T hSig hM, Matrix.mul_sub, Matrix.mul_one]
  simp only [Matrix.mul_assoc]

end mats

lemma toEuclideanLin_one_apply {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    toEuclideanLin (1 : Matrix (Fin n) (Fin n) ℝ) x = x := by
  simp

lemma toEuclideanLin_one_sub_apply {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ)
    (T : Matrix (Fin k) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    toEuclideanLin (1 - A * T) x = x - toEuclideanLin A (toEuclideanLin T x) := by
  rw [map_sub, LinearMap.sub_apply, toEuclideanLin_one_apply, toEuclideanLin_mul_apply]

end IteratedLP_Gaussian_proposition_3_3_aux

open IteratedLP_Gaussian_proposition_3_3_aux in
theorem solution (d k : ℕ) (m : EuclideanSpace ℝ (Fin d))
    (Sig : Matrix (Fin d) (Fin d) ℝ) (hSig : Sig.PosDef)
    (T : Matrix (Fin k) (Fin d) ℝ) (hT : T.rank = k)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → EuclideanSpace ℝ (Fin d)) (hZ : Measurable Z)
    (hlaw : P.map Z = multivariateGaussian m Sig) :
    (∀ κ : ProbabilityTheory.Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d)),
      (∀ b, κ b = multivariateGaussian
        (m + toEuclideanLin (Sig * Tᵀ * (T * Sig * Tᵀ)⁻¹) (b - toEuclideanLin T m))
        (Sig - Sig * Tᵀ * (T * Sig * Tᵀ)⁻¹ * T * Sig)) →
      P.map (fun ω => (toEuclideanLin T (Z ω), Z ω)) =
        (P.map (fun ω => toEuclideanLin T (Z ω))) ⊗ₘ κ) ∧
    (IsGaussian (P.map (fun ω => Z ω -
        (P[Z | MeasurableSpace.comap (fun ω => toEuclideanLin T (Z ω)) inferInstance]) ω)) ∧
      IndepFun (fun ω => Z ω -
        (P[Z | MeasurableSpace.comap (fun ω => toEuclideanLin T (Z ω)) inferInstance]) ω)
        (fun ω => toEuclideanLin T (Z ω)) P) ∧
    (∀ σ : ℝ, 0 < σ → Sig = σ ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ) →
      ∀ zb : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin d),
        (∀ b, toEuclideanLin T (zb b) = b ∧
          ∀ z, toEuclideanLin T z = b → ‖zb b - m‖ ≤ ‖z - m‖) →
      ∀ κ : ProbabilityTheory.Kernel (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin d)),
        (∀ b, κ b = (stdGaussian (EuclideanSpace ℝ (Fin d))).map
          (fun g => zb b + σ • (LinearMap.ker (toEuclideanLin T)).starProjection g)) →
        P.map (fun ω => (toEuclideanLin T (Z ω), Z ω)) =
          (P.map (fun ω => toEuclideanLin T (Z ω))) ⊗ₘ κ) := by
  have hM : (T * Sig * Tᵀ).PosDef := posDef_M Sig hSig T hT
  have hdet : IsUnit (T * Sig * Tᵀ).det := (isUnit_iff_isUnit_det _).mp hM.isUnit
  have i1 := I1 Sig T hdet
  have i3 := I3 Sig T hSig hM
  have i4 := I4 Sig T hSig hM
  have hQpsd : ((1 - Sig * Tᵀ * (T * Sig * Tᵀ)⁻¹ * T) * Sig *
      (1 - Sig * Tᵀ * (T * Sig * Tᵀ)⁻¹ * T)ᵀ).PosSemidef := by
    have := hSig.posSemidef.mul_mul_conjTranspose_same (1 - Sig * Tᵀ * (T * Sig * Tᵀ)⁻¹ * T)
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  generalize hA : Sig * Tᵀ * (T * Sig * Tᵀ)⁻¹ = A at i1 i3 i4 hQpsd ⊢
  have hZG : HasGaussianLaw Z P := ⟨by rw [hlaw]; infer_instance⟩
  -- `Y = TZ` and the residual `W = (I - AT) Z`, so that `Z = W + A Y`.
  let Y : Ω → EuclideanSpace ℝ (Fin k) := fun ω => toEuclideanLin T (Z ω)
  let W : Ω → EuclideanSpace ℝ (Fin d) := fun ω => toEuclideanLin (1 - A * T) (Z ω)
  have hdecomp : ∀ ω, Z ω = W ω + toEuclideanLin A (Y ω) := by
    intro ω
    simp only [W, Y]
    rw [toEuclideanLin_one_sub_apply, sub_add_cancel]
  have hYm : Measurable Y := (clm T).measurable.comp hZ
  have hWm : Measurable W := (clm (1 - A * T)).measurable.comp hZ
  have hYW : HasGaussianLaw (fun ω => (Y ω, W ω)) P := hZG.map ((clm T).prod (clm (1 - A * T)))
  -- `Y` and `W` are jointly Gaussian and uncorrelated, hence independent.
  have hind : IndepFun Y W P := by
    refine hYW.indepFun_of_covariance_inner (fun x y => ?_)
    have e1 : (fun ω => inner ℝ x (Y ω)) = (fun z => inner ℝ (toEuclideanLin Tᵀ x) z) ∘ Z := by
      funext ω
      simp only [Function.comp, Y]
      rw [real_inner_comm, inner_toEuclideanLin', real_inner_comm]
    have e2 : (fun ω => inner ℝ y (W ω)) =
        (fun z => inner ℝ (toEuclideanLin (1 - A * T)ᵀ y) z) ∘ Z := by
      funext ω
      simp only [Function.comp, W]
      rw [real_inner_comm, inner_toEuclideanLin', real_inner_comm]
    rw [e1, e2, ← covariance_map (by fun_prop) (by fun_prop) hZ.aemeasurable, hlaw,
      ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
      covarianceBilin_multivariateGaussian hSig.posSemidef]
    simp only [ofLp_toEuclideanLin_apply]
    rw [mulVec_transpose T x.ofLp, mulVec_mulVec, ← dotProduct_mulVec, mulVec_mulVec,
      ← Matrix.mul_assoc, i3, zero_mulVec, dotProduct_zero]
  have hlawW : P.map W = multivariateGaussian (toEuclideanLin (1 - A * T) m)
      ((1 - A * T) * Sig * (1 - A * T)ᵀ) := by
    have : W = (fun z => 0 + toEuclideanLin (1 - A * T) z) ∘ Z := by
      funext ω; simp [W]
    rw [this, ← Measure.map_map (by fun_prop) hZ, hlaw, map_affine m Sig hSig.posSemidef _ 0,
      zero_add]
  have part1 : ∀ κ : ProbabilityTheory.Kernel (EuclideanSpace ℝ (Fin k))
      (EuclideanSpace ℝ (Fin d)),
      (∀ b, κ b = multivariateGaussian (m + toEuclideanLin A (b - toEuclideanLin T m))
        (Sig - A * T * Sig)) →
      P.map (fun ω => (Y ω, Z ω)) = (P.map Y) ⊗ₘ κ := by
    intro κ hκ
    have hκ' : ∀ b, κ b = (P.map W).map (fun w => w + toEuclideanLin A b) := by
      intro b
      have hf : (fun w => w + toEuclideanLin A b) =
          fun w => toEuclideanLin A b + toEuclideanLin (1 : Matrix (Fin d) (Fin d) ℝ) w := by
        funext w; rw [toEuclideanLin_one_apply, add_comm]
      rw [hκ b, hlawW, hf, map_affine _ _ hQpsd 1 _, transpose_one, Matrix.one_mul,
        Matrix.mul_one, i4, toEuclideanLin_one_apply, toEuclideanLin_one_sub_apply, map_sub]
      congr 1
      abel
    have hfun : (fun ω => (Y ω, Z ω)) =
        (fun p => (p.1, p.2 + toEuclideanLin A p.1)) ∘ (fun ω => (Y ω, W ω)) := by
      funext ω
      exact Prod.ext rfl (hdecomp ω)
    rw [hfun, ← Measure.map_map (by fun_prop) (hYm.prodMk hWm),
      (indepFun_iff_map_prod_eq_prod_map_map hYm.aemeasurable hWm.aemeasurable).mp hind]
    have : IsProbabilityMeasure (P.map W) := Measure.isProbabilityMeasure_map hWm.aemeasurable
    exact map_prod_shift _ _ _ (by fun_prop) κ hκ'
  refine ⟨part1, ?_, ?_⟩
  · have hle : MeasurableSpace.comap Y inferInstance ≤ (inferInstance : MeasurableSpace Ω) :=
      hYm.comap_le
    have hWi : Integrable W P := (hZG.map (clm (1 - A * T))).integrable
    have hAYi : Integrable (fun ω => toEuclideanLin A (Y ω)) P :=
      (hZG.map ((clm A).comp (clm T))).integrable
    have hYmY : Measurable[MeasurableSpace.comap Y inferInstance] Y := comap_measurable Y
    have hWmW : Measurable[MeasurableSpace.comap W inferInstance] W := comap_measurable W
    have hsm : StronglyMeasurable[MeasurableSpace.comap Y inferInstance]
        (fun ω => toEuclideanLin A (Y ω)) := ((clm A).measurable.comp hYmY).stronglyMeasurable
    have hce : P[Z | MeasurableSpace.comap Y inferInstance] =ᵐ[P]
        fun ω => (∫ ω, W ω ∂P) + toEuclideanLin A (Y ω) := by
      have hZ' : Z = W + fun ω => toEuclideanLin A (Y ω) := funext hdecomp
      have h1 := condExp_add hWi hAYi (MeasurableSpace.comap Y inferInstance)
      rw [← hZ'] at h1
      have h2 : P[fun ω => toEuclideanLin A (Y ω) | MeasurableSpace.comap Y inferInstance] =
          fun ω => toEuclideanLin A (Y ω) :=
        condExp_of_stronglyMeasurable hle hsm hAYi
      have h3 : P[W | MeasurableSpace.comap Y inferInstance] =ᵐ[P] fun _ => ∫ ω, W ω ∂P :=
        condExp_indep_eq hWm.comap_le hle hWmW.stronglyMeasurable hind.symm
      filter_upwards [h1, h3] with ω h1ω h3ω
      rw [h1ω, Pi.add_apply, h3ω, h2]
    have hR : (fun ω => Z ω - P[Z | MeasurableSpace.comap Y inferInstance] ω) =ᵐ[P]
        fun ω => W ω - ∫ ω, W ω ∂P := by
      filter_upwards [hce] with ω hω
      rw [hω, hdecomp ω]
      abel
    refine ⟨?_, ?_⟩
    · show IsGaussian (P.map (fun ω => Z ω - P[Z | MeasurableSpace.comap Y inferInstance] ω))
      rw [Measure.map_congr hR]
      have : (fun ω => W ω - ∫ ω, W ω ∂P) = (fun w => -(∫ ω, W ω ∂P) + w) ∘ W := by
        funext ω; simp only [Function.comp]; abel
      rw [this, ← Measure.map_map (measurable_const_add _) hWm]
      have : IsGaussian (P.map W) := (hZG.map (clm (1 - A * T))).isGaussian_map
      infer_instance
    · show IndepFun (fun ω => Z ω - P[Z | MeasurableSpace.comap Y inferInstance] ω) Y P
      refine (hind.symm.comp (measurable_sub_const (∫ ω, W ω ∂P)) measurable_id).congr ?_
        (ae_eq_refl _)
      exact hR.symm
  · intro σ hσ hS2 zb hzb κ hκ
    apply part1 κ
    intro b
    rw [hκ b]
    have hAC : A = Tᵀ * ((σ ^ 2) • (T * Sig * Tᵀ)⁻¹) := by
      rw [← hA]
      nth_rewrite 1 [hS2]
      simp [Matrix.smul_mul, Matrix.mul_smul]
    have hperp : ∀ u v, toEuclideanLin T v = 0 → inner ℝ (toEuclideanLin A u) v = 0 := by
      intro u v hv
      rw [hAC, toEuclideanLin_mul_apply, inner_toEuclideanLin', transpose_transpose, hv,
        inner_zero_right]
    have hTA : ∀ u, toEuclideanLin T (toEuclideanLin A u) = u := by
      intro u
      rw [← toEuclideanLin_mul_apply, i1, toEuclideanLin_one_apply]
    -- `I - AT` is the orthogonal projection onto `ker T`.
    have hproj : ∀ g, (LinearMap.ker (toEuclideanLin T)).starProjection g =
        toEuclideanLin (1 - A * T) g := by
      intro g
      apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      · rw [LinearMap.mem_ker, toEuclideanLin_one_sub_apply, map_sub, hTA, sub_self]
      · intro w hw
        rw [toEuclideanLin_one_sub_apply, sub_sub_cancel]
        exact hperp _ _ hw
    -- the conditional mean is the closest point of `{Tz = b}` to `m`.
    set zs := m + toEuclideanLin A (b - toEuclideanLin T m) with hzs
    have hTzs : toEuclideanLin T zs = b := by
      rw [hzs, map_add, hTA, add_sub_cancel]
    have hzbeq : zb b = zs := by
      obtain ⟨h1, h2⟩ := hzb b
      have key : ∀ z, toEuclideanLin T z = b → ‖z - m‖ ^ 2 = ‖z - zs‖ ^ 2 + ‖zs - m‖ ^ 2 := by
        intro z hz
        have e : z - m = (z - zs) + (zs - m) := by abel
        have hin : inner ℝ (z - zs) (zs - m) = 0 := by
          have : zs - m = toEuclideanLin A (b - toEuclideanLin T m) := by
            rw [hzs, add_sub_cancel_left]
          rw [this, real_inner_comm]
          apply hperp
          rw [map_sub, hz, hTzs, sub_self]
        rw [e, norm_add_sq_real, hin]
        ring
      have k1 := key (zb b) h1
      have k2 := h2 zs hTzs
      have k3 : ‖zb b - m‖ ^ 2 ≤ ‖zs - m‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) k2 2
      have k4 : ‖zb b - zs‖ ^ 2 = 0 := by
        have := sq_nonneg ‖zb b - zs‖
        linarith
      exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp k4))
    have hfun : (fun g => zb b + σ • (LinearMap.ker (toEuclideanLin T)).starProjection g) =
        fun g => zs + toEuclideanLin (σ • (1 - A * T)) g := by
      funext g
      rw [hproj, hzbeq, map_smul, LinearMap.smul_apply]
    rw [hfun, ← multivariateGaussian_zero_one, map_affine 0 1 PosSemidef.one _ zs, map_zero,
      add_zero, ← i4, hS2]
    congr 1
    simp [transpose_smul, smul_smul, sq]
