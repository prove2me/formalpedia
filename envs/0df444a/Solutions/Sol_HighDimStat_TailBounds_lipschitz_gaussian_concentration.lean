-- Prove2me | solution 1 for HighDimStat.TailBounds.lipschitz_gaussian_concentration
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-02T17:47:56.946715+00:00
-- url     : https://prove2.me/submissions/b0e6fa4c-251d-4e9d-85f6-6f941c3ef4ee

import Definitions.Def_HighDimStat_TailBounds_IsLLipschitz
import Definitions.Def_HighDimStat_TailBounds_IsSubGaussian
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 2000000

section

open MeasureTheory ContinuousLinearMap
open scoped Convolution

namespace GaussianConcentration

set_option maxHeartbeats 1200000

/-- Convolution of an integrable kernel with a bounded observable has a uniform bound.
Applied to the second derivative of a compact smoothing kernel, this bounds the Hessian
without any derivatives of the original Lipschitz observable. -/
lemma bounded_convolution_norm {E U V W : Type*}
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure E) [SFinite μ] (B : U →L[ℝ] V →L[ℝ] W)
    {a : E → U} {b : E → V} (ha : Integrable a μ) (hb : Continuous b)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, ‖b x‖ ≤ C) (x : E) :
    ‖(a ⋆[B, μ] b) x‖ ≤ (‖B‖ * C) * ∫ y, ‖a y‖ ∂μ := by
  have hnorm (y : E) : ‖B (a y) (b (x-y))‖ ≤ (‖B‖ * C) * ‖a y‖ := by
    calc
      _ ≤ ‖B‖ * ‖a y‖ * ‖b (x-y)‖ := B.le_opNorm₂ _ _
      _ ≤ ‖B‖ * ‖a y‖ * C :=
        mul_le_mul_of_nonneg_left (hbound _) (mul_nonneg B.opNorm_nonneg (norm_nonneg _))
      _ = _ := by ring
  have hi : Integrable (fun y => B (a y) (b (x-y))) μ :=
    (ha.norm.const_mul (‖B‖ * C)).mono'
      (B.aestronglyMeasurable_comp₂ ha.aestronglyMeasurable
        (hb.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (ae_of_all _ hnorm)
  rw [convolution_def]
  calc
    _ ≤ ∫ y, ‖B (a y) (b (x-y))‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, (‖B‖ * C) * ‖a y‖ ∂μ := integral_mono hi.norm (ha.norm.const_mul _) hnorm
    _ = _ := integral_const_mul _ _

/-- Compact-kernel smoothing of a bounded continuous observable has a bounded Hessian. -/
lemma bounded_convolution_hessian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {ρ f : E → ℝ}
    (hρ : ContDiff ℝ 2 ρ) (hρc : HasCompactSupport ρ) (hf : Continuous f)
    {C : ℝ} (hC : 0 ≤ C) (hf_bound : ∀ x, ‖f x‖ ≤ C) :
    ∃ H : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ (ρ ⋆[lsmul ℝ ℝ, μ] f)) x‖ ≤ H := by
  letI : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  letI : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let B : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := lsmul ℝ ℝ
  let B1 : (E →L[ℝ] ℝ) →L[ℝ] ℝ →L[ℝ] (E →L[ℝ] ℝ) := B.precompL E
  let B2 : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) := B1.precompL E
  have hfLoc : LocallyIntegrable f μ := hf.locallyIntegrable
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by norm_num)
  have hdρ : ContDiff ℝ 1 (fderiv ℝ ρ) := hρ.fderiv_right (by norm_num)
  have hdf : fderiv ℝ (ρ ⋆[B, μ] f) = fderiv ℝ ρ ⋆[B1, μ] f := by
    funext x
    exact (hρc.hasFDerivAt_convolution_left B hρ1 hfLoc x).fderiv
  have hddf (x : E) : fderiv ℝ (fderiv ℝ (ρ ⋆[B, μ] f)) x =
      (convolution (𝕜 := ℝ) (fderiv ℝ (fderiv ℝ ρ)) f B2 μ) x := by
    rw [hdf]
    exact ((hρc.fderiv ℝ).hasFDerivAt_convolution_left B1 hdρ hfLoc x).fderiv
  have hddi : Integrable (fderiv ℝ (fderiv ℝ ρ)) μ :=
    (hdρ.continuous_fderiv one_ne_zero).integrable_of_hasCompactSupport
      ((hρc.fderiv ℝ).fderiv ℝ)
  refine ⟨(‖B2‖ * C) * ∫ y, ‖fderiv ℝ (fderiv ℝ ρ) y‖ ∂μ, ?_⟩
  intro x
  rw [hddf]
  exact bounded_convolution_norm μ _ hddi hf hC hf_bound x

end GaussianConcentration

end

section

open MeasureTheory Real

namespace GaussianConcentration

set_option maxHeartbeats 800000

/-- Averaging translates against a probability kernel preserves the exact Lipschitz constant.
This is the regularity invariant needed when smoothing the native concentration target. -/
lemma lipschitz_average {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] {K : NNReal} {f : E → ℝ}
    (hf : LipschitzWith K f) (hi : ∀ x, Integrable (fun y => f (x-y)) μ) :
    LipschitzWith K (fun x => ∫ y, f (x-y) ∂μ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  rw [Real.dist_eq, ← integral_sub (hi x) (hi z), ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ y, ‖f (x-y)-f (z-y)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, (K : ℝ) * dist x z ∂μ := by
      apply integral_mono ((hi x).sub (hi z)).norm (integrable_const _)
      intro y
      have h := hf.dist_le_mul (x-y) (z-y)
      simpa only [Real.dist_eq, Real.norm_eq_abs, dist_sub_right, Pi.sub_apply] using h
    _ = (K : ℝ) * dist x z := by simp

/-- A probability kernel supported in a small ball gives a uniform smoothing error. -/
lemma average_sub_le {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] {K : NNReal} {f : E → ℝ}
    (hf : LipschitzWith K f) (hi : ∀ x, Integrable (fun y => f (x-y)) μ)
    {ε : ℝ} (hsupport : ∀ᵐ y ∂μ, ‖y‖ ≤ ε) (x : E) :
    |(∫ y, f (x-y) ∂μ) - f x| ≤ (K : ℝ)*ε := by
  have hconst : (∫ _y : E, f x ∂μ) = f x := by simp
  rw [← hconst, ← integral_sub (hi x) (integrable_const _), ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ y, ‖f (x-y)-f x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, (K : ℝ)*ε ∂μ := by
      apply integral_mono_ae ((hi x).sub (integrable_const _)).norm (integrable_const _)
      filter_upwards [hsupport] with y hy
      have h := hf.dist_le_mul (x-y) x
      have hd : dist (x-y) x = ‖y‖ := by rw [dist_eq_norm]; simp
      rw [hd] at h
      exact (show ‖f (x-y)-f x‖ ≤ (K : ℝ)*‖y‖ from h).trans
        (mul_le_mul_of_nonneg_left hy K.coe_nonneg)
    _ = _ := by simp

end GaussianConcentration

end

section

open MeasureTheory ContinuousLinearMap Filter
open scoped Convolution Topology

namespace GaussianConcentration

set_option maxHeartbeats 1400000

/-- Compact normalized smoothing retains the exact Lipschitz constant and uniform bound,
while supplying all the smoothness and Hessian bounds required by covariance interpolation. -/
lemma bounded_lipschitz_bump_smoothing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {K : NNReal} {f : E → ℝ} (hf : LipschitzWith K f) {C : ℝ}
    (hf_bound : ∀ x, ‖f x‖ ≤ C) (φ : ContDiffBump (0 : E)) :
    ∃ g : E → ℝ, ContDiff ℝ 2 g ∧ LipschitzWith K g ∧
      (∀ x, ‖g x‖ ≤ C) ∧ (∃ H : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ H) ∧
      ∀ x, |g x - f x| ≤ (K : ℝ) * φ.rOut := by
  let σ : Measure E := Measure.addHaar
  let ρ := φ.normed σ
  let ν := σ.withDensity (fun x => ENNReal.ofReal (ρ x))
  let g : E → ℝ := ρ ⋆[lsmul ℝ ℝ, σ] f
  have hC : 0 ≤ C := (norm_nonneg (f 0)).trans (hf_bound 0)
  have hρm : Measurable (fun x => ENNReal.ofReal (ρ x)) :=
    φ.continuous_normed.measurable.ennreal_ofReal
  have hρi : Integrable ρ σ := φ.integrable_normed
  have hρnn (x : E) : 0 ≤ ρ x := φ.nonneg_normed x
  haveI : IsProbabilityMeasure ν := by
    constructor
    change σ.withDensity (fun x => ENNReal.ofReal (ρ x)) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hρi (ae_of_all _ hρnn)]
    rw [φ.integral_normed]
    simp
  have hi (x : E) : Integrable (fun y => f (x-y)) ν := by
    have hc : Continuous (fun y => f (x-y)) := hf.continuous.comp (continuous_const.sub continuous_id)
    simpa only [mul_one] using (integrable_const (1 : ℝ) (μ := ν)).bdd_mul
      hc.aestronglyMeasurable (ae_of_all _ fun y => hf_bound _)
  have he (x : E) : g x = ∫ y, f (x-y) ∂ν := by
    have h := integral_withDensity_eq_integral_toReal_smul (μ := σ) hρm
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top) (fun y => f (x-y))
    simpa only [ν, g, convolution_def, lsmul_apply, smul_eq_mul,
      ENNReal.toReal_ofReal (hρnn _)] using h.symm
  have hLip : LipschitzWith K g := by
    have hfun : g = fun x => ∫ y, f (x-y) ∂ν := funext he
    rw [hfun]
    exact lipschitz_average ν hf hi
  have hg_bound (x : E) : ‖g x‖ ≤ C := by
    rw [he]
    calc
      _ ≤ ∫ y, ‖f (x-y)‖ ∂ν := norm_integral_le_integral_norm _
      _ ≤ ∫ _y : E, C ∂ν := integral_mono (hi x).norm (integrable_const C) (fun y => hf_bound _)
      _ = C := by simp
  have hs : ∀ᵐ y ∂ν, ‖y‖ ≤ φ.rOut := by
    apply (ae_withDensity_iff hρm).mpr
    filter_upwards [] with y hy
    have hne : ρ y ≠ 0 := by
      intro hzero
      exact hy (by simp [hzero])
    have hb : y ∈ Metric.ball (0 : E) φ.rOut := by
      rw [← φ.support_normed_eq (μ := σ)]
      exact hne
    have hn : ‖y‖ < φ.rOut := by
      simpa only [Metric.mem_ball, dist_zero_right] using hb
    exact hn.le
  have hg : ContDiff ℝ 2 g :=
    φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
      φ.contDiff_normed hf.continuous.locallyIntegrable
  have hH := bounded_convolution_hessian (ρ := ρ) (f := f) σ
    (φ.contDiff_normed (μ := σ)) (φ.hasCompactSupport_normed (μ := σ))
    hf.continuous hC hf_bound
  refine ⟨g, hg, hLip, hg_bound, hH, ?_⟩
  intro x
  rw [he]
  exact average_sub_le ν hf hi hs x

end GaussianConcentration

end

section

open InnerProductSpace
open scoped RealInnerProductSpace

namespace GaussianConcentration

set_option maxHeartbeats 800000

/-- Contracting two derivatives over an orthonormal basis has the dimension-free bound
required in Gaussian covariance interpolation. -/
lemma dual_basis_product_bound {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (b : OrthonormalBasis ι ℝ E) (p q : E →L[ℝ] ℝ) :
    |∑ i, p (b i) * q (b i)| ≤ ‖p‖ * ‖q‖ := by
  let u := (toDual ℝ E).symm p
  let v := (toDual ℝ E).symm q
  have hp (i : ι) : p (b i) = ⟪u, b i⟫ :=
    (toDual_symm_apply (𝕜 := ℝ) (y := p) (x := b i)).symm
  have hq (i : ι) : q (b i) = ⟪b i, v⟫ := by
    rw [real_inner_comm]
    exact (toDual_symm_apply (𝕜 := ℝ) (y := q) (x := b i)).symm
  simp_rw [hp, hq, b.sum_inner_mul_inner]
  exact (abs_real_inner_le_norm u v).trans_eq (by simp [u, v])

lemma lipschitz_gradient_pair_bound {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {K : NNReal} (hf : LipschitzWith K f) (x y : EuclideanSpace ℝ (Fin n)) :
    |∑ i, fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i) *
      fderiv ℝ f y (EuclideanSpace.basisFun (Fin n) ℝ i)| ≤ (K : ℝ)^2 := by
  apply (dual_basis_product_bound (EuclideanSpace.basisFun (Fin n) ℝ) _ _).trans
  have hx := norm_fderiv_le_of_lipschitz ℝ hf (x₀ := x)
  have hy := norm_fderiv_le_of_lipschitz ℝ hf (x₀ := y)
  simpa only [pow_two] using mul_le_mul hx hy (norm_nonneg _) K.coe_nonneg

end GaussianConcentration

end

section

open InnerProductSpace
open scoped RealInnerProductSpace

namespace GaussianConcentration

set_option maxHeartbeats 1000000

section Product

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma product_fderiv_apply {f g : E → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (z v : E × E) :
    fderiv ℝ (fun w : E × E => f w.1 * g w.2) z v =
      f z.1 * fderiv ℝ g z.2 v.2 + g z.2 * fderiv ℝ f z.1 v.1 := by
  have h₁ := (hf z.1).hasFDerivAt.comp z (ContinuousLinearMap.fst ℝ E E).hasFDerivAt
  have h₂ := (hg z.2).hasFDerivAt.comp z (ContinuousLinearMap.snd ℝ E E).hasFDerivAt
  have h := congrArg (fun p => p v) (h₁.mul h₂).fderiv
  change fderiv ℝ (fun w : E × E => f w.1 * g w.2) z v =
    f z.1 * fderiv ℝ g z.2 v.2 + g z.2 * fderiv ℝ f z.1 v.1 at h
  exact h

lemma product_hessian_apply {f g : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (z u v : E × E) :
    fderiv ℝ (fderiv ℝ (fun w : E × E => f w.1 * g w.2)) z u v =
      fderiv ℝ f z.1 u.1 * fderiv ℝ g z.2 v.2 +
      f z.1 * fderiv ℝ (fderiv ℝ g) z.2 u.2 v.2 +
      fderiv ℝ g z.2 u.2 * fderiv ℝ f z.1 v.1 +
      g z.2 * fderiv ℝ (fderiv ℝ f) z.1 u.1 v.1 := by
  let F := fun w : E × E => f w.1 * g w.2
  have hF : ContDiff ℝ 2 F :=
    (hf.comp (ContinuousLinearMap.fst ℝ E E).contDiff).mul
      (hg.comp (ContinuousLinearMap.snd ℝ E E).contDiff)
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable_one
  have hdg : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable_one
  have hdF : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable_one
  have h₁ := (hf.differentiable (by norm_num) z.1).hasFDerivAt.comp z
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt
  have h₂ := (hg.differentiable (by norm_num) z.2).hasFDerivAt.comp z
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt
  have h₃ := ((hdf z.1).hasFDerivAt.comp z
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt).clm_apply (hasFDerivAt_const v.1 z)
  have h₄ := ((hdg z.2).hasFDerivAt.comp z
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt).clm_apply (hasFDerivAt_const v.2 z)
  have hd := (h₁.mul h₄).add (h₂.mul h₃)
  have he : (fun w => f w.1 * fderiv ℝ g w.2 v.2 +
      g w.2 * fderiv ℝ f w.1 v.1) = fun w => fderiv ℝ F w v := by
    funext w
    exact (product_fderiv_apply (hf.differentiable (by norm_num))
      (hg.differentiable (by norm_num)) w v).symm
  change HasFDerivAt (fun w : E × E => f w.1 * fderiv ℝ g w.2 v.2 +
    g w.2 * fderiv ℝ f w.1 v.1) _ z at hd
  rw [he] at hd
  have hd' := (hdF z).hasFDerivAt.clm_apply (hasFDerivAt_const v z)
  have hh := hd.unique hd'
  have ha := congrArg (fun p => p u) hh
  simp only [ContinuousLinearMap.comp_zero, zero_add] at ha
  change f z.1 * fderiv ℝ (fderiv ℝ g) z.2 u.2 v.2 +
    fderiv ℝ g z.2 v.2 * fderiv ℝ f z.1 u.1 +
    (g z.2 * fderiv ℝ (fderiv ℝ f) z.1 u.1 v.1 +
    fderiv ℝ f z.1 v.1 * fderiv ℝ g z.2 u.2) =
    fderiv ℝ (fderiv ℝ F) z u v at ha
  dsimp [F] at ha ⊢
  rw [← ha]
  ring

lemma product_hessian_cross {f g : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (z : E × E) (a b : E) :
    fderiv ℝ (fderiv ℝ (fun w : E × E => f w.1 * g w.2)) z (a, 0) (0, b) =
      fderiv ℝ f z.1 a * fderiv ℝ g z.2 b := by
  simp [product_hessian_apply hf hg]

lemma product_hessian_cross_swap {f g : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (z : E × E) (a b : E) :
    fderiv ℝ (fderiv ℝ (fun w : E × E => f w.1 * g w.2)) z (0, b) (a, 0) =
      fderiv ℝ f z.1 a * fderiv ℝ g z.2 b := by
  simp [product_hessian_apply hf hg, mul_comm]

lemma bilinear_pair_diagonal_cancel (B : (E × E) →L[ℝ] (E × E) →L[ℝ] ℝ) (a : E) :
    B (a, a) (a, a) - B (a, 0) (a, 0) - B (0, a) (0, a) =
      B (a, 0) (0, a) + B (0, a) (a, 0) := by
  have ha : (a, a) = (a, 0) + (0, a) := by simp
  rw [ha]
  simp only [map_add, ContinuousLinearMap.add_apply]
  ring

end Product

lemma product_hessian_trace_cancel {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : E → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (b : ι → E) (z : E × E) :
    (∑ i, fderiv ℝ (fderiv ℝ (fun w : E × E => f w.1 * g w.2)) z
      (b i, b i) (b i, b i)) -
    (∑ i, fderiv ℝ (fderiv ℝ (fun w : E × E => f w.1 * g w.2)) z
      (b i, 0) (b i, 0)) -
    (∑ i, fderiv ℝ (fderiv ℝ (fun w : E × E => f w.1 * g w.2)) z
      (0, b i) (0, b i)) =
      2 * ∑ i, fderiv ℝ f z.1 (b i) * fderiv ℝ g z.2 (b i) := by
  simp_rw [← Finset.sum_sub_distrib, bilinear_pair_diagonal_cancel,
    product_hessian_cross hf hg, product_hessian_cross_swap hf hg]
  simp [two_mul, Finset.sum_add_distrib]

lemma exponential_fderiv_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : Differentiable ℝ f) (lam : ℝ) (x v : E) :
    fderiv ℝ (fun y => Real.exp (lam * f y)) x v =
      lam * Real.exp (lam * f x) * fderiv ℝ f x v := by
  have hd := ((hf x).hasFDerivAt.const_mul lam).exp
  have h := congrArg (fun p => p v) hd.fderiv
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul] at h
  rw [h]
  ring

/-- The Hessian covariance contraction contains no Hessian of f after the diagonal
blocks cancel. Its remaining gradient contraction has the exact constant K². -/
lemma exponential_product_trace_bound {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ 2 f) {K : NNReal} (hLip : LipschitzWith K f)
    {lam : ℝ} (hlam : 0 ≤ lam) (z : EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin n)) :
    let F := fun w : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      Real.exp (lam * f w.1) * f w.2
    let b := EuclideanSpace.basisFun (Fin n) ℝ
    (∑ i, fderiv ℝ (fderiv ℝ F) z (b i, b i) (b i, b i)) -
    (∑ i, fderiv ℝ (fderiv ℝ F) z (b i, 0) (b i, 0)) -
    (∑ i, fderiv ℝ (fderiv ℝ F) z (0, b i) (0, b i)) ≤
      2 * lam * (K : ℝ)^2 * Real.exp (lam * f z.1) := by
  dsimp only
  have he : ContDiff ℝ 2 (fun y => Real.exp (lam * f y)) :=
    (contDiff_const.mul hf).exp
  rw [product_hessian_trace_cancel he hf]
  simp_rw [exponential_fderiv_apply (hf.differentiable (by norm_num)) lam,
    mul_assoc, ← Finset.mul_sum]
  have hsum := (le_abs_self _).trans (lipschitz_gradient_pair_bound hLip z.1 z.2)
  have hmul := mul_le_mul_of_nonneg_left hsum
    (mul_nonneg hlam (Real.exp_pos (lam * f z.1)).le)
  nlinarith

end GaussianConcentration

end

section

namespace GaussianConcentration

set_option maxHeartbeats 1200000

section Bounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma linear_apply_bound (p : E →L[ℝ] ℝ) {D : ℝ} (hp : ‖p‖ ≤ D) (v : E) :
    ‖p v‖ ≤ D * ‖v‖ :=
  (p.le_opNorm v).trans (mul_le_mul_of_nonneg_right hp (norm_nonneg _))

lemma bilinear_apply_bound (B : E →L[ℝ] E →L[ℝ] ℝ) {H : ℝ}
    (hB : ‖B‖ ≤ H) (u v : E) : ‖B u v‖ ≤ H * ‖u‖ * ‖v‖ := by
  apply (B u).le_opNorm v |>.trans
  exact mul_le_mul_of_nonneg_right
    ((B.le_opNorm u).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _)))
    (norm_nonneg _)

lemma product_fderiv_bound {f g : E → ℝ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) {Cf Cg Df Dg : ℝ}
    (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg) (hDf : 0 ≤ Df) (hDg : 0 ≤ Dg)
    (hf0 : ∀ x, ‖f x‖ ≤ Cf) (hg0 : ∀ x, ‖g x‖ ≤ Cg)
    (hf1 : ∀ x, ‖fderiv ℝ f x‖ ≤ Df) (hg1 : ∀ x, ‖fderiv ℝ g x‖ ≤ Dg)
    (z : E × E) :
    ‖fderiv ℝ (fun w : E × E => f w.1 * g w.2) z‖ ≤ Cf * Dg + Cg * Df := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [product_fderiv_apply hf hg]
  calc
    ‖f z.1 * fderiv ℝ g z.2 v.2 + g z.2 * fderiv ℝ f z.1 v.1‖
      ≤ ‖f z.1‖ * ‖fderiv ℝ g z.2 v.2‖ +
        ‖g z.2‖ * ‖fderiv ℝ f z.1 v.1‖ := by
          simpa only [norm_mul] using norm_add_le
            (f z.1 * fderiv ℝ g z.2 v.2) (g z.2 * fderiv ℝ f z.1 v.1)
    _ ≤ Cf * (Dg * ‖v‖) + Cg * (Df * ‖v‖) := by
      gcongr
      · exact hf0 _
      · exact (linear_apply_bound _ (hg1 _) _).trans
          (mul_le_mul_of_nonneg_left (norm_snd_le v) hDg)
      · exact hg0 _
      · exact (linear_apply_bound _ (hf1 _) _).trans
          (mul_le_mul_of_nonneg_left (norm_fst_le v) hDf)
    _ = (Cf * Dg + Cg * Df) * ‖v‖ := by ring

lemma product_hessian_bound {f g : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) {Cf Cg Df Dg Hf Hg : ℝ}
    (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg) (hDf : 0 ≤ Df) (hDg : 0 ≤ Dg)
    (hHf : 0 ≤ Hf) (hHg : 0 ≤ Hg)
    (hf0 : ∀ x, ‖f x‖ ≤ Cf) (hg0 : ∀ x, ‖g x‖ ≤ Cg)
    (hf1 : ∀ x, ‖fderiv ℝ f x‖ ≤ Df) (hg1 : ∀ x, ‖fderiv ℝ g x‖ ≤ Dg)
    (hf2 : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ Hf)
    (hg2 : ∀ x, ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ Hg) (z : E × E) :
    ‖fderiv ℝ (fderiv ℝ (fun w : E × E => f w.1 * g w.2)) z‖ ≤
      Df * Dg + Cf * Hg + Dg * Df + Cg * Hf := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro u
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [product_hessian_apply hf hg]
  have hfA (w : E × E) : ‖fderiv ℝ f z.1 w.1‖ ≤ Df * ‖w‖ :=
    (linear_apply_bound _ (hf1 _) _).trans
      (mul_le_mul_of_nonneg_left (norm_fst_le w) hDf)
  have hgA (w : E × E) : ‖fderiv ℝ g z.2 w.2‖ ≤ Dg * ‖w‖ :=
    (linear_apply_bound _ (hg1 _) _).trans
      (mul_le_mul_of_nonneg_left (norm_snd_le w) hDg)
  have hfB : ‖fderiv ℝ (fderiv ℝ f) z.1 u.1 v.1‖ ≤ Hf * ‖u‖ * ‖v‖ := by
    apply (bilinear_apply_bound _ (hf2 _) _ _).trans
    gcongr
    · exact norm_fst_le u
    · exact norm_fst_le v
  have hgB : ‖fderiv ℝ (fderiv ℝ g) z.2 u.2 v.2‖ ≤ Hg * ‖u‖ * ‖v‖ := by
    apply (bilinear_apply_bound _ (hg2 _) _ _).trans
    gcongr
    · exact norm_snd_le u
    · exact norm_snd_le v
  calc
    _ ≤ ‖fderiv ℝ f z.1 u.1 * fderiv ℝ g z.2 v.2‖ +
        ‖f z.1 * fderiv ℝ (fderiv ℝ g) z.2 u.2 v.2‖ +
        ‖fderiv ℝ g z.2 u.2 * fderiv ℝ f z.1 v.1‖ +
        ‖g z.2 * fderiv ℝ (fderiv ℝ f) z.1 u.1 v.1‖ :=
      norm_add₄_le
    _ ≤ (Df * ‖u‖) * (Dg * ‖v‖) + Cf * (Hg * ‖u‖ * ‖v‖) +
        (Dg * ‖u‖) * (Df * ‖v‖) + Cg * (Hf * ‖u‖ * ‖v‖) := by
      simp only [norm_mul]
      gcongr
      all_goals solve
        | exact hfA u | exact hgA v | exact hf0 _ | exact hgB
        | exact hgA u | exact hfA v | exact hg0 _ | exact hfB
    _ = ((Df * Dg + Cf * Hg + Dg * Df + Cg * Hf) * ‖u‖) * ‖v‖ := by ring

lemma exponential_hessian_apply {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (lam : ℝ) (x u v : E) :
    fderiv ℝ (fderiv ℝ (fun y => Real.exp (lam * f y))) x u v =
      Real.exp (lam * f x) * (lam^2 * fderiv ℝ f x u * fderiv ℝ f x v +
        lam * fderiv ℝ (fderiv ℝ f) x u v) := by
  let g := fun y => Real.exp (lam * f y)
  have hg : ContDiff ℝ 2 g := (contDiff_const.mul hf).exp
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable_one
  have hdg : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable_one
  have h₁ := (((hf.differentiable (by norm_num) x).hasFDerivAt.const_mul lam).exp).const_mul lam
  have h₂ := (hdf x).hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  have hd := h₁.mul h₂
  have he : (fun y => lam * Real.exp (lam * f y) * fderiv ℝ f y v) =
      fun y => fderiv ℝ g y v := by
    funext y
    exact (exponential_fderiv_apply (hf.differentiable (by norm_num)) lam y v).symm
  change HasFDerivAt (fun y => lam * Real.exp (lam * f y) * fderiv ℝ f y v) _ x at hd
  rw [he] at hd
  have hd' := (hdg x).hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  have h := congrArg (fun p => p u) (hd.unique hd')
  simp only [ContinuousLinearMap.comp_zero, zero_add] at h
  change lam * Real.exp (lam * f x) * fderiv ℝ (fderiv ℝ f) x u v +
    fderiv ℝ f x v * (lam * (Real.exp (lam * f x) * (lam * fderiv ℝ f x u))) =
    fderiv ℝ (fderiv ℝ g) x u v at h
  dsimp [g] at h ⊢
  rw [← h]
  ring

lemma bounded_exponential_derivatives {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    {C D H : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hH : 0 ≤ H)
    (hf0 : ∀ x, ‖f x‖ ≤ C) (hf1 : ∀ x, ‖fderiv ℝ f x‖ ≤ D)
    (hf2 : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ H) (lam : ℝ) :
    (∀ x, ‖Real.exp (lam * f x)‖ ≤ Real.exp (|lam| * C)) ∧
    (∀ x, ‖fderiv ℝ (fun y => Real.exp (lam * f y)) x‖ ≤
      |lam| * Real.exp (|lam| * C) * D) ∧
    (∀ x, ‖fderiv ℝ (fderiv ℝ (fun y => Real.exp (lam * f y))) x‖ ≤
      Real.exp (|lam| * C) * (|lam|^2 * D^2 + |lam| * H)) := by
  have he (x : E) : ‖Real.exp (lam * f x)‖ ≤ Real.exp (|lam| * C) := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    exact (le_abs_self _).trans (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hf0 x) (abs_nonneg lam))
  refine ⟨he, ?_, ?_⟩
  · intro x
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    rw [exponential_fderiv_apply (hf.differentiable (by norm_num))]
    calc
      _ = |lam| * ‖Real.exp (lam * f x)‖ * ‖fderiv ℝ f x v‖ := by simp [norm_mul, Real.norm_eq_abs]
      _ ≤ |lam| * Real.exp (|lam| * C) * (D * ‖v‖) := by
        gcongr
        · exact he x
        · exact linear_apply_bound _ (hf1 _) v
      _ = (|lam| * Real.exp (|lam| * C) * D) * ‖v‖ := by ring
  · intro x
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro u
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    rw [exponential_hessian_apply hf]
    have hA := linear_apply_bound _ (hf1 x) u
    have hB := linear_apply_bound _ (hf1 x) v
    have hAB := bilinear_apply_bound _ (hf2 x) u v
    calc
      _ ≤ ‖Real.exp (lam * f x)‖ *
          (‖lam^2 * fderiv ℝ f x u * fderiv ℝ f x v‖ +
            ‖lam * fderiv ℝ (fderiv ℝ f) x u v‖) := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
      _ ≤ Real.exp (|lam| * C) *
          (|lam|^2 * (D * ‖u‖) * (D * ‖v‖) + |lam| * (H * ‖u‖ * ‖v‖)) := by
        simp only [norm_mul, norm_pow, Real.norm_eq_abs]
        gcongr
        all_goals solve
          | simpa only [Real.norm_eq_abs] using he x
          | simpa only [Real.norm_eq_abs] using hA
          | simpa only [Real.norm_eq_abs] using hB
          | simpa only [Real.norm_eq_abs] using hAB
      _ = (Real.exp (|lam| * C) * (|lam|^2 * D^2 + |lam| * H) * ‖u‖) * ‖v‖ := by ring

end Bounds

end GaussianConcentration

end

section

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

end

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

section

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

end

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

section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace GaussianConcentration

set_option maxHeartbeats 1000000

lemma gaussian_rotation_interpolation_fin {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L M : (Fin n → ℝ) →L[ℝ] E)
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) {C D H : ℝ}
    (hf_bound : ∀ y, ‖f y‖ ≤ C)
    (hdf_bound : ∀ y, ‖fderiv ℝ f y‖ ≤ D)
    (hddf_bound : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H) (θ : ℝ) :
    HasDerivAt
      (fun u => ∫ x, f (Real.cos u • L x + Real.sin u • M x)
        ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      (∑ i : Fin n, ∫ x,
        (fderiv ℝ (fderiv ℝ f) (Real.cos θ • L x + Real.sin θ • M x)
          (Real.cos θ • L (Pi.single i 1) + Real.sin θ • M (Pi.single i 1)))
          (-Real.sin θ • L (Pi.single i 1) + Real.cos θ • M (Pi.single i 1))
        ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) θ := by
  cases n with
  | zero =>
    have hL (x : Fin 0 → ℝ) : L x = 0 := by
      rw [Subsingleton.elim x 0, map_zero]
    have hM (x : Fin 0 → ℝ) : M x = 0 := by
      rw [Subsingleton.elim x 0, map_zero]
    simpa only [hL, hM, smul_zero, zero_add, Finset.univ_eq_empty, Finset.sum_empty] using
      hasDerivAt_const θ (∫ x : Fin 0 → ℝ, f 0
        ∂Measure.pi (fun _ : Fin 0 => gaussianReal 0 1))
  | succ n =>
    exact SlepianProof.gaussian_rotation_interpolation L M f hf
      hf_bound hdf_bound hddf_bound θ

/-- Reindexing permits Gaussian interpolation on a finite sum of independent blocks,
without excluding an empty dimension or adding dummy random variables. -/
lemma gaussian_rotation_interpolation_fintype {κ : Type*} [Fintype κ] [DecidableEq κ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L M : (κ → ℝ) →L[ℝ] E)
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) {C D H : ℝ}
    (hf_bound : ∀ y, ‖f y‖ ≤ C)
    (hdf_bound : ∀ y, ‖fderiv ℝ f y‖ ≤ D)
    (hddf_bound : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H) (θ : ℝ) :
    HasDerivAt
      (fun u => ∫ x, f (Real.cos u • L x + Real.sin u • M x)
        ∂Measure.pi (fun _ : κ => gaussianReal 0 1))
      (∑ i : κ, ∫ x,
        (fderiv ℝ (fderiv ℝ f) (Real.cos θ • L x + Real.sin θ • M x)
          (Real.cos θ • L (Pi.single i 1) + Real.sin θ • M (Pi.single i 1)))
          (-Real.sin θ • L (Pi.single i 1) + Real.cos θ • M (Pi.single i 1))
        ∂Measure.pi (fun _ : κ => gaussianReal 0 1)) θ := by
  classical
  let e := Fintype.equivFin κ
  let R : (Fin (Fintype.card κ) → ℝ) →L[ℝ] (κ → ℝ) :=
    { toFun x i := x (e i)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have heq : (⇑R) = ⇑(MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e.symm) := by
    funext x i
    simp [R, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  have hp : MeasurePreserving R
      (Measure.pi (fun _ : Fin (Fintype.card κ) => gaussianReal 0 1))
      (Measure.pi (fun _ : κ => gaussianReal 0 1)) :=
    by
      rw [heq]
      exact measurePreserving_piCongrLeft (fun _ : κ => gaussianReal 0 1) e.symm
  have hemb : MeasurableEmbedding R :=
    by
      rw [heq]
      exact (MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e.symm).measurableEmbedding
  have hi (g : (κ → ℝ) → ℝ) :
      (∫ x, g (R x) ∂Measure.pi (fun _ : Fin (Fintype.card κ) => gaussianReal 0 1)) =
      ∫ x, g x ∂Measure.pi (fun _ : κ => gaussianReal 0 1) :=
    hp.integral_comp hemb g
  have hs (i : Fin (Fintype.card κ)) : R (Pi.single i 1) = Pi.single (e.symm i) 1 := by
    ext j
    simp [R, Pi.single_apply, ← e.eq_symm_apply]
  have h := gaussian_rotation_interpolation_fin (L.comp R) (M.comp R) f hf
    hf_bound hdf_bound hddf_bound θ
  have hf' : (fun u => ∫ x, f (Real.cos u • (L.comp R) x + Real.sin u • (M.comp R) x)
      ∂Measure.pi (fun _ : Fin (Fintype.card κ) => gaussianReal 0 1)) =
      (fun u => ∫ x, f (Real.cos u • L x + Real.sin u • M x)
      ∂Measure.pi (fun _ : κ => gaussianReal 0 1)) := by
    funext u
    simpa only [ContinuousLinearMap.comp_apply] using
      hi (fun x => f (Real.cos u • L x + Real.sin u • M x))
  rw [hf'] at h
  simp only [ContinuousLinearMap.comp_apply, hs] at h
  have hInt (i : Fin (Fintype.card κ)) := hi (fun x =>
    (fderiv ℝ (fderiv ℝ f) (Real.cos θ • L x + Real.sin θ • M x)
      (Real.cos θ • L (Pi.single (e.symm i) 1) + Real.sin θ • M (Pi.single (e.symm i) 1)))
      (-Real.sin θ • L (Pi.single (e.symm i) 1) + Real.cos θ • M (Pi.single (e.symm i) 1)))
  simp_rw [hInt] at h
  convert h using 1
  exact (e.symm.sum_comp _).symm

end GaussianConcentration

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace GaussianConcentration

set_option maxHeartbeats 1200000

/-- The Gaussian covariance interpolation estimate integrates the contracted Hessian
bound with total weight one. This is the source of the sharp constant. -/
lemma gaussian_rotation_covariance_bound {κ : Type*} [Fintype κ] [DecidableEq κ]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L M : (κ → ℝ) →L[ℝ] E) (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    {B D H C : ℝ} (hf_bound : ∀ y, ‖f y‖ ≤ B)
    (hdf_bound : ∀ y, ‖fderiv ℝ f y‖ ≤ D)
    (hddf_bound : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H)
    (hindep : ∀ i : κ, L (Pi.single i 1) = 0 ∨ M (Pi.single i 1) = 0)
    (htrace : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      (∑ i : κ, ∫ x,
        fderiv ℝ (fderiv ℝ f) (Real.cos θ • L x + Real.sin θ • M x)
          (L (Pi.single i 1)) (L (Pi.single i 1))
        ∂Measure.pi (fun _ : κ => gaussianReal 0 1)) -
      (∑ i : κ, ∫ x,
        fderiv ℝ (fderiv ℝ f) (Real.cos θ • L x + Real.sin θ • M x)
          (M (Pi.single i 1)) (M (Pi.single i 1))
        ∂Measure.pi (fun _ : κ => gaussianReal 0 1)) ≤ 2 * C) :
    (∫ x, f (L x) ∂Measure.pi (fun _ : κ => gaussianReal 0 1)) ≤
      (∫ x, f (M x) ∂Measure.pi (fun _ : κ => gaussianReal 0 1)) + C := by
  let μ := Measure.pi (fun _ : κ => gaussianReal 0 1)
  let Z (θ : ℝ) : (κ → ℝ) →L[ℝ] E := Real.cos θ • L + Real.sin θ • M
  let T (θ : ℝ) (A : (κ → ℝ) →L[ℝ] E) := ∑ i : κ, ∫ x,
    fderiv ℝ (fderiv ℝ f) (Z θ x) (A (Pi.single i 1)) (A (Pi.single i 1)) ∂μ
  let I (θ : ℝ) := ∫ x, f (Z θ x) ∂μ
  have hBcont : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuous_fderiv one_ne_zero
  have hi (θ : ℝ) (A : (κ → ℝ) →L[ℝ] E) (i : κ) : Integrable
      (fun x => fderiv ℝ (fderiv ℝ f) (Z θ x)
        (A (Pi.single i 1)) (A (Pi.single i 1))) μ := by
    have hc : Continuous (fun x => fderiv ℝ (fderiv ℝ f) (Z θ x)
        (A (Pi.single i 1)) (A (Pi.single i 1))) :=
      ((hBcont.comp (Z θ).continuous).clm_apply continuous_const).clm_apply continuous_const
    have hb (x : κ → ℝ) : ‖fderiv ℝ (fderiv ℝ f) (Z θ x)
        (A (Pi.single i 1)) (A (Pi.single i 1))‖ ≤
        H * ‖A (Pi.single i 1)‖ * ‖A (Pi.single i 1)‖ := by
      apply ((fderiv ℝ (fderiv ℝ f) (Z θ x) (A (Pi.single i 1))).le_opNorm _).trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact ((fderiv ℝ (fderiv ℝ f) (Z θ x)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hddf_bound _) (norm_nonneg _))
    simpa only [mul_one] using (integrable_const (1 : ℝ) (μ := μ)).bdd_mul
      hc.aestronglyMeasurable (ae_of_all _ hb)
  have hd (θ : ℝ) : HasDerivAt I
      (Real.cos θ * Real.sin θ * (T θ M - T θ L)) θ := by
    have h := gaussian_rotation_interpolation_fintype L M f hf
      hf_bound hdf_bound hddf_bound θ
    simp_rw [SlepianProof.bilinear_disjoint_rotation _ _ _ _ _ (hindep _)] at h
    simp_rw [integral_const_mul] at h
    change HasDerivAt I (∑ i : κ, (Real.cos θ * Real.sin θ) *
      (∫ x, fderiv ℝ (fderiv ℝ f) (Z θ x) (M (Pi.single i 1)) (M (Pi.single i 1)) -
        fderiv ℝ (fderiv ℝ f) (Z θ x) (L (Pi.single i 1)) (L (Pi.single i 1)) ∂μ)) θ at h
    have hsub (i : κ) := integral_sub (hi θ M i) (hi θ L i)
    simp_rw [hsub] at h
    rw [← Finset.mul_sum, Finset.sum_sub_distrib] at h
    exact h
  let J (θ : ℝ) := I θ + C * (Real.sin θ)^2
  have hdJ (θ : ℝ) : HasDerivAt J
      (Real.cos θ * Real.sin θ * (T θ M - T θ L) +
        C * (2 * Real.sin θ * Real.cos θ)) θ := by
    convert (hd θ).add (((Real.hasDerivAt_sin θ).pow 2).const_mul C) using 1 <;>
      solve | rfl | ring
  have hJdiff : Differentiable ℝ J := fun θ => (hdJ θ).differentiableAt
  have hJnonneg (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) : 0 ≤ deriv J θ := by
    rw [(hdJ θ).deriv]
    have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
      (hθ.2.trans (by linarith [Real.pi_pos]))
    have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
    have ht : T θ L - T θ M ≤ 2 * C := htrace θ hθ
    have h := mul_le_mul_of_nonneg_left ht (mul_nonneg hc hs)
    nlinarith
  have hm := monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) (Real.pi / 2))
    hJdiff.continuous.continuousOn hJdiff.differentiableOn
    (fun θ hθ => hJnonneg θ (interior_subset hθ))
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have h := hm ⟨le_rfl, hpi⟩ ⟨hpi, le_rfl⟩ hpi
  simpa [J, I, Z, μ] using h

end GaussianConcentration

end

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

/-- Independent blocks factorize expectations. The proof uses the actual product law,
so it does not assume independence as a new hypothesis. -/
lemma gaussian_blocks_integral_product {n : ℕ}
    (f g : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f) (hg : Continuous g) :
    (∫ x, f (gaussianBlock1 n x) * g (gaussianBlock2 n x)
      ∂Measure.pi (fun _ : TripleIndex n => gaussianReal 0 1)) =
      (∫ x, f x ∂stdGaussian (EuclideanSpace ℝ (Fin n))) *
      (∫ x, g x ∂stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  let e := (EuclideanSpace.equiv (Fin n) ℝ).symm
  let μ := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let ν := Measure.pi (fun _ : Fin n ⊕ Fin n => gaussianReal 0 1)
  let P : (TripleIndex n → ℝ) →L[ℝ] ((Fin n ⊕ Fin n) → ℝ) :=
    { toFun x i := x (Sum.inr i)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hp : MeasurePreserving P (Measure.pi (fun _ : TripleIndex n => gaussianReal 0 1)) ν :=
    (measurePreserving_snd (μ := μ) (ν := ν)).comp
      (measurePreserving_sumPiEquivProdPi (fun _ : TripleIndex n => gaussianReal 0 1))
  let H (x : (Fin n ⊕ Fin n) → ℝ) :=
    f (e (fun i => x (Sum.inl i))) * g (e (fun i => x (Sum.inr i)))
  have hH : Continuous H := by
    apply Continuous.mul
    · exact hf.comp (e.continuous.comp (continuous_pi fun i => continuous_apply _))
    · exact hg.comp (e.continuous.comp (continuous_pi fun i => continuous_apply _))
  have h₁ := integral_map (μ := Measure.pi (fun _ : TripleIndex n => gaussianReal 0 1)) hp.measurable.aemeasurable hH.aestronglyMeasurable
  rw [hp.map_eq] at h₁
  have h₂ := (measurePreserving_sumPiEquivProdPi
    (fun _ : Fin n ⊕ Fin n => gaussianReal 0 1)).integral_comp'
    (fun z : (Fin n → ℝ) × (Fin n → ℝ) => f (e z.1) * g (e z.2))
  change (∫ x, H x ∂ν) = ∫ z, f (e z.1) * g (e z.2) ∂μ.prod μ at h₂
  have h₃ := integral_prod_mul (μ := μ) (ν := μ) (fun x => f (e x)) (fun x => g (e x))
  have he : μ.map e = stdGaussian (EuclideanSpace ℝ (Fin n)) := map_pi_eq_stdGaussian
  have hfi := integral_map (μ := μ) e.continuous.measurable.aemeasurable hf.aestronglyMeasurable
  have hgi := integral_map (μ := μ) e.continuous.measurable.aemeasurable hg.aestronglyMeasurable
  rw [he] at hfi hgi
  calc
    _ = ∫ x, H (P x) ∂Measure.pi (fun _ : TripleIndex n => gaussianReal 0 1) := rfl
    _ = ∫ x, H x ∂ν := h₁.symm
    _ = ∫ z, f (e z.1) * g (e z.2) ∂μ.prod μ := h₂
    _ = (∫ x, f (e x) ∂μ) * (∫ x, g (e x) ∂μ) := h₃
    _ = _ := by rw [← hfi, ← hgi]

end GaussianConcentration

end

section

open MeasureTheory ProbabilityTheory

namespace GaussianConcentration

set_option maxHeartbeats 1800000

/-- Sharp exponential covariance for bounded C² Lipschitz functions with bounded Hessian.
These bounds justify interpolation; they will be removed by Lipschitz-preserving approximation. -/
lemma bounded_smooth_gaussian_covariance {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 2 f)
    {K : NNReal} (hLip : LipschitzWith K f) {C H : ℝ}
    (hf0 : ∀ x, ‖f x‖ ≤ C) (hf2 : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ H)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    (∫ x, f x * Real.exp (lam * f x) ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤
      ((∫ x, f x ∂stdGaussian (EuclideanSpace ℝ (Fin n))) + (K : ℝ)^2 * lam) *
        (∫ x, Real.exp (lam * f x) ∂stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  let E := EuclideanSpace ℝ (Fin n)
  let μ := Measure.pi (fun _ : TripleIndex n => gaussianReal 0 1)
  let γ := stdGaussian E
  let g := fun x => Real.exp (lam * f x)
  let F := fun z : E × E => g z.1 * f z.2
  let L := (gaussianBlock0 n).prod (gaussianBlock0 n)
  let M := (gaussianBlock1 n).prod (gaussianBlock2 n)
  let A := Real.exp (|lam| * C)
  let Dg := |lam| * A * (K : ℝ)
  let Hg := A * (|lam|^2 * (K : ℝ)^2 + |lam| * H)
  let DF := A * (K : ℝ) + C * Dg
  let HF := Dg * (K : ℝ) + A * H + (K : ℝ) * Dg + C * Hg
  have hC : 0 ≤ C := (norm_nonneg _).trans (hf0 0)
  have hH : 0 ≤ H := (norm_nonneg (fderiv ℝ (fderiv ℝ f) 0)).trans (hf2 0)
  have hf1 (x : E) : ‖fderiv ℝ f x‖ ≤ (K : ℝ) :=
    norm_fderiv_le_of_lipschitz ℝ hLip
  obtain ⟨hg0, hg1, hg2⟩ := bounded_exponential_derivatives hf hC K.coe_nonneg hH hf0 hf1 hf2 lam
  have hg : ContDiff ℝ 2 g := (contDiff_const.mul hf).exp
  have hF : ContDiff ℝ 2 F :=
    (hg.comp (ContinuousLinearMap.fst ℝ E E).contDiff).mul
      (hf.comp (ContinuousLinearMap.snd ℝ E E).contDiff)
  have hF0 (z : E × E) : ‖F z‖ ≤ A * C := by
    exact (norm_mul _ _).trans_le (mul_le_mul (hg0 _) (hf0 _) (norm_nonneg _) (by positivity))
  have hF1 (z : E × E) : ‖fderiv ℝ F z‖ ≤ DF :=
    product_fderiv_bound (hg.differentiable (by norm_num)) (hf.differentiable (by norm_num))
      (by positivity) hC (by positivity) K.coe_nonneg hg0 hf0 hg1 hf1 z
  have hF2 (z : E × E) : ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ HF :=
    product_hessian_bound hg hf (by positivity) hC (by positivity) K.coe_nonneg
      (by positivity) hH hg0 hf0 hg1 hf1 hg2 hf2 z
  have hindep (k : TripleIndex n) : L (Pi.single k 1) = 0 ∨ M (Pi.single k 1) = 0 := by
    cases k with
    | inl i => right; simp [M]
    | inr k => left; cases k <;> simp [L]
  let Z (θ : ℝ) := Real.cos θ • L + Real.sin θ • M
  have hBcont : Continuous (fderiv ℝ (fderiv ℝ F)) :=
    (hF.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuous_fderiv one_ne_zero
  have hi (θ : ℝ) (P : (TripleIndex n → ℝ) →L[ℝ] E × E) (k : TripleIndex n) :
      Integrable (fun x => fderiv ℝ (fderiv ℝ F) (Z θ x)
        (P (Pi.single k 1)) (P (Pi.single k 1))) μ := by
    have hc : Continuous (fun x => fderiv ℝ (fderiv ℝ F) (Z θ x)
        (P (Pi.single k 1)) (P (Pi.single k 1))) :=
      ((hBcont.comp (Z θ).continuous).clm_apply continuous_const).clm_apply continuous_const
    have hb (x : TripleIndex n → ℝ) : ‖fderiv ℝ (fderiv ℝ F) (Z θ x)
        (P (Pi.single k 1)) (P (Pi.single k 1))‖ ≤
        HF * ‖P (Pi.single k 1)‖ * ‖P (Pi.single k 1)‖ :=
      bilinear_apply_bound _ (hF2 _) _ _
    simpa only [mul_one] using (integrable_const (1 : ℝ) (μ := μ)).bdd_mul
      hc.aestronglyMeasurable (ae_of_all _ hb)
  have hgi (θ : ℝ) : Integrable (fun x => g (Z θ x).1) μ := by
    have hc : Continuous (fun x => g (Z θ x).1) :=
      hg.continuous.comp (continuous_fst.comp (Z θ).continuous)
    simpa only [mul_one] using (integrable_const (1 : ℝ) (μ := μ)).bdd_mul
      hc.aestronglyMeasurable (ae_of_all _ fun x => hg0 _)
  have hgm (θ : ℝ) : (∫ x, g (Z θ x).1 ∂μ) = ∫ x, g x ∂γ := by
    let P := Real.cos θ • gaussianBlock0 n + Real.sin θ • gaussianBlock1 n
    have hmap : μ.map P = γ := gaussianBlock_rotation_map θ
    have h := integral_map (μ := μ) P.continuous.measurable.aemeasurable hg.continuous.aestronglyMeasurable
    rw [hmap] at h
    change (∫ x, g x ∂γ) = ∫ x, g (P x) ∂μ at h
    convert h.symm using 1
    apply integral_congr_ae
    filter_upwards [] with x
    rfl
  have htrace (θ : ℝ) :
      (∑ k : TripleIndex n, ∫ x, fderiv ℝ (fderiv ℝ F) (Z θ x)
        (L (Pi.single k 1)) (L (Pi.single k 1)) ∂μ) -
      (∑ k : TripleIndex n, ∫ x, fderiv ℝ (fderiv ℝ F) (Z θ x)
        (M (Pi.single k 1)) (M (Pi.single k 1)) ∂μ) ≤
        2 * (lam * (K : ℝ)^2 * ∫ x, g x ∂γ) := by
    have hLi := integrable_finsetSum Finset.univ (fun k _ => hi θ L k)
    have hMi := integrable_finsetSum Finset.univ (fun k _ => hi θ M k)
    rw [← integral_finsetSum Finset.univ (fun k _ => hi θ L k),
      ← integral_finsetSum Finset.univ (fun k _ => hi θ M k), ← integral_sub hLi hMi]
    have hpoint (x : TripleIndex n → ℝ) :
        (∑ k : TripleIndex n, fderiv ℝ (fderiv ℝ F) (Z θ x)
          (L (Pi.single k 1)) (L (Pi.single k 1))) -
        (∑ k : TripleIndex n, fderiv ℝ (fderiv ℝ F) (Z θ x)
          (M (Pi.single k 1)) (M (Pi.single k 1))) ≤
          (2 * lam * (K : ℝ)^2) * g (Z θ x).1 := by
      have h := exponential_product_trace_bound hf hLip hlam (Z θ x)
      change _ ≤ (2 * lam * (K : ℝ)^2) * g (Z θ x).1 at h
      have hzero : fderiv ℝ (fderiv ℝ F) (Z θ x) (0, 0) (0, 0) = 0 := by
        change fderiv ℝ (fderiv ℝ F) (Z θ x) 0 0 = 0
        simp
      simpa [Fintype.sum_sum_type, L, M, hzero, sub_add_eq_sub_sub] using h
    have hb := integral_mono (hLi.sub hMi) ((hgi θ).const_mul (2 * lam * (K : ℝ)^2)) hpoint
    rw [integral_const_mul, hgm] at hb
    exact hb.trans_eq (by ring)
  have h := gaussian_rotation_covariance_bound L M F hF hF0 hF1 hF2 hindep
    (fun θ _ => htrace θ)
  have hleft : (∫ x, F (L x) ∂μ) = ∫ x, g x * f x ∂γ := by
    have hm : μ.map (gaussianBlock0 n) = γ := gaussianBlock0_map
    have h := integral_map (μ := μ) (gaussianBlock0 n).continuous.measurable.aemeasurable
      (hg.continuous.mul hf.continuous).aestronglyMeasurable
    rw [hm] at h
    exact h.symm
  have hright : (∫ x, F (M x) ∂μ) = (∫ x, g x ∂γ) * (∫ x, f x ∂γ) :=
    gaussian_blocks_integral_product g f hg.continuous hf.continuous
  change (∫ x, F (L x) ∂μ) ≤ (∫ x, F (M x) ∂μ) +
    lam * (K : ℝ)^2 * (∫ x, g x ∂γ) at h
  rw [hleft, hright] at h
  calc
    _ = ∫ x, g x * f x ∂γ := by apply integral_congr_ae; filter_upwards [] with x; dsimp [g]; ring
    _ ≤ (∫ x, g x ∂γ) * (∫ x, f x ∂γ) + lam * (K : ℝ)^2 * (∫ x, g x ∂γ) := h
    _ = _ := by dsimp [γ, g, E]; ring

end GaussianConcentration

end

section

open Real Set

namespace GaussianConcentration

set_option maxHeartbeats 800000

/-- The last analytic step of the sharp Gaussian concentration proof. A covariance bound
on the MGF derivative integrates to the exact variance proxy, without dividing by the MGF. -/
lemma mgf_bound_of_derivative {M M' : ℝ → ℝ} {m c : ℝ}
    (hderiv : ∀ x, HasDerivAt M (M' x) x) (hzero : M 0 = 1)
    (hbound : ∀ x, 0 ≤ x → M' x ≤ (m + c*x) * M x)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    M lam ≤ exp (m*lam + c*lam^2/2) := by
  let H : ℝ → ℝ := fun x => exp (-(m*x + c*x^2/2)) * M x
  have hq (x : ℝ) : HasDerivAt (fun y : ℝ => m*y+c*y^2/2) (m+c*x) x := by
    convert ((hasDerivAt_id x).const_mul m).add
      ((((hasDerivAt_id x).pow 2).const_mul c).div_const 2) using 1 <;>
        (try simp only [id_eq, mul_one, Nat.cast_ofNat, pow_one]) <;>
        (solve | ring | rfl | (funext y; simp only [Pi.add_apply, Pi.pow_apply, id_eq]; ring))
  have hd (x : ℝ) : HasDerivAt H
      (exp (-(m*x+c*x^2/2)) * (M' x - (m+c*x)*M x)) x := by
    convert ((hq x).neg.exp).mul (hderiv x) using 1 <;> (try dsimp [H]) <;>
      (solve | ring | rfl | (funext y; simp only [Pi.mul_apply]; congr 1; ring))
  have hHc : Continuous H := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  have hanti : AntitoneOn H (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hHc.continuousOn
    · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hd x).deriv]
      apply mul_nonpos_of_nonneg_of_nonpos (exp_pos _).le
      have hx0 : 0 ≤ x := interior_subset hx
      exact sub_nonpos.mpr (hbound x hx0)
  have hH : H lam ≤ 1 := by
    have h := hanti (by simp : (0 : ℝ) ∈ Ici 0) hlam hlam
    simpa only [H, mul_zero, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero,
      neg_zero, exp_zero, one_mul, hzero] using h
  have h := mul_le_mul_of_nonneg_left hH (exp_pos (m*lam+c*lam^2/2)).le
  simpa [H, ← mul_assoc, ← exp_add] using h

end GaussianConcentration

end

section

open MeasureTheory ProbabilityTheory Real Set

namespace GaussianConcentration

set_option maxHeartbeats 800000

/-- Integrating the exponential covariance estimate gives the centered MGF bound.
The covariance estimate is the outstanding analytic input, explicitly recorded here. -/
lemma centered_mgf_bound_of_covariance {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (f : Ω → ℝ) (c : ℝ)
    (hi : ∀ lam : ℝ, Integrable (fun ω => exp (lam*f ω)) μ)
    (hcov : ∀ lam : ℝ, 0 ≤ lam →
      (∫ ω, f ω * exp (lam*f ω) ∂μ) ≤
        ((∫ ω, f ω ∂μ) + c*lam) * (∫ ω, exp (lam*f ω) ∂μ))
    {lam : ℝ} (hlam : 0 ≤ lam) :
    (∫ ω, exp (lam*(f ω - ∫ ω', f ω' ∂μ)) ∂μ) ≤ exp (c*lam^2/2) := by
  have hset : integrableExpSet f μ = univ := by
    ext t
    simp only [integrableExpSet, mem_setOf_eq, mem_univ, iff_true]
    exact hi t
  have hderiv (t : ℝ) : HasDerivAt (mgf f μ)
      (∫ ω, f ω * exp (t*f ω) ∂μ) t := by
    apply hasDerivAt_mgf
    rw [hset, interior_univ]
    exact mem_univ t
  have hb := mgf_bound_of_derivative hderiv (by simp [mgf]) hcov hlam
  have he : (∫ ω, exp (lam*(f ω - ∫ ω', f ω' ∂μ)) ∂μ) =
      exp (-lam*∫ ω, f ω ∂μ) * mgf f μ lam := by
    simp_rw [mul_sub, sub_eq_add_neg, exp_add]
    rw [integral_mul_const]
    dsimp [mgf]
    simp only [neg_mul]
    ring
  rw [he]
  apply (mul_le_mul_of_nonneg_left hb (exp_pos _).le).trans_eq
  rw [← exp_add]
  congr 1
  ring

end GaussianConcentration

end

section

open MeasureTheory ProbabilityTheory Real

namespace GaussianConcentration

set_option maxHeartbeats 800000

lemma native_lipschitz {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ}
    (hf : HighDimStat.TailBounds.IsLLipschitz f L) : LipschitzWith ‖L‖₊ f := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, dist_eq_norm]
  exact (hf x y).trans (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _))

section Gaussian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ] {K : NNReal} {f : E → ℝ}

lemma lipschitz_growth (hf : LipschitzWith K f) (x : E) :
    ‖f x‖ ≤ (K : ℝ) * ‖x‖ + ‖f 0‖ := by
  have h := hf.dist_le_mul x 0
  rw [Real.dist_eq, dist_zero_right] at h
  calc
    ‖f x‖ = ‖(f x - f 0) + f 0‖ := by congr 1; ring
    _ ≤ ‖f x - f 0‖ + ‖f 0‖ := norm_add_le _ _
    _ ≤ _ := by rw [Real.norm_eq_abs]; linarith

/-- Lipschitz Gaussian observables are integrable without a separate integrability premise. -/
lemma gaussian_lipschitz_integrable (hf : LipschitzWith K f) : Integrable f μ := by
  refine ((IsGaussian.integrable_id (μ := μ)).norm.const_mul (K : ℝ) |>.add
    (integrable_const ‖f 0‖)).mono' hf.continuous.aestronglyMeasurable ?_
  exact ae_of_all _ (lipschitz_growth hf)

/-- Every exponential moment of a Lipschitz Gaussian observable exists. Fernique's theorem
supplies a quadratic envelope; this asserts existence, not the sharp concentration estimate. -/
lemma gaussian_lipschitz_exp_integrable (hf : LipschitzWith K f) (lam : ℝ) :
    Integrable (fun x => exp (lam * f x)) μ := by
  obtain ⟨c, hc, hi⟩ := IsGaussian.exists_integrable_exp_sq μ
  let B : ℝ := |lam| * (K : ℝ)
  let D : ℝ := |lam| * ‖f 0‖ + B^2/(4*c)
  have henv (x : E) : lam * f x ≤ D + c * ‖x‖^2 := by
    have hy : B * ‖x‖ ≤ c * ‖x‖^2 + B^2/(4*c) := by
      have hs := sq_nonneg (2*c*‖x‖-B)
      have he : B^2/(4*c)*(4*c) = B^2 := by field_simp
      nlinarith
    calc
      lam * f x ≤ |lam * f x| := le_abs_self _
      _ = |lam| * ‖f x‖ := by rw [abs_mul, Real.norm_eq_abs]
      _ ≤ |lam| * ((K : ℝ)*‖x‖ + ‖f 0‖) :=
        mul_le_mul_of_nonneg_left (lipschitz_growth hf x) (abs_nonneg _)
      _ ≤ D + c * ‖x‖^2 := by dsimp [B, D] at *; nlinarith
  refine (hi.const_mul (exp D)).mono'
    (Real.continuous_exp.comp (hf.continuous.const_mul lam)).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  calc
    exp (lam*f x) ≤ exp (D+c*‖x‖^2) := exp_le_exp.mpr (henv x)
    _ = exp D * exp (c*‖x‖^2) := exp_add _ _

lemma gaussian_lipschitz_centered_exp_integrable (hf : LipschitzWith K f) (lam : ℝ) :
    Integrable (fun x => exp (lam * (f x - ∫ y, f y ∂μ))) μ := by
  have hi := (gaussian_lipschitz_exp_integrable μ hf lam).mul_const
    (exp (-lam * ∫ y, f y ∂μ))
  simpa only [mul_sub, mul_add, mul_neg, sub_eq_add_neg, exp_add, neg_mul] using hi

end Gaussian

end GaussianConcentration

end

section

open MeasureTheory ProbabilityTheory

namespace GaussianConcentration

set_option maxHeartbeats 1000000

lemma bounded_smooth_gaussian_mgf_nonneg {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 2 f)
    {K : NNReal} (hLip : LipschitzWith K f) {C H : ℝ}
    (hf0 : ∀ x, ‖f x‖ ≤ C) (hf2 : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ H)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    (∫ x, Real.exp (lam * (f x - ∫ y, f y ∂stdGaussian (EuclideanSpace ℝ (Fin n))))
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤ Real.exp ((K : ℝ)^2 * lam^2 / 2) := by
  exact centered_mgf_bound_of_covariance f ((K : ℝ)^2)
    (gaussian_lipschitz_exp_integrable _ hLip)
    (fun t ht => bounded_smooth_gaussian_covariance f hf hLip hf0 hf2 ht) hlam

/-- The full sharp MGF estimate for the bounded smooth stage. It includes negative
parameters and zero dimension; the approximation step is still needed for the native root. -/
lemma bounded_smooth_gaussian_mgf {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 2 f)
    {K : NNReal} (hLip : LipschitzWith K f) {C H : ℝ}
    (hf0 : ∀ x, ‖f x‖ ≤ C) (hf2 : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ H) (lam : ℝ) :
    (∫ x, Real.exp (lam * (f x - ∫ y, f y ∂stdGaussian (EuclideanSpace ℝ (Fin n))))
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤ Real.exp ((K : ℝ)^2 * lam^2 / 2) := by
  by_cases hlam : 0 ≤ lam
  · exact bounded_smooth_gaussian_mgf_nonneg f hf hLip hf0 hf2 hlam
  · have hneg : 0 ≤ -lam := by linarith
    have hfneg0 (x) : ‖(-f) x‖ ≤ C := by simpa using hf0 x
    have hdfneg : fderiv ℝ (-f) = fun x => -fderiv ℝ f x := by
      funext x; exact fderiv_neg
    have hfneg2 (x) : ‖fderiv ℝ (fderiv ℝ (-f)) x‖ ≤ H := by
      rw [hdfneg, fderiv_fun_neg, ContinuousLinearMap.opNorm_neg]
      exact hf2 x
    have hb := bounded_smooth_gaussian_mgf_nonneg (-f) hf.neg hLip.neg hfneg0 hfneg2 hneg
    convert hb using 1
    · apply integral_congr_ae
      filter_upwards [] with x
      simp only [Pi.neg_apply, integral_neg]
      congr 1
      ring
    · congr 1
      ring

end GaussianConcentration

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace GaussianConcentration

set_option maxHeartbeats 1000000

lemma centered_exp_integral_eq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (lam : ℝ) :
    (∫ x, Real.exp (lam * (f x - ∫ y, f y ∂μ)) ∂μ) =
      Real.exp (-lam * ∫ y, f y ∂μ) * ∫ x, Real.exp (lam * f x) ∂μ := by
  simp_rw [mul_sub, sub_eq_add_neg, Real.exp_add]
  rw [integral_mul_const]
  simp only [neg_mul]
  ring

section Limit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsGaussian μ]

/-- Gaussian exponential moments and means pass to pointwise limits at a fixed Lipschitz
constant. The uniform bound at zero supplies a single integrable Gaussian envelope. -/
lemma centered_gaussian_mgf_tendsto {K : NNReal} {fs : ℕ → E → ℝ} {f : E → ℝ}
    (hLip : ∀ n, LipschitzWith K (fs n)) {A : ℝ}
    (hzero : ∀ n, ‖fs n 0‖ ≤ A)
    (hpoint : ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x))) (lam : ℝ) :
    Tendsto (fun n => ∫ x, Real.exp (lam * (fs n x - ∫ y, fs n y ∂μ)) ∂μ) atTop
      (𝓝 (∫ x, Real.exp (lam * (f x - ∫ y, f y ∂μ)) ∂μ)) := by
  let G := fun x : E => (K : ℝ) * ‖x‖ + A
  have hG : LipschitzWith K G := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, dist_eq_norm]
    change |(K : ℝ) * ‖x‖ + A - ((K : ℝ) * ‖y‖ + A)| ≤ (K : ℝ) * ‖x-y‖
    rw [show (K : ℝ) * ‖x‖ + A - ((K : ℝ) * ‖y‖ + A) =
      (K : ℝ) * (‖x‖-‖y‖) by ring, abs_mul, abs_of_nonneg K.coe_nonneg]
    exact mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) K.coe_nonneg
  have hGi : Integrable G μ :=
    ((IsGaussian.integrable_id (μ := μ)).norm.const_mul (K : ℝ)).add (integrable_const A)
  have hbound (n : ℕ) (x : E) : ‖fs n x‖ ≤ G x := by
    calc
      ‖fs n x‖ ≤ (K : ℝ) * ‖x‖ + ‖fs n 0‖ := lipschitz_growth (hLip n) x
      _ ≤ (K : ℝ) * ‖x‖ + A := add_le_add le_rfl (hzero n)
  have hmean := tendsto_integral_of_dominated_convergence G
    (fun n => (hLip n).continuous.aestronglyMeasurable) hGi
    (fun n => ae_of_all _ (hbound n)) (ae_of_all _ hpoint)
  have hEi : Integrable (fun x => Real.exp (|lam| * G x)) μ :=
    gaussian_lipschitz_exp_integrable μ hG |lam|
  have hEbound (n : ℕ) (x : E) : ‖Real.exp (lam * fs n x)‖ ≤ Real.exp (|lam| * G x) := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      lam * fs n x ≤ |lam * fs n x| := le_abs_self _
      _ = |lam| * ‖fs n x‖ := by rw [abs_mul, Real.norm_eq_abs]
      _ ≤ |lam| * G x := mul_le_mul_of_nonneg_left (hbound n x) (abs_nonneg _)
  have hEpoint (x : E) : Tendsto (fun n => Real.exp (lam * fs n x)) atTop
      (𝓝 (Real.exp (lam * f x))) :=
    (Real.continuous_exp.tendsto _).comp (tendsto_const_nhds.mul (hpoint x))
  have hExp := tendsto_integral_of_dominated_convergence (fun x => Real.exp (|lam| * G x))
    (fun n => (Real.continuous_exp.comp ((hLip n).continuous.const_mul lam)).aestronglyMeasurable)
    hEi (fun n => ae_of_all _ (hEbound n)) (ae_of_all _ hEpoint)
  have hmean' : Tendsto (fun n => -lam * ∫ y, fs n y ∂μ) atTop
      (𝓝 (-lam * ∫ y, f y ∂μ)) := tendsto_const_nhds.mul hmean
  have h := ((Real.continuous_exp.tendsto _).comp hmean').mul hExp
  simp_rw [centered_exp_integral_eq]
  exact h

lemma gaussian_mgf_bound_of_lipschitz_approximation {K : NNReal}
    {fs : ℕ → E → ℝ} {f : E → ℝ} (hLip : ∀ n, LipschitzWith K (fs n)) {A : ℝ}
    (hzero : ∀ n, ‖fs n 0‖ ≤ A)
    (hpoint : ∀ x, Tendsto (fun n => fs n x) atTop (𝓝 (f x)))
    (hmgf : ∀ n lam, (∫ x, Real.exp (lam * (fs n x - ∫ y, fs n y ∂μ)) ∂μ) ≤
      Real.exp ((K : ℝ)^2 * lam^2 / 2)) (lam : ℝ) :
    (∫ x, Real.exp (lam * (f x - ∫ y, f y ∂μ)) ∂μ) ≤
      Real.exp ((K : ℝ)^2 * lam^2 / 2) := by
  exact le_of_tendsto (centered_gaussian_mgf_tendsto μ hLip hzero hpoint lam)
    (Eventually.of_forall fun n => hmgf n lam)

end Limit

end GaussianConcentration

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace GaussianConcentration

set_option maxHeartbeats 1400000

/-- The smoothness and Hessian assumptions have been removed. Normalized compact kernels
approximate the bounded Lipschitz observable at precisely the same Lipschitz constant. -/
lemma bounded_lipschitz_gaussian_mgf {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) {K : NNReal} (hf : LipschitzWith K f)
    {C : ℝ} (hf_bound : ∀ x, ‖f x‖ ≤ C) (lam : ℝ) :
    (∫ x, Real.exp (lam * (f x - ∫ y, f y ∂stdGaussian (EuclideanSpace ℝ (Fin n))))
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤ Real.exp ((K : ℝ)^2 * lam^2 / 2) := by
  let φ (k : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    { rIn := (1 / ((k : ℝ) + 1)) / 2
      rOut := 1 / ((k : ℝ) + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := half_lt_self (by positivity) }
  have hs (k : ℕ) := bounded_lipschitz_bump_smoothing hf hf_bound (φ k)
  choose gs hgs using hs
  have hLip (k : ℕ) : LipschitzWith K (gs k) := (hgs k).2.1
  have hzero (k : ℕ) : ‖gs k 0‖ ≤ C := (hgs k).2.2.1 0
  have hε : Tendsto (fun k : ℕ => (K : ℝ) * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hpoint (x : EuclideanSpace ℝ (Fin n)) : Tendsto (fun k => gs k x) atTop (𝓝 (f x)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    refine squeeze_zero (fun _ => dist_nonneg) ?_ hε
    intro k
    rw [Real.dist_eq]
    exact (hgs k).2.2.2.2 x
  have hmgf (k : ℕ) (t : ℝ) :
      (∫ x, Real.exp (t * (gs k x - ∫ y, gs k y ∂stdGaussian (EuclideanSpace ℝ (Fin n))))
        ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤ Real.exp ((K : ℝ)^2 * t^2 / 2) := by
    obtain ⟨H, hH⟩ := (hgs k).2.2.2.1
    exact bounded_smooth_gaussian_mgf (gs k) (hgs k).1 (hLip k) (hgs k).2.2.1 hH t
  exact gaussian_mgf_bound_of_lipschitz_approximation _ hLip hzero hpoint hmgf lam

end GaussianConcentration

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace GaussianConcentration

set_option maxHeartbeats 1400000

lemma real_clip_norm_le {R : ℝ} (hR : 0 ≤ R) (t : ℝ) :
    ‖max (-R) (min R t)‖ ≤ ‖t‖ := by
  have hLip : LipschitzWith 1 (fun t : ℝ => max (-R) (min R t)) :=
    (LipschitzWith.id.const_min R).const_max (-R)
  have hzero : max (-R) (min R (0 : ℝ)) = 0 := by
    rw [min_eq_right hR, max_eq_right (by linarith)]
  simpa only [hzero, Real.dist_eq, sub_zero, one_mul, NNReal.coe_one, Real.norm_eq_abs] using
    hLip.dist_le_mul t 0

/-- The sharp standard Gaussian MGF bound for every Lipschitz observable, with no
boundedness, smoothness, or extra integrability hypotheses. -/
lemma gaussian_lipschitz_mgf {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) {K : NNReal} (hf : LipschitzWith K f) (lam : ℝ) :
    (∫ x, Real.exp (lam * (f x - ∫ y, f y ∂stdGaussian (EuclideanSpace ℝ (Fin n))))
      ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤ Real.exp ((K : ℝ)^2 * lam^2 / 2) := by
  let fs (k : ℕ) := fun x => max (-(k : ℝ)) (min (k : ℝ) (f x))
  have hLip (k : ℕ) : LipschitzWith K (fs k) :=
    (hf.const_min (k : ℝ)).const_max (-(k : ℝ))
  have hbound (k : ℕ) (x) : ‖fs k x‖ ≤ (k : ℝ) := by
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    refine ⟨le_max_left _ _, max_le ?_ (min_le_left _ _)⟩
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hzero (k : ℕ) : ‖fs k 0‖ ≤ ‖f 0‖ := real_clip_norm_le (Nat.cast_nonneg k) (f 0)
  have hpoint (x : EuclideanSpace ℝ (Fin n)) : Tendsto (fun k => fs k x) atTop (𝓝 (f x)) := by
    obtain ⟨N, hN⟩ := exists_nat_ge |f x|
    have he : (fun k => fs k x) =ᶠ[atTop] (fun _ => f x) := by
      filter_upwards [eventually_ge_atTop N] with k hk
      have habs : |f x| ≤ (k : ℝ) := hN.trans (by exact_mod_cast hk)
      have hlow : -(k : ℝ) ≤ f x := (abs_le.mp habs).1
      have hhigh : f x ≤ (k : ℝ) := (abs_le.mp habs).2
      dsimp [fs]
      rw [min_eq_right hhigh, max_eq_right hlow]
    exact tendsto_const_nhds.congr' he.symm
  have hmgf (k : ℕ) (t : ℝ) := bounded_lipschitz_gaussian_mgf (fs k) (hLip k) (hbound k) t
  exact gaussian_mgf_bound_of_lipschitz_approximation _ hLip hzero hpoint hmgf lam

end GaussianConcentration

end

section

open MeasureTheory ProbabilityTheory

namespace HighDimStat.TailBounds

/-- **Theorem 2.26** (Gaussian concentration of Lipschitz functions), Wainwright,
*High-Dimensional Statistics* (2019), p. 40. Let `(X1,...,Xn)` be a vector of i.i.d. standard
Gaussian variables, and let `f : ℝ^n → ℝ` be `L`-Lipschitz with respect to the Euclidean norm.
Then `f(X) - E[f(X)]` is sub-Gaussian with parameter at most `L`, and hence
`P[|f(X)-E[f(X)]| ≥ t] ≤ 2e^{-t²/2L²}` for all `t ≥ 0`. -/
theorem lipschitz_gaussian_concentration_of_standard_mgf {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {Prob : Measure Ω} [IsProbabilityMeasure Prob] (X : Ω → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ)
    (hcore : ∀ (g : EuclideanSpace ℝ (Fin n) → ℝ) (K : NNReal), LipschitzWith K g →
      ∀ lam : ℝ, (∫ x, Real.exp (lam * (g x - ∫ y, g y ∂stdGaussian (EuclideanSpace ℝ (Fin n))))
        ∂stdGaussian (EuclideanSpace ℝ (Fin n))) ≤ Real.exp ((K : ℝ)^2 * lam^2/2))
    (hXGauss : HasGaussianLaw X Prob)
    (hXmean : ∀ i, ∫ ω, X ω i ∂Prob = 0)
    (hXcov : ∀ i j, ∫ ω, X ω i * X ω j ∂Prob = if i = j then 1 else 0)
    (hLip : IsLLipschitz f L) :
    IsSubGaussian (fun ω => f (X ω) - ∫ ω', f (X ω') ∂Prob) Prob L ∧
    ∀ t : ℝ, 0 ≤ t →
      Prob.real {ω | t ≤ |f (X ω) - ∫ ω', f (X ω') ∂Prob|} ≤ 2 * Real.exp (-(t ^ 2) / (2 * L ^ 2))
    := by
  let γ := stdGaussian (EuclideanSpace ℝ (Fin n))
  let K : NNReal := ‖L‖₊
  let Z : Ω → ℝ := fun ω => f (X ω) - ∫ ω', f (X ω') ∂Prob
  have hf := GaussianConcentration.native_lipschitz hLip
  have hlaw := GaussianConcentration.gaussian_map_eq_standard X hXGauss hXmean hXcov
  have hFint : Integrable (fun ω => f (X ω)) Prob := by
    have hi : Integrable f (Prob.map X) := by
      rw [hlaw]
      exact GaussianConcentration.gaussian_lipschitz_integrable _ hf
    exact hi.comp_aemeasurable hXGauss.aemeasurable
  have hFmean : (∫ ω, f (X ω) ∂Prob) = ∫ x, f x ∂γ := by
    rw [← integral_map hXGauss.aemeasurable hf.continuous.aestronglyMeasurable, hlaw]
  have hZint : Integrable Z Prob := hFint.sub (integrable_const _)
  have hZmean : (∫ ω, Z ω ∂Prob) = 0 := by
    change (∫ ω, f (X ω) - ∫ ω', f (X ω') ∂Prob ∂Prob) = 0
    rw [integral_sub hFint (integrable_const _)]
    simp
  have hZmgf : HasSubgaussianMGF Z (K^2) Prob := by
    constructor
    · intro lam
      have hi : Integrable (fun x => Real.exp (lam * (f x - ∫ y, f y ∂γ))) (Prob.map X) := by
        rw [hlaw]
        exact GaussianConcentration.gaussian_lipschitz_centered_exp_integrable _ hf lam
      simpa only [Z, hFmean, Function.comp_def] using hi.comp_aemeasurable hXGauss.aemeasurable
    · intro lam
      change (∫ ω, Real.exp (lam * Z ω) ∂Prob) ≤ _
      have he : (∫ ω, Real.exp (lam * Z ω) ∂Prob) =
          ∫ x, Real.exp (lam * (f x - ∫ y, f y ∂γ)) ∂γ := by
        have hsm : AEStronglyMeasurable
            (fun x => Real.exp (lam * (f x - ∫ y, f y ∂γ))) (Prob.map X) :=
          (Real.continuous_exp.comp
            ((hf.continuous.sub continuous_const).const_mul lam)).aestronglyMeasurable
        dsimp [Z]
        rw [hFmean, ← integral_map hXGauss.aemeasurable hsm, hlaw]
      rw [he]
      simpa only [NNReal.coe_pow] using hcore f K hf lam
  have hKsq : (K : ℝ)^2 = L^2 := by simp [K, Real.norm_eq_abs]
  constructor
  · change IsSubGaussian Z Prob L
    unfold IsSubGaussian
    refine ⟨hZint, ?_, ?_⟩
    · intro lam
      simpa only [hZmean, sub_zero] using hZmgf.integrable_exp_mul lam
    · intro lam
      simpa only [hZmean, sub_zero, mgf, NNReal.coe_pow, hKsq] using hZmgf.mgf_le lam
  · intro t ht
    have hp := hZmgf.measure_ge_le ht
    have hn := hZmgf.neg.measure_ge_le ht
    have hsub : {ω | t ≤ |Z ω|} ⊆ {ω | t ≤ Z ω} ∪ {ω | t ≤ -Z ω} := by
      intro ω hω
      change t ≤ |Z ω| at hω
      change t ≤ Z ω ∨ t ≤ -Z ω
      exact le_abs.mp hω
    change Prob.real {ω | t ≤ |Z ω|} ≤ _
    calc
      _ ≤ Prob.real ({ω | t ≤ Z ω} ∪ {ω | t ≤ -Z ω}) := measureReal_mono hsub
      _ ≤ Prob.real {ω | t ≤ Z ω} + Prob.real {ω | t ≤ -Z ω} := measureReal_union_le _ _
      _ ≤ 2 * Real.exp (-(t^2)/(2*L^2)) := by
        simp only [NNReal.coe_pow, hKsq, Pi.neg_apply] at hp hn
        linarith


end HighDimStat.TailBounds

end

open MeasureTheory ProbabilityTheory HighDimStat.TailBounds

theorem solution {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {Prob : Measure Ω} [IsProbabilityMeasure Prob] (X : Ω → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ)
    (hXGauss : HasGaussianLaw X Prob)
    (hXmean : ∀ i, ∫ ω, X ω i ∂Prob = 0)
    (hXcov : ∀ i j, ∫ ω, X ω i * X ω j ∂Prob = if i = j then 1 else 0)
    (hLip : IsLLipschitz f L) :
    IsSubGaussian (fun ω => f (X ω) - ∫ ω', f (X ω') ∂Prob) Prob L ∧
    ∀ t : ℝ, 0 ≤ t →
      Prob.real {ω | t ≤ |f (X ω) - ∫ ω', f (X ω') ∂Prob|} ≤ 2 * Real.exp (-(t ^ 2) / (2 * L ^ 2))
    := by
  exact HighDimStat.TailBounds.lipschitz_gaussian_concentration_of_standard_mgf X f L
    (fun g K hg lam => GaussianConcentration.gaussian_lipschitz_mgf g hg lam)
    hXGauss hXmean hXcov hLip

#print axioms solution
