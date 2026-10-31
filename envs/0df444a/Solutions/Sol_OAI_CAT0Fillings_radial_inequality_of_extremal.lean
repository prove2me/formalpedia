-- Prove2me | solution 1 for OAI.CAT0Fillings.radial_inequality_of_extremal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T03:13:16.262505+00:00
-- url     : https://prove2.me/submissions/e0afb314-212a-4bae-bb4a-3e7f737a5296

import Mathlib
import Definitions.Def_SharpCAT0Filling
import Definitions.Def_OAIQ29C0002

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Calculus_Smoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal

namespace CAT0Fillings
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [IsAddHaarMeasure μ]
lemma hasFDerivAt_convolution_lipschitz {f g : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hg : Continuous g) (hgc : HasCompactSupport g) (x : E) :
    HasFDerivAt (g ⋆[lsmul ℝ ℝ, μ] f)
      ((g ⋆[lsmul ℝ ℝ, μ] (fderiv ℝ f)) x) x := by
  have hsub := (μ.measurePreserving_sub_left x).quasiMeasurePreserving
  have hD : ∀ᵐ t ∂μ, DifferentiableAt ℝ f (x - t) :=
    hsub.ae (hf.ae_differentiableAt (μ := μ))
  have hgI := hg.integrable_of_hasCompactSupport (μ := μ) hgc
  have hFI (y : E) : Integrable (fun t => g t * f (y-t)) μ :=
    (hg.mul (hf.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hgc.mul_right
  have hDm : AEStronglyMeasurable (fun t => g t • fderiv ℝ f (x-t)) μ :=
    hg.aestronglyMeasurable.smul
      ((measurable_fderiv ℝ f).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  have hdif : ∀ᵐ t ∂μ, HasFDerivAt (fun y => g t * f (y-t))
      (g t • fderiv ℝ f (x-t)) x := by
    filter_upwards [hD] with t ht
    simpa +unfoldPartialApp [Function.comp_def, Pi.smul_apply, smul_eq_mul] using
      ((ht.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const t)).const_mul (g t))
  have hbound : ∀ᵐ t ∂μ, ∀ y ∈ (univ : Set E),
      ‖g t * f (y-t) - g t * f (x-t)‖ ≤ (‖g t‖ * K) * ‖y-x‖ := by
    filter_upwards with t y _
    rw [← mul_sub, norm_mul, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simpa [dist_eq_norm] using hf.dist_le_mul (y-t) (x-t)
  have H := hasFDerivAt_integral_of_dominated_loc_of_lip'
    (μ := μ) (s := univ) (F := fun y t => g t * f (y-t))
    (F' := fun t => g t • fderiv ℝ f (x-t)) (bound := fun t => ‖g t‖ * K)
    (x₀ := x) univ_mem (fun y _ => (hFI y).aestronglyMeasurable) (hFI x)
    hDm hbound (hgI.norm.mul_const K) hdif
  simpa +unfoldPartialApp [convolution, lsmul_apply, smul_eq_mul] using H.2

lemma locallyIntegrable_fderiv_lipschitz {f : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) : LocallyIntegrable (fderiv ℝ f) μ := by
  apply (locallyIntegrable_const (μ := μ) (K : ℝ)).mono
    (measurable_fderiv ℝ f).aestronglyMeasurable
  filter_upwards with x
  simpa using norm_fderiv_le_of_lipschitz ℝ hf (x₀ := x)

lemma fderiv_bump_convolution {f : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (φ : ContDiffBump (0 : E)) (x : E) :
    fderiv ℝ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x =
      ((φ.normed μ ⋆[lsmul ℝ ℝ, μ] fderiv ℝ f) x) :=
  (hasFDerivAt_convolution_lipschitz μ hf (φ.contDiff_normed (n := 1)).continuous
    φ.hasCompactSupport_normed x).fderiv

lemma ae_fderiv_bump_convolution_tendsto {f : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0 : E)} {C : ℝ}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (hφ' : ∀ᶠ i in l, (φ i).rOut ≤ C * (φ i).rIn) :
    ∀ᵐ x ∂μ, Tendsto (fun i => fderiv ℝ ((φ i).normed μ ⋆[lsmul ℝ ℝ, μ] f) x)
      l (𝓝 (fderiv ℝ f x)) := by
  simp_rw [fderiv_bump_convolution μ hf]
  exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hφ hφ'
    (locallyIntegrable_fderiv_lipschitz μ hf)

lemma norm_fderiv_bump_convolution_le {f : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (φ : ContDiffBump (0 : E)) (x : E) :
    ‖fderiv ℝ (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) x‖ ≤ K := by
  rw [fderiv_bump_convolution μ hf, convolution_def]
  have hI := ((φ.contDiff_normed (μ := μ) (n := 1)).continuous.integrable_of_hasCompactSupport
    (μ := μ) φ.hasCompactSupport_normed).mul_const (K : ℝ)
  have H := norm_integral_le_of_norm_le hI (Eventually.of_forall (fun t => show
      ‖lsmul ℝ ℝ (φ.normed μ t) (fderiv ℝ f (x-t))‖ ≤ φ.normed μ t * K from by
    rw [lsmul_apply, norm_smul, Real.norm_of_nonneg (φ.nonneg_normed t)]
    exact mul_le_mul_of_nonneg_left (norm_fderiv_le_of_lipschitz ℝ hf) (φ.nonneg_normed t)))
  simpa only [integral_mul_const, φ.integral_normed, one_mul] using H

lemma lipschitzWith_bump_convolution {f : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (φ : ContDiffBump (0 : E)) :
    LipschitzWith K (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) := by
  apply lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · exact fun x => (hasFDerivAt_convolution_lipschitz μ hf
      (φ.contDiff_normed (n := 1)).continuous φ.hasCompactSupport_normed x).differentiableAt
  · intro x
    exact_mod_cast norm_fderiv_bump_convolution_le μ hf φ x

lemma contDiff_bump_convolution {f : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (φ : ContDiffBump (0 : E)) (n : ℕ∞) :
    ContDiff ℝ n (φ.normed μ ⋆[lsmul ℝ ℝ, μ] f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ)
    φ.contDiff_normed hf.continuous.locallyIntegrable

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma shrinkingBump_tendsto : Tendsto (fun j : ℕ => (shrinkingBump (E := E) j).rOut)
    atTop (𝓝 0) := by
  simpa [shrinkingBump, div_eq_mul_inv] using
    (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ))

lemma exists_smooth_lipschitz_approximation {f : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) : ∃ f' : ℕ → E → ℝ,
      (∀ j, ContDiff ℝ (⊤ : ℕ∞) (f' j) ∧ LipschitzWith K (f' j)) ∧
      (∀ x, Tendsto (fun j => f' j x) atTop (𝓝 (f x))) ∧
      (∀ᵐ x ∂μ, Tendsto (fun j => fderiv ℝ (f' j) x) atTop (𝓝 (fderiv ℝ f x))) := by
  refine ⟨fun j => (shrinkingBump j).normed μ ⋆[lsmul ℝ ℝ, μ] f, ?_, ?_, ?_⟩
  · intro j
    exact ⟨contDiff_bump_convolution μ hf _ ⊤, lipschitzWith_bump_convolution μ hf _⟩
  · exact ContDiffBump.convolution_tendsto_right_of_continuous shrinkingBump_tendsto hf.continuous
  · apply ae_fderiv_bump_convolution_tendsto μ hf shrinkingBump_tendsto (C := 2)
    filter_upwards with j
    dsimp [shrinkingBump]
    ring_nf
    rfl

end CAT0Fillings

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Calculus_LipschitzFTC
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.Foundations.testClass_nonempty _root_.OAI.CAT0Fillings.Foundations.unitTestClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

lemma LipschitzWith.integral_deriv_eq_sub {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (a b : ℝ) :
    ∫ t in a..b, deriv f t = f b - f a := by
  obtain ⟨g,hg,hpt,hderiv⟩ := exists_smooth_lipschitz_approximation volume hf
  have hbound (j : ℕ) (t : ℝ) : ‖deriv (g j) t‖ ≤ K :=
    norm_deriv_le_of_lipschitz (hg j).2
  have hlim : ∀ᵐ t ∂volume,
      Tendsto (fun j => deriv (g j) t) atTop (𝓝 (deriv f t)) := by
    filter_upwards [hderiv] with t ht
    have H := ((ContinuousLinearMap.apply ℝ ℝ (1:ℝ)).continuous.tendsto
      (fderiv ℝ f t)).comp ht
    exact H
  have hi (j : ℕ) : IntervalIntegrable (deriv (g j)) volume a b :=
    ((hg j).1.continuous_deriv (by norm_num)).intervalIntegrable a b
  have hlimI : Tendsto (fun j => ∫ t in a..b, deriv (g j) t) atTop
      (𝓝 (∫ t in a..b, deriv f t)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (bound := fun _ => (K:ℝ))
    · exact Filter.Eventually.of_forall (fun j => ((hg j).1.continuous_deriv (by norm_num)).aestronglyMeasurable)
    · exact Filter.Eventually.of_forall (fun j => Filter.Eventually.of_forall (fun t _ => hbound j t))
    · exact intervalIntegrable_const
    · exact hlim.mono (fun _ ht _ => ht)
  have heq (j : ℕ) : ∫ t in a..b, deriv (g j) t = g j b - g j a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => ((hg j).1.differentiable (by norm_num) t).hasDerivAt) (hi j)
  simp only [heq] at hlimI
  exact tendsto_nhds_unique hlimI ((hpt b).sub (hpt a))

end CAT0Fillings

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma lipschitz_slice {f : ℝ × X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (t : ℝ) :
    LipschitzWith K (fun x => f (t,x)) := by
  simpa [Function.comp_def] using hf.comp ((LipschitzWith.const t).prodMk
    (LipschitzWith.id : LipschitzWith 1 (id : X → X)))

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma lipschitz_time {f : ℝ × X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (x : X) :
    LipschitzWith K (fun t => f (t,x)) := by
  simpa [Function.comp_def] using hf.comp ((LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).prodMk
    (LipschitzWith.const x))

omit [MeasurableSpace X] [BorelSpace X] in
lemma boundedLip_of_lipschitz_compact {f : X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    BoundedLip f := by
  refine ⟨⟨K,hf⟩,?_⟩
  obtain ⟨b,hb⟩ := (isCompact_range hf.continuous.abs).bddAbove
  exact ⟨b,fun x => hb (mem_range_self x)⟩

omit [CompactSpace X] in
lemma measurable_timeDeriv {f : ℝ × X → ℝ} (hf : Continuous f) :
    Measurable (fun p : ℝ × X => deriv (fun t => f (t,p.2)) p.1) := by
  exact (measurable_deriv_with_param (f := fun x t => f (t,x))
    (hf.comp continuous_swap)).comp measurable_swap

omit [CompactSpace X] in
lemma integrable_timeDeriv {f : ℝ × X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (μ : Measure X) [IsFiniteMeasure μ] (t : ℝ) :
    Integrable (fun x => deriv (fun s => f (s,x)) t) μ := by
  apply (integrable_const (K:ℝ)).mono'
    ((measurable_timeDeriv hf.continuous).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  filter_upwards with x
  exact norm_deriv_le_of_lipschitz (lipschitz_time hf x)

lemma ae_time_hasDeriv {f : ℝ × X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (μ : Measure X) [IsFiniteMeasure μ] :
    ∀ᵐ t ∂volume, ∀ᵐ x ∂μ, HasDerivAt (fun s => f (s,x))
      (deriv (fun s => f (s,x)) t) t := by
  have hmeas := measurableSet_of_differentiableAt_with_param ℝ
    (f := fun x t => f (t,x)) (hf.continuous.comp continuous_swap)
  have hp : ∀ᵐ p ∂μ.prod volume, DifferentiableAt ℝ (fun t => f (t,p.1)) p.2 := by
    apply (ae_prod_iff_ae_ae hmeas).mpr
    filter_upwards with x
    exact (lipschitz_time hf x).ae_differentiableAt
  have hq := (Measure.measurePreserving_swap (μ := volume) (ν := μ)).quasiMeasurePreserving.ae hp
  filter_upwards [ae_ae_of_ae_prod hq] with t ht
  filter_upwards [ht] with x hx
  exact hx.hasDerivAt

end CAT0Fillings
end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Geometry_Determinant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings

theorem abs_det_le_sqrt_det_of_posSemidef {n : ℕ} (L P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosSemidef)
    (h : ∀ i v, |L i ⬝ᵥ v| ≤ Real.sqrt (v ⬝ᵥ P.mulVec v)) :
    |L.det| ≤ Real.sqrt P.det := by
  by_cases hzero : P.det = 0
  · obtain ⟨v,hv,hPv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hzero
    have hLv : L.mulVec v = 0 := by
      ext i
      have hh := h i v
      rw [hPv, dotProduct_zero,Real.sqrt_zero] at hh
      exact abs_nonpos_iff.mp hh
    have hL := Matrix.exists_mulVec_eq_zero_iff.1 ⟨v,hv,hLv⟩
    rw [hL,hzero,abs_zero,Real.sqrt_zero]
  · apply abs_det_le_sqrt_det_of_posDef L P _ h
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hP.isHermitian
    intro v hv
    refine lt_of_le_of_ne (hP.dotProduct_mulVec_nonneg v) ?_
    intro heq
    have hz := (hP.dotProduct_mulVec_zero_iff _).1 heq.symm
    exact hv (Matrix.eq_zero_of_mulVec_eq_zero hzero hz)

end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_ProductRule
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal

namespace CAT0Fillings
open MeasureTheory Set Filter
open scoped Topology NNReal

namespace Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]

lemma IntegerRectifiable.cycle_product_rule {k : ℕ} {T : Functional X (k + 1)}
    (hT : IntegerRectifiable T) (hz : IsCycle T) {b f : X → ℝ} (hb : BoundedLip b)
    (hf : BoundedLip f) (π : Fin k → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    T b (Matrix.vecCons f π) = -T f (Matrix.vecCons b π) := by
  have h := IntegerRectifiable.product_rule hT hb hf π hπ
  have hz' : boundarySucc T = fun _ _ => 0 := hz
  rw [hz'] at h
  exact eq_neg_of_add_eq_zero_left h

end Foundations
end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Slicing_EuclideanSplit
attribute [-simp] _root_.OAI.CAT0Fillings.Prism.tail_apply _root_.OAI.CAT0Fillings.Prism.tail_single_succ _root_.OAI.CAT0Fillings.Prism.tail_single_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.Prism

lemma split_single_zero (k : ℕ) : split k (EuclideanSpace.single 0 1) = (1,0) := by
  ext <;> simp

end CAT0Fillings.Prism

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_DomainRestriction
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open MeasureTheory Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {k : ℕ} (C : IntegerChart X k)

variable [CompactSpace X] [Nonempty X]

lemma restrictDomain_isMetricCurrent {t : Set (Euc k)} (ht : MeasurableSet t)
    (hts : t ⊆ C.domain) (hC : IsMetricCurrent C.action) :
    IsMetricCurrent (C.restrictDomain ht hts).action := by
  rw [C.restrictDomain_action ht hts hC]
  exact BorelRestriction.restrictCurrent_isMetricCurrent hC
    (C.measurableSet_paramExtended_image ht hts)

end IntegerChart
end CAT0Fillings
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_Pushforward
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Foundations.testClass_nonempty _root_.OAI.CAT0Fillings.Foundations.unitTestClass_nonempty _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

universe u
namespace CurrentOperations
attribute [local instance] Classical.propDecidable
variable {X : Type u} {Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
lemma boundedLip_comp {b : Y → ℝ} (hb : BoundedLip b) {f : X → Y}
    {K : ℝ≥0} (hf : LipschitzWith K f) : BoundedLip (b ∘ f) := by
  obtain ⟨⟨L, hL⟩, M, hM⟩ := hb
  exact ⟨⟨L*K, hL.comp hf⟩, M, fun x => hM (f x)⟩

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
lemma admissible_comp {k : ℕ} {b : Y → ℝ} {π : Fin k → Y → ℝ}
    (h : Admissible b π) {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) :
    Admissible (b ∘ f) (fun i => π i ∘ f) := by
  refine ⟨boundedLip_comp h.1 hf, fun i => ?_⟩
  obtain ⟨L, hL⟩ := h.2 i
  exact ⟨L*K, hL.comp hf⟩

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
lemma pushCurrent_apply {k : ℕ} (f : X → Y) (T : Functional X k)
    {b : Y → ℝ} {π : Fin k → Y → ℝ} (h : Admissible b π) :
    pushCurrent f T b π = T (b ∘ f) (fun i => π i ∘ f) := ite_eq_left h

lemma pushCurrent_controls {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T)
    {μ : Measure X} (hμ : Controls T μ) {f : X → Y} {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    Controls (pushCurrent f T) ((↑(K^k) : ℝ≥0∞) • μ.map f) := by
  intro b π hb hπ
  rw [pushCurrent_apply f T ⟨hb, fun i => ⟨1, hπ i⟩⟩,
    integral_smul_measure, integral_map hf.continuous.aemeasurable
      hb.continuous.abs.aestronglyMeasurable]
  have h := hT.mass_bound hμ (boundedLip_comp hb hf) (fun _ => K)
    (fun i => by simpa only [one_mul] using (hπ i).comp hf)
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.coe_toReal, NNReal.coe_pow, smul_eq_mul, Function.comp_apply] using h

lemma pushCurrent_isMetricCurrent {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) :
    IsMetricCurrent (pushCurrent f T) where
  offDomain := by intro b π h; exact ite_eq_right h
  linearFirst := by
    intro b c π a d hb hc hπ
    rw [pushCurrent_apply f T ⟨(hb.const_mul a).add (hc.const_mul d), hπ⟩,
      pushCurrent_apply f T ⟨hb, hπ⟩, pushCurrent_apply f T ⟨hc, hπ⟩]
    exact hT.linearFirst (b ∘ f) (c ∘ f) (fun i => π i ∘ f) a d
      (boundedLip_comp hb hf) (boundedLip_comp hc hf) (admissible_comp ⟨hb, hπ⟩ hf).2
  linearCoord := by
    intro b π i g a c h hg
    have hπg : ∀ j, ∃ L : ℝ≥0, LipschitzWith L ((Function.update π i g) j) := by
      intro j
      by_cases hj : j = i
      · simpa only [hj, Function.update_self] using hg
      · simpa only [Function.update_of_ne hj] using h.2 j
    have hl : ∃ L : ℝ≥0, LipschitzWith L (fun y => a * π i y + c * g y) := by
      obtain ⟨L, hL⟩ := h.2 i
      obtain ⟨M, hM⟩ := hg
      exact ⟨_, (lipschitz_mul_real hL a).add (lipschitz_mul_real hM c)⟩
    have hπac : ∀ j, ∃ L : ℝ≥0,
        LipschitzWith L ((Function.update π i (fun y => a * π i y + c * g y)) j) := by
      intro j
      by_cases hj : j = i
      · simpa only [hj, Function.update_self] using hl
      · simpa only [Function.update_of_ne hj] using h.2 j
    rw [pushCurrent_apply f T ⟨h.1, hπac⟩, pushCurrent_apply f T h,
      pushCurrent_apply f T ⟨h.1, hπg⟩]
    have h₁ : (fun j => (Function.update π i (fun y => a * π i y + c * g y)) j ∘ f) =
        Function.update (fun j => π j ∘ f) i (fun x => a * π i (f x) + c * g (f x)) := by
      funext j x
      by_cases hji : j = i <;> simp [hji, Function.update_of_ne]
    have h₂ : (fun j => (Function.update π i g) j ∘ f) =
        Function.update (fun j => π j ∘ f) i (g ∘ f) := by
      funext j x
      by_cases hji : j = i <;> simp [hji, Function.update_of_ne]
    rw [h₁, h₂]
    obtain ⟨L, hL⟩ := hg
    exact hT.linearCoord _ _ i _ a c (admissible_comp h hf) ⟨L*K, hL.comp hf⟩
  sequentialContinuity := by
    intro b π πs hb hLip hpt
    choose L hL using hLip
    have hπ (i) : LipschitzWith (L i) (π i) := by
      apply lipschitzWith_iff_dist_le_mul.mpr
      intro x y
      exact le_of_tendsto ((hpt i x).dist (hpt i y))
        (Eventually.of_forall fun j => (hL i j).dist_le_mul x y)
    simp only [pushCurrent_apply f T ⟨hb, fun i => ⟨L i, hL i _⟩⟩,
      pushCurrent_apply f T ⟨hb, fun i => ⟨L i, hπ i⟩⟩]
    exact hT.sequentialContinuity _ _ _ (boundedLip_comp hb hf)
      (fun i => ⟨L i*K, fun j => (hL i j).comp hf⟩) (fun i x => hpt i (f x))
  locality := by
    intro b π h hloc
    rw [pushCurrent_apply f T h]
    obtain ⟨i, U, c, hU, hbU, hc⟩ := hloc
    apply hT.locality _ _ (admissible_comp h hf)
    refine ⟨i, f ⁻¹' U, c, hU.preimage hf.continuous, ?_, ?_⟩
    · intro x hx; exact hbU hx
    · intro x hx; exact hc (f x) hx
  finiteMass := by
    obtain ⟨μ, hμ, hctrl⟩ := hT.finiteMass
    let := hμ
    refine ⟨(↑(K^k) : ℝ≥0∞) • μ.map f, ⟨?_⟩, pushCurrent_controls hT hctrl hf⟩
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top (μ.map f) univ)

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
lemma pushCurrent_comp {Z : Type*} [MetricSpace Z] {k : ℕ} {T : Functional X k}
    {f : X → Y} {g : Y → Z} {L : ℝ≥0} (hg : LipschitzWith L g) :
    pushCurrent (g ∘ f) T = pushCurrent g (pushCurrent f T) := by
  funext b π
  by_cases h : Admissible b π
  · rw [pushCurrent_apply (g ∘ f) T h, pushCurrent_apply g (pushCurrent f T) h,
      pushCurrent_apply f T (admissible_comp h hg)]
    rfl
  · simp only [pushCurrent, ite_eq_right h]

end CurrentOperations
end CAT0Fillings
end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_Postcompose
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory
open CurrentOperations

namespace IntegerChart
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {k : ℕ}
  (C : IntegerChart X k) {f : X → Y} {K J : ℝ≥0}

lemma postcompose_scalar (hf : LipschitzWith K f)
    (hJ : AntilipschitzWith J (f ∘ C.param)) (b : Y → ℝ) :
    (C.postcompose hf hJ).scalar b = C.scalar (b ∘ f) := by
  classical
  funext x
  change (if h : x ∈ C.domain then b (f (C.param ⟨x,h⟩)) else 0) = _
  rfl

lemma postcompose_jacobian (hf : LipschitzWith K f)
    (hJ : AntilipschitzWith J (f ∘ C.param)) (π : Fin k → Y → ℝ) :
    (C.postcompose hf hJ).jacobian π = C.jacobian (fun i => π i ∘ f) := by
  rfl

lemma postcompose_action (hf : LipschitzWith K f)
    (hJ : AntilipschitzWith J (f ∘ C.param)) :
    (C.postcompose hf hJ).action = pushCurrent f C.action := by
  classical
  funext b π
  by_cases h : Admissible b π
  · rw [pushCurrent_apply f C.action h,action,ite_eq_left h,
      action,ite_eq_left (admissible_comp h hf)]
    change (∫ x in C.domain, (C.multiplicity x : ℝ)*
      (C.postcompose hf hJ).scalar b x*(C.postcompose hf hJ).jacobian π x) = _
    rw [C.postcompose_scalar hf hJ,C.postcompose_jacobian hf hJ]
  · simp only [action,pushCurrent,ite_eq_right h]

lemma postcompose_image (hf : LipschitzWith K f)
    (hJ : AntilipschitzWith J (f ∘ C.param)) :
    (C.postcompose hf hJ).image = f '' C.image := by
  exact range_comp f C.param

end IntegerChart

end CAT0Fillings
end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_SumControls
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

section SumControls
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {k : ℕ} {T : Functional X k} {S : ℕ → Functional X k}
  {μ : ℕ → Measure X} [IsFiniteMeasure (Measure.sum μ)]

omit [CompactSpace X] in
lemma controls_sum_general (hμ : ∀ i, Controls (S i) (μ i))
    (hT : ∀ b π, T b π = ∑' i, S i b π) : Controls T (Measure.sum μ) := by
  intro b π hb hπ
  have hbi : Integrable (fun x => |b x|) (Measure.sum μ) :=
    (hb.toBoundedContinuous.integrable (Measure.sum μ)).abs
  have hs : Summable (fun i => ∫ x, |b x| ∂μ i) := by
    simpa only [Real.norm_eq_abs,abs_abs] using hbi.summable_integral
  have hsa : Summable (fun i => S i b π) :=
    hs.of_norm_bounded (fun i => by simpa only [Real.norm_eq_abs] using hμ i b π hb hπ)
  rw [hT b π,integral_sum_measure hbi]
  calc
    |∑' i, S i b π| ≤ ∑' i, |S i b π| := by
      simpa only [Real.norm_eq_abs] using
        (norm_tsum_le_tsum_norm (f := fun i => S i b π) hsa.norm)
    _ ≤ ∑' i, ∫ x, |b x| ∂μ i := hsa.abs.tsum_le_tsum (fun i => hμ i b π hb hπ) hs

end SumControls

end CAT0Fillings

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_ControlledSum
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {k : ℕ}
lemma IsMetricCurrent.control_bound_uniform {T : Functional X k} (hT : IsMetricCurrent T)
    {μ : Measure X} [IsFiniteMeasure μ] (hμ : Controls T μ)
    {b : X → ℝ} (hb : BoundedLip b) {π : Fin k → X → ℝ}
    (K : Fin k → ℝ≥0) (hK : ∀ i, LipschitzWith (K i) (π i))
    {M : ℝ} (hM : ∀ x, |b x| ≤ M) :
    |T b π| ≤ ((∏ i, (K i : ℝ))*M)*μ.real univ := by
  have hi : Integrable (fun x => |b x|) μ := (hb.toBoundedContinuous.integrable μ).abs
  have hbound : (∫ x, |b x| ∂μ) ≤ μ.real univ * M := by
    simpa using integral_mono hi (integrable_const M) hM
  calc
    _ ≤ (∏ i, (K i : ℝ)) * ∫ x, |b x| ∂μ := hT.mass_bound hμ hb K hK
    _ ≤ (∏ i, (K i : ℝ)) * (μ.real univ*M) :=
      mul_le_mul_of_nonneg_left hbound (Finset.prod_nonneg fun i _ => (K i).coe_nonneg)
    _ = _ := by ring

lemma summable_controlled_actions {T : ℕ → Functional X k}
    (hT : ∀ i, IsMetricCurrent (T i)) {μ : ℕ → Measure X}
    [∀ i, IsFiniteMeasure (μ i)] (hμ : ∀ i, Controls (T i) (μ i))
    (hS : Summable (fun i => (μ i).real univ))
    (b : X → ℝ) (π : Fin k → X → ℝ) : Summable (fun i => T i b π) := by
  by_cases h : Admissible b π
  · choose K hK using h.2
    obtain ⟨M,hM⟩ := h.1.2
    exact (hS.mul_left ((∏ j, (K j : ℝ))*M)).of_norm_bounded
      (fun i => by simpa only [Real.norm_eq_abs] using
        (hT i).control_bound_uniform (hμ i) h.1 K hK hM)
  · simp only [fun i => (hT i).offDomain b π h,summable_zero]

lemma isMetricCurrent_tsum_controlled {T : ℕ → Functional X k}
    (hT : ∀ i, IsMetricCurrent (T i)) {μ : ℕ → Measure X}
    [∀ i, IsFiniteMeasure (μ i)] (hμ : ∀ i, Controls (T i) (μ i))
    (hS : Summable (fun i => (μ i).real univ)) :
    IsMetricCurrent (fun b π => ∑' i, T i b π) := by
  have hs := summable_controlled_actions hT hμ hS
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro b π hab
    simp only [fun i => (hT i).offDomain b π hab,tsum_zero]
  · intro b c π a d hb hc hπ
    simp only [fun i => (hT i).linearFirst b c π a d hb hc hπ]
    rw [((hs b π).mul_left a).tsum_add ((hs c π).mul_left d)]
    simp only [tsum_mul_left]
  · intro b π j f a c hab hf
    simp only [fun i => (hT i).linearCoord b π j f a c hab hf]
    rw [((hs b π).mul_left a).tsum_add ((hs b (Function.update π j f)).mul_left c)]
    simp only [tsum_mul_left]
  · intro b π πs hb hπs hlim
    choose K hK using hπs
    obtain ⟨M,hM⟩ := hb.2
    apply tendsto_tsum_of_dominated_convergence
      (hS.mul_left ((∏ j, (K j : ℝ))*M))
      (fun i => (hT i).sequentialContinuity b π πs hb (fun j => ⟨K j,hK j⟩) hlim)
    exact Eventually.of_forall (fun j i =>
      (hT i).control_bound_uniform (hμ i) hb K (fun l => hK l j) hM)
  · intro b π hab hloc
    simp only [fun i => (hT i).locality b π hab hloc,tsum_zero]
  · let := finite_sum_measure_of_summable_total μ hS
    exact ⟨Measure.sum μ,inferInstance,controls_sum_general hμ (fun _ _ => rfl)⟩

end CAT0Fillings

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_CycleCalculus
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter Matrix
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
local notation "BL" => boundedLipSubmodule (X := X)
lemma Foundations.IntegerRectifiable.cycle_update {k : ℕ} {T : Functional X (k+1)}
    (hT : IntegerRectifiable T) (hz : IsCycle T) {b f : X → ℝ}
    (hb : BoundedLip b) (hf : BoundedLip f) (π : Fin (k+1) → X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) (j : Fin (k+1)) :
    T b (Function.update π j f) =
      (-1:ℝ)^(j.val+1) * T f (Fin.cons b (j.removeNth π)) := by
  have hp := Foundations.IntegerRectifiable.apply_permute hT
    (Foundations.admissible_vecCons hb hf.1 (fun i => hπ (j.succAbove i))) j.cycleRange
  change T b (Fin.cons f (j.removeNth π) ∘ j.cycleRange) = _ at hp
  rw [Fin.cons_comp_cycleRange,Fin.insertNth_removeNth,Fin.sign_cycleRange] at hp
  rw [hp,Foundations.IntegerRectifiable.cycle_product_rule hT hz hb hf _ (fun i => hπ (j.succAbove i))]
  change ((((-1:ℤˣ)^j.val : ℤˣ) : ℤ) : ℝ) *
    (-T f (Fin.cons b (j.removeNth π))) = _
  simp [pow_succ]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma fin_removeNth_succ {α : Type*} {k : ℕ} (v : Fin (k+2) → α) (j : Fin (k+1)) :
    j.succ.removeNth v = Fin.cons (v 0) (j.removeNth (fun i => v i.succ)) := by
  funext i
  refine Fin.cases ?_ (fun l => ?_) i
  · simp [Fin.removeNth_apply]
  · simp [Fin.removeNth_apply]

lemma IsMetricCurrent.fullMultilinear_cycle_update {k : ℕ} {T : Functional X (k+1)}
    (hcur : IsMetricCurrent T) (hT : IntegerRectifiable T) (hz : IsCycle T)
    (v : Fin (k+2) → BL) (i : Fin (k+2)) (g : BL) :
    hcur.fullMultilinear (Function.update v i g) =
      (-1:ℝ)^i.val * T g (fun j => (i.removeNth v j : X → ℝ)) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [IsMetricCurrent.fullMultilinear,MultilinearMap.mk'_apply,
      Function.update_self,bl_update_tail_zero,Fin.removeNth_zero]
    simp only [Fin.val_zero,pow_zero,one_mul]
    rfl
  · change T ((Function.update v j.succ g) 0)
      (fun l => ((Function.update v j.succ g) l.succ : X → ℝ)) = _
    rw [Function.update_of_ne (Fin.succ_ne_zero j).symm,bl_update_tail_succ]
    rw [Foundations.IntegerRectifiable.cycle_update hT hz (v 0).property g.property _
      (fun l => (v l.succ).property.1),fin_removeNth_succ]
    congr 2
    funext l
    refine Fin.cases ?_ (fun m => ?_) l <;> rfl

end CAT0Fillings

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_CycleDifference
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter Matrix
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
local notation "BL" => boundedLipSubmodule (X := X)

lemma MultilinearMap.sub_eq_sum_update {ι : Type*} [Fintype ι] [LinearOrder ι]
    {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    (M : MultilinearMap ℝ E ℝ) (a b : ∀ i, E i) :
    M a - M b = ∑ i, M (Function.update (mixedTuple a b i) i (a i-b i)) := by
  have h := M.map_sub_map_piecewise a b Finset.univ
  simp only [Finset.piecewise_univ,Finset.mem_univ,true_implies] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext j
  by_cases hji : j=i
  · subst j
    simp
  · by_cases hj : j < i <;> simp [mixedTuple,hj,hji,Ne.symm hji]

lemma IsMetricCurrent.cycle_difference {k : ℕ} {T : Functional X (k+1)}
    (hcur : IsMetricCurrent T) (hT : IntegerRectifiable T) (hz : IsCycle T)
    (a b : Fin (k+2) → BL) :
    hcur.fullMultilinear a - hcur.fullMultilinear b =
      ∑ i, (-1:ℝ)^i.val * T (a i-b i)
        (fun j => ((i.removeNth (mixedTuple a b i)) j : X → ℝ)) := by
  rw [MultilinearMap.sub_eq_sum_update]
  apply Finset.sum_congr rfl
  intro i _
  exact hcur.fullMultilinear_cycle_update hT hz _ _ _

lemma IsMetricCurrent.cycle_difference_bound {k : ℕ} {T : Functional X (k+1)}
    (hcur : IsMetricCurrent T) (hT : IntegerRectifiable T) (hz : IsCycle T)
    (a b : Fin (k+2) → BL) (K : ℝ≥0)
    (ha : ∀ i, LipschitzWith K (a i : X → ℝ))
    (hb : ∀ i, LipschitzWith K (b i : X → ℝ))
    (D : ℝ) (hd : ∀ i x, |(a i : X → ℝ) x - (b i : X → ℝ) x| ≤ D) :
    |hcur.fullMultilinear a - hcur.fullMultilinear b| ≤
      ((k+2:ℕ):ℝ) * (K:ℝ)^(k+1) * mass T * D := by
  rw [hcur.cycle_difference hT hz]
  calc
    |∑ i, (-1:ℝ)^i.val * T (a i-b i)
        (fun j => ((i.removeNth (mixedTuple a b i)) j : X → ℝ))| ≤
      ∑ i : Fin (k+2), (K:ℝ)^(k+1) * mass T * D := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
        have H := hcur.mass_bound_uniform (a i-b i).property (fun _ => K)
          (fun j => show LipschitzWith K
            ((i.removeNth (mixedTuple a b i)) j : X → ℝ) from by
              dsimp [Fin.removeNth,mixedTuple]
              split_ifs <;> first | exact ha _ | exact hb _)
          (hd i)
        simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_assoc,
          Submodule.coe_sub,Pi.sub_apply,mul_comm D] using H
    _ = _ := by simp [mul_assoc]

end CAT0Fillings

namespace CAT0Fillings
open Set MeasureTheory Filter Matrix
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
local notation "BL" => boundedLipSubmodule (X := X)

lemma IsMetricCurrent.cycle_time_lipschitz {k : ℕ} {T : Functional X (k+1)}
    (hcur : IsMetricCurrent T) (hT : IntegerRectifiable T) (hz : IsCycle T)
    (V : ℝ → Fin (k+2) → BL) (K : ℝ≥0)
    (hx : ∀ t i, LipschitzWith K (V t i : X → ℝ))
    (ht : ∀ i x, LipschitzWith K (fun t => (V t i : X → ℝ) x)) :
    LipschitzWith (⟨((k+2:ℕ):ℝ) * (K:ℝ)^(k+1) * mass T * (K:ℝ),by
      exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (mass_nonneg T)) K.coe_nonneg⟩ : ℝ≥0) (fun t => hcur.fullMultilinear (V t)) := by
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro t s
  have H := hcur.cycle_difference_bound hT hz (V t) (V s) K (hx t) (hx s)
    ((K:ℝ)*dist t s) (fun i x => by simpa only [Real.dist_eq] using (ht i x).dist_le_mul t s)
  change |hcur.fullMultilinear (V t) - hcur.fullMultilinear (V s)| ≤
    ((((k+2:ℕ):ℝ) * (K:ℝ)^(k+1) * mass T) * (K:ℝ)) * dist t s
  simpa only [mul_assoc] using H

end CAT0Fillings
end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_MovingAction
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.BorelCoefficients
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ]
variable {k : ℕ} {T : Functional X k}
lemma borelAction_filterContinuity (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {b : X → ℝ} (hb : Integrable b μ) (π : Fin k → X → ℝ)
    (πs : ι → Fin k → X → ℝ)
    (hLip : ∀ i, ∃ K : ℝ≥0, ∀ j, LipschitzWith K (πs j i))
    (hpt : ∀ i x, Tendsto (fun j => πs j i x) l (𝓝 (π i x))) :
    Tendsto (fun j => borelAction μ hT b (πs j)) l (𝓝 (borelAction μ hT b π)) := by
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro u hu
  exact borelAction_sequentialContinuity μ hT hμ hb π (fun j => πs (u j))
    (fun i => ⟨(hLip i).choose,fun j => (hLip i).choose_spec (u j)⟩)
    (fun i x => (hpt i x).comp hu)

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] [IsFiniteMeasure μ] in
lemma tendsto_toL1_dominated {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {fs : ι → X → ℝ} {f G : X → ℝ} (hfs : ∀ j, Integrable (fs j) μ)
    (hf : Integrable f μ) (hG : Integrable G μ)
    (hb : ∀ j, ∀ᵐ x ∂μ, ‖fs j x‖ ≤ G x)
    (hp : ∀ᵐ x ∂μ, Tendsto (fun j => fs j x) l (𝓝 (f x))) :
    Tendsto (fun j => (hfs j).toL1 (fs j)) l (𝓝 (hf.toL1 f)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have heq (j) : ‖(hfs j).toL1 (fs j) - hf.toL1 f‖ = ∫ x, ‖fs j x - f x‖ ∂μ := by
    rw [← Integrable.toL1_sub, L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [((hfs j).sub hf).coeFn_toL1] with x hx
    exact congrArg norm hx
  simp only [heq]
  have H := tendsto_integral_filter_of_dominated_convergence (fun x => G x + ‖f x‖)
    (Filter.Eventually.of_forall (fun j => ((hfs j).sub hf).norm.aestronglyMeasurable))
    (Filter.Eventually.of_forall (fun j => (hb j).mono fun x hx =>
      by simpa only [Pi.sub_apply,norm_norm] using
        (norm_sub_le (fs j x) (f x)).trans (add_le_add_left hx _))) (hG.add hf.norm)
    (hp.mono fun x hx => by simpa using (hx.sub_const (f x)).norm)
  simpa using H

lemma borelAction_moving (hT : IsMetricCurrent T) (hμ : Controls T μ)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] [NeBot l]
    {bs : ι → X → ℝ} {b : X → ℝ} (hbs : ∀ j, Integrable (bs j) μ)
    (hb : Integrable b μ)
    (hbpt : Tendsto (fun j => (hbs j).toL1 (bs j)) l (𝓝 (hb.toL1 b)))
    (π : Fin k → X → ℝ) (πs : ι → Fin k → X → ℝ)
    (hLip : ∀ i, ∃ K : ℝ≥0, ∀ j, LipschitzWith K (πs j i))
    (hpt : ∀ i x, Tendsto (fun j => πs j i x) l (𝓝 (π i x))) :
    Tendsto (fun j => borelAction μ hT (bs j) (πs j)) l
      (𝓝 (borelAction μ hT b π)) := by
  choose K hK using hLip
  have hfixed := borelAction_filterContinuity μ hT hμ hb π πs
    (fun i => ⟨K i,hK i⟩) hpt
  have hdiff : Tendsto (fun j => borelAction μ hT (bs j) (πs j) -
      borelAction μ hT b (πs j)) l (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    refine squeeze_zero (g := fun j => (∏ i, (K i:ℝ)) *
      ‖(hbs j).toL1 (bs j) - hb.toL1 b‖) (fun _ => norm_nonneg _) (fun j => ?_) ?_
    · rw [borelAction_of_integrable μ hT (hbs j) _ (fun i => ⟨K i,hK i j⟩),
        borelAction_of_integrable μ hT hb _ (fun i => ⟨K i,hK i j⟩),← map_sub]
      exact l1Action_bound μ hT hμ (πs j) K (fun i => hK i j) _
    · simpa only [mul_zero] using
        ((tendsto_iff_norm_sub_tendsto_zero.mp hbpt).const_mul (∏ i, (K i:ℝ)))
  simpa only [zero_add,sub_add_cancel] using hdiff.add hfixed

end CAT0Fillings.BorelCoefficients

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_CycleDerivative
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter Matrix
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
local notation "BL" => boundedLipSubmodule (X := X)
omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma bounded_time_slope {d : ℕ} (V : ℝ → Fin d → BL) (K : ℝ≥0)
    (ht : ∀ i x, LipschitzWith K (fun t => (V t i : X → ℝ) x)) (t h : ℝ) (i : Fin d) (x : X) :
    |h⁻¹ * ((V (t+h) i : X → ℝ) x - (V t i : X → ℝ) x)| ≤ K := by
  by_cases hh : h=0
  · simp [hh]
  · have H := (ht i x).dist_le_mul (t+h) t
    rw [Real.dist_eq,Real.dist_eq,add_sub_cancel_left] at H
    rw [abs_mul,abs_inv]
    calc |h|⁻¹ * |(V (t+h) i : X → ℝ) x - (V t i : X → ℝ) x| ≤
      |h|⁻¹ * ((K:ℝ)*|h|) := mul_le_mul_of_nonneg_left H (by positivity)
      _ = K := by field_simp

lemma IsMetricCurrent.hasDeriv_cycle_path {k : ℕ} {T : Functional X (k+1)}
    (hcur : IsMetricCurrent T) (hT : IntegerRectifiable T) (hz : IsCycle T)
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : Controls T μ)
    (V : ℝ → Fin (k+2) → BL) (K : ℝ≥0)
    (hx : ∀ t i, LipschitzWith K (V t i : X → ℝ))
    (ht : ∀ i x, LipschitzWith K (fun t => (V t i : X → ℝ) x))
    (t : ℝ) (D : Fin (k+2) → X → ℝ) (hD : ∀ i, Integrable (D i) μ)
    (hder : ∀ i, ∀ᵐ x ∂μ, HasDerivAt (fun s => (V s i : X → ℝ) x) (D i x) t) :
    HasDerivAt (fun s => hcur.fullMultilinear (V s))
      (∑ i, (-1:ℝ)^i.val * BorelCoefficients.borelAction μ hcur (D i)
        (fun j => (i.removeNth (V t) j : X → ℝ))) t := by
  let B (h : ℝ) (i : Fin (k+2)) : BL := h⁻¹ • (V (t+h) i - V t i)
  let P (h : ℝ) (i : Fin (k+2)) : Fin (k+1) → X → ℝ :=
    fun j => (i.removeNth (mixedTuple (V (t+h)) (V t) i) j : X → ℝ)
  have hP (h i j) : LipschitzWith K (P h i j) := by
    dsimp [P,Fin.removeNth,mixedTuple]
    split_ifs <;> exact hx _ _
  have hPb (i j x) : Tendsto (fun h => P h i j x) (𝓝[≠] 0)
      (𝓝 ((i.removeNth (V t) j : X → ℝ) x)) := by
    dsimp [P,Fin.removeNth,mixedTuple]
    split_ifs
    · have H : Tendsto (fun h : ℝ => (V (t+h) (i.succAbove j) : X → ℝ) x) (𝓝 0)
          (𝓝 ((V t (i.succAbove j) : X → ℝ) x)) := by
        have HH : Tendsto (fun h : ℝ => t+h) (𝓝 0) (𝓝 t) := by
          simpa only [add_zero] using (tendsto_const_nhds.add tendsto_id :
            Tendsto (fun h : ℝ => t+h) (𝓝 0) (𝓝 (t+0)))
        exact (ht (i.succAbove j) x).continuous.continuousAt.tendsto.comp HH
      simpa only [add_zero] using H.mono_left nhdsWithin_le_nhds
    · exact tendsto_const_nhds
  have hbi (h i) : Integrable (B h i : X → ℝ) μ :=
    BorelCoefficients.integrable_boundedLip μ (B h i).property
  have hL1 (i) : Tendsto (fun h => (hbi h i).toL1 (B h i)) (𝓝[≠] 0)
      (𝓝 ((hD i).toL1 (D i))) := by
    apply BorelCoefficients.tendsto_toL1_dominated μ (fun h => hbi h i) (hD i)
      (G := fun _ => (K:ℝ)) (integrable_const (K:ℝ))
    · intro h
      filter_upwards with x
      exact bounded_time_slope V K ht t h i x
    · filter_upwards [hder i] with x hdx
      exact hdx.tendsto_slope_zero
  have hlim (i) : Tendsto (fun h => T (B h i) (P h i)) (𝓝[≠] 0)
      (𝓝 (BorelCoefficients.borelAction μ hcur (D i)
        (fun j => (i.removeNth (V t) j : X → ℝ)))) := by
    have H := BorelCoefficients.borelAction_moving μ hcur hμ (fun h => hbi h i) (hD i)
      (hL1 i) _ (fun h => P h i) (fun j => ⟨K,fun h => hP h i j⟩) (hPb i)
    have heq (h : ℝ) := BorelCoefficients.borelAction_eq μ hcur hμ
      (show Admissible (B h i : X → ℝ) (P h i) from
        ⟨(B h i).property,fun j => ⟨K,hP h i j⟩⟩)
    simp_rw [heq] at H
    exact H
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have H := tendsto_finsetSum Finset.univ (fun i _ => (hlim i).const_mul ((-1:ℝ)^i.val))
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  funext h
  simp only [smul_eq_mul,hcur.cycle_difference hT hz,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hc := hcur.linearFirst (V (t+h) i - V t i) (V (t+h) i - V t i)
    (P h i) h⁻¹ 0 (V (t+h) i - V t i).property (V (t+h) i - V t i).property
    (fun j => ⟨K,hP h i j⟩)
  simp only [zero_mul,add_zero] at hc
  change h⁻¹ * ((-1:ℝ)^i.val * T (V (t+h) i - V t i) (P h i)) =
    (-1:ℝ)^i.val * T (B h i) (P h i)
  rw [show T (B h i) (P h i) = h⁻¹ * T (V (t+h) i - V t i) (P h i) from hc]
  ring

end CAT0Fillings

open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Prism_Chart
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)

lemma prism_image : C.prism.image = Icc (0:ℝ) 1 ×ˢ C.image := by
  ext p
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨z.2.1,⟨⟨(Prism.split k z).2,z.2.2⟩,rfl⟩⟩
  · rintro ⟨ht,⟨z,hz⟩⟩
    let w : C.prismDomain := ⟨(Prism.split k).symm (p.1,z),by
      change Prism.split k ((Prism.split k).symm (p.1,z)) ∈ Icc (0:ℝ) 1 ×ˢ C.domain
      simpa only [ContinuousLinearEquiv.apply_symm_apply,mem_prod] using And.intro ht z.2⟩
    refine ⟨w,?_⟩
    change C.prismParam w = p
    simp only [prismParam,w,ContinuousLinearEquiv.apply_symm_apply]
    exact Prod.ext rfl hz

lemma prism_image_disjoint {D : IntegerChart X k} (h : Disjoint C.image D.image) :
    Disjoint C.prism.image D.prism.image := by
  rw [C.prism_image,D.prism_image]
  exact Set.disjoint_left.mpr fun _ hp hq => Set.disjoint_left.mp h hp.2 hq.2

end CAT0Fillings.IntegerChart

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Prism_Differential
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)
lemma prism_scalar_eq {f : ℝ × X → ℝ} {p : ℝ × Euc k}
    (hp : p ∈ Icc (0:ℝ) 1 ×ˢ C.domain) :
    C.prism.scalar f ((Prism.split k).symm p) = f (p.1,C.param ⟨p.2,hp.2⟩) := by
  have hz : (Prism.split k).symm p ∈ C.prism.domain := by
    simpa only [prism,prismDomain,mem_preimage,ContinuousLinearEquiv.apply_symm_apply] using hp
  rw [C.prism.scalar_eq hz]
  change f (C.prismParam _) = _
  simp only [prismParam,ContinuousLinearEquiv.apply_symm_apply]

lemma prism_scalar_extension {f : ℝ × X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∃ G : ℝ × Euc k → ℝ, (∃ L, LipschitzWith L G) ∧
      ∀ p (hp : p ∈ Icc (0:ℝ) 1 ×ˢ C.domain),
        G p = f (p.1,C.param ⟨p.2,hp.2⟩) := by
  obtain ⟨L,U,hC,hU⟩ := C.prism.bilipschitz
  obtain ⟨F,hF,heq⟩ := (C.prism.scalar_lipschitzOn hC hf).extend_real
  refine ⟨F ∘ (Prism.split k).symm,⟨_,hF.comp (Prism.split k).symm.lipschitz⟩,?_⟩
  intro p hp
  have hz : (Prism.split k).symm p ∈ C.prism.domain := by
    simpa only [prism,prismDomain,mem_preimage,ContinuousLinearEquiv.apply_symm_apply] using hp
  exact (heq hz).symm.trans (C.prism_scalar_eq hp)

lemma prism_fderiv_decompose {f : ℝ × X → ℝ} {G : ℝ × Euc k → ℝ}
    (heq : ∀ p (hp : p ∈ Icc (0:ℝ) 1 ×ˢ C.domain),
      G p = f (p.1,C.param ⟨p.2,hp.2⟩))
    {p : ℝ × Euc k} (ht : p.1 ∈ Ioo (0:ℝ) 1) (hz : p.2 ∈ C.domain)
    (hG : DifferentiableAt ℝ G p)
    (hu : UniqueDiffWithinAt ℝ C.domain p.2)
    (hup : UniqueDiffWithinAt ℝ C.prism.domain ((Prism.split k).symm p)) :
    (fderivWithin ℝ (C.prism.scalar f) C.prism.domain ((Prism.split k).symm p))
        (EuclideanSpace.single 0 1) = deriv (fun t => f (t,C.param ⟨p.2,hz⟩)) p.1 ∧
    (∀ j : Fin k,
      (fderivWithin ℝ (C.prism.scalar f) C.prism.domain ((Prism.split k).symm p))
        (EuclideanSpace.single j.succ 1) =
      (fderivWithin ℝ (C.scalar (fun x => f (p.1,x))) C.domain p.2)
        (EuclideanSpace.single j 1)) := by
  have hfp : fderivWithin ℝ (C.prism.scalar f) C.prism.domain ((Prism.split k).symm p) =
      (fderiv ℝ G p).comp (Prism.split k).toContinuousLinearMap := by
    apply HasFDerivWithinAt.fderivWithin _ hup
    have hd := hG.hasFDerivAt.comp ((Prism.split k).symm p) (Prism.split k).hasFDerivAt
    apply hd.hasFDerivWithinAt.congr
    · intro w hw
      have hm : Prism.split k w ∈ Icc (0:ℝ) 1 ×ˢ C.domain := hw
      rw [Function.comp_apply,heq _ hm,C.prism.scalar_eq hw]
      rfl
    · rw [Function.comp_apply,ContinuousLinearEquiv.apply_symm_apply,
        C.prism_scalar_eq ⟨Ioo_subset_Icc_self ht,hz⟩,heq _ ⟨Ioo_subset_Icc_self ht,hz⟩]
  have hft : HasDerivAt (fun t => f (t,C.param ⟨p.2,hz⟩))
      ((fderiv ℝ G p) (1,0)) p.1 := by
    have hd := hG.hasFDerivAt.comp_hasDerivAt p.1
      ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
    apply hd.congr_of_eventuallyEq
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with t ht
    exact (heq (t,p.2) ⟨ht,hz⟩).symm
  have hfx : fderivWithin ℝ (C.scalar (fun x => f (p.1,x))) C.domain p.2 =
      (fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ ℝ (Euc k)) := by
    have hd := hG.hasFDerivAt.comp p.2
      ((hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id (𝕜 := ℝ) p.2))
    apply HasFDerivWithinAt.fderivWithin _ hu
    apply hd.hasFDerivWithinAt.congr
    · intro z hz
      rw [C.scalar_eq hz]
      exact (heq (p.1,z) ⟨Ioo_subset_Icc_self ht,hz⟩).symm
    · rw [C.scalar_eq hz]
      exact (heq p ⟨Ioo_subset_Icc_self ht,hz⟩).symm
  constructor
  · rw [hfp,ContinuousLinearMap.comp_apply]
    change (fderiv ℝ G p) (Prism.split k (EuclideanSpace.single 0 1)) = _
    rw [Prism.split_single_zero,hft.deriv]
  · intro j
    rw [hfp,hfx,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply]
    change (fderiv ℝ G p) (Prism.split k (EuclideanSpace.single j.succ 1)) = _
    rw [Prism.split_single_succ]
    rfl

end CAT0Fillings.IntegerChart

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)

lemma prism_split_measurePreserving :
    MeasurePreserving (Prism.split k).symm
      ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain))
      (volume.restrict C.prism.domain) := by
  rw [Measure.prod_restrict]
  exact MeasurePreserving.symm (Prism.split k).toHomeomorph.toMeasurableEquiv
    ((Prism.split_measurePreserving k).restrict_preimage (measurableSet_Icc.prod C.borel))

lemma ae_prism_fderiv_decompose {f : ℝ × X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∀ᵐ p ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain),
    (fderivWithin ℝ (C.prism.scalar f) C.prism.domain ((Prism.split k).symm p))
        (EuclideanSpace.single 0 1) =
      deriv (fun t => C.scalar (fun x => f (t,x)) p.2) p.1 ∧
    (∀ j : Fin k,
      (fderivWithin ℝ (C.prism.scalar f) C.prism.domain ((Prism.split k).symm p))
        (EuclideanSpace.single j.succ 1) =
      (fderivWithin ℝ (C.scalar (fun x => f (p.1,x))) C.domain p.2)
        (EuclideanSpace.single j 1)) := by
  obtain ⟨G,⟨L,hG⟩,heq⟩ := C.prism_scalar_extension hf
  have hd : ∀ᵐ p ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain),
      DifferentiableAt ℝ G p := by
    rw [Measure.prod_restrict]
    exact ae_restrict_le (hG.ae_differentiableAt
      (μ := (volume : Measure ℝ).prod (volume : Measure (Euc k))))
  have ht : ∀ᵐ t ∂volume.restrict (Icc (0:ℝ) 1), t ∈ Ioo (0:ℝ) 1 := by
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)))]
    exact ae_restrict_mem measurableSet_Ioo
  have hpt := Measure.quasiMeasurePreserving_fst (ν := volume.restrict C.domain) |>.ae ht
  have hpu := Measure.quasiMeasurePreserving_snd (μ := volume.restrict (Icc (0:ℝ) 1)) |>.ae
    (ae_uniqueDiffWithinAt volume C.domain)
  have hpz := Measure.quasiMeasurePreserving_snd (μ := volume.restrict (Icc (0:ℝ) 1)) |>.ae
    (ae_restrict_mem (μ := volume) C.borel)
  have hpp := C.prism_split_measurePreserving.quasiMeasurePreserving.ae
    (ae_uniqueDiffWithinAt volume C.prism.domain)
  filter_upwards [hd,hpt,hpu,hpz,hpp] with p hd ht hu hz hup
  have h := C.prism_fderiv_decompose heq ht hz hd hu hup
  convert h using 2
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext t
  exact C.scalar_eq hz

lemma ae_prism_jacobian_decompose (π : Fin (k+1) → ℝ × X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    ∀ᵐ p ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain),
      C.prism.jacobian π ((Prism.split k).symm p) =
        ∑ i : Fin (k+1), (-1:ℝ)^i.val *
          deriv (fun t => C.scalar (fun x => π i (t,x)) p.2) p.1 *
          C.jacobian (fun j x => π (i.succAbove j) (p.1,x)) p.2 := by
  have h := ae_all_iff.mpr fun i => C.ae_prism_fderiv_decompose (hπ i).choose_spec
  filter_upwards [h] with p hp
  change Matrix.det (Matrix.of (fun i j =>
    (fderivWithin ℝ (C.prism.scalar (π i)) C.prism.domain ((Prism.split k).symm p))
      (EuclideanSpace.single j 1))) = _
  rw [Matrix.det_succ_column_zero]
  simp only [Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [(hp i).1]
  congr 1
  apply congrArg Matrix.det
  ext j l
  exact (hp (i.succAbove j)).2 l

end CAT0Fillings.IntegerChart

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Prism_TimeCoordinate
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint _root_.OAI.CAT0Fillings.EuclideanStraightening.replaceMap_apply _root_.OAI.CAT0Fillings.EuclideanStraightening.straightenMap_zero _root_.OAI.CAT0Fillings.EuclideanStraightening.switchZero_apply_zero _root_.OAI.CAT0Fillings.Prism.tail_apply _root_.OAI.CAT0Fillings.Prism.tail_single_succ _root_.OAI.CAT0Fillings.Prism.tail_single_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)
lemma ae_prism_fderiv_time :
    ∀ᵐ z ∂volume.restrict C.prism.domain,
      fderivWithin ℝ (C.prism.scalar Prod.fst) C.prism.domain z =
        (ContinuousLinearMap.fst ℝ ℝ (Euc k)).comp (Prism.split k).toContinuousLinearMap := by
  filter_upwards [ae_uniqueDiffWithinAt volume C.prism.domain,
    ae_restrict_mem (μ := volume) C.prism.borel] with z hu hz
  let F : Euc (k+1) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ (Euc k)).comp (Prism.split k).toContinuousLinearMap
  have heq : EqOn (C.prism.scalar Prod.fst) F C.prism.domain := by
    intro w hw
    rw [C.prism.scalar_eq hw]
    rfl
  rw [fderivWithin_congr' heq hz]
  exact F.fderivWithin hu

lemma ae_prism_jacobian_time (π : Fin k → ℝ × X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    ∀ᵐ p ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain),
      C.prism.jacobian (Matrix.vecCons Prod.fst π) ((Prism.split k).symm p) =
        C.jacobian (fun i x => π i (p.1,x)) p.2 := by
  have htime := C.prism_split_measurePreserving.quasiMeasurePreserving.ae C.ae_prism_fderiv_time
  have hcoord := ae_all_iff.mpr fun i => C.ae_prism_fderiv_decompose (hπ i).choose_spec
  filter_upwards [htime,hcoord] with p ht hp
  change Matrix.det (Matrix.of (fun i j =>
    (fderivWithin ℝ (C.prism.scalar (Matrix.vecCons Prod.fst π i)) C.prism.domain
      ((Prism.split k).symm p)) (EuclideanSpace.single j 1))) = _
  rw [Matrix.det_succ_row_zero]
  have hrow (j : Fin (k+1)) :
      (fderivWithin ℝ (C.prism.scalar Prod.fst) C.prism.domain ((Prism.split k).symm p))
        (EuclideanSpace.single j 1) = if j = 0 then 1 else 0 := by
    rw [ht]
    induction j using Fin.cases with
    | zero => simp [ContinuousLinearMap.comp_apply]
    | succ j => simp [ContinuousLinearMap.comp_apply]
  simp only [Matrix.of_apply,Matrix.cons_val_zero,hrow]
  simp only [mul_ite,mul_zero,ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true, if_true,
    Fin.val_zero,pow_zero,one_mul]
  apply congrArg Matrix.det
  ext i j
  simpa only [Matrix.submatrix_apply,Matrix.of_apply,Fin.succAbove_zero,Matrix.cons_val_succ]
    using (hp i).2 j

lemma lipschitz_time {f : ℝ × X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (x : X) :
    LipschitzWith K (fun t => f (t,x)) := by
  simpa [Function.comp_def] using hf.comp ((LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ)).prodMk
    (LipschitzWith.const x))

lemma lipschitz_slice {f : ℝ × X → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (t : ℝ) :
    LipschitzWith K (fun x => f (t,x)) := by
  simpa [Function.comp_def] using hf.comp ((LipschitzWith.const t).prodMk
    (LipschitzWith.id : LipschitzWith 1 (id : X → X)))

lemma boundedLip_slice {b : ℝ × X → ℝ} (hb : BoundedLip b) (t : ℝ) :
    BoundedLip (fun x => b (t,x)) :=
  ⟨⟨_,lipschitz_slice hb.1.choose_spec t⟩,hb.2.choose,fun x => hb.2.choose_spec (t,x)⟩

end CAT0Fillings.IntegerChart
end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_CycleFTC
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
local notation "BL" => boundedLipSubmodule (X := X)
lemma IsMetricCurrent.cycle_time_FTC {k : ℕ} {T : Functional X (k+1)}
    (hcur : IsMetricCurrent T) (hT : IntegerRectifiable T) (hz : IsCycle T)
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : Controls T μ)
    (v : Fin (k+2) → ℝ × X → ℝ) (K : ℝ≥0) (hv : ∀ i, LipschitzWith K (v i))
    (a b : ℝ) :
    (∫ t in a..b, ∑ i, (-1:ℝ)^i.val * BorelCoefficients.borelAction μ hcur
      (fun x => deriv (fun s => v i (s,x)) t)
      (fun j x => v (i.succAbove j) (t,x))) =
      T (fun x => v 0 (b,x)) (fun j x => v j.succ (b,x)) -
      T (fun x => v 0 (a,x)) (fun j x => v j.succ (a,x)) := by
  let V (t : ℝ) (i : Fin (k+2)) : BL :=
    ⟨fun x => v i (t,x),boundedLip_of_lipschitz_compact (lipschitz_slice (hv i) t)⟩
  have hx (t i) : LipschitzWith K (V t i : X → ℝ) := lipschitz_slice (hv i) t
  have ht (i x) : LipschitzWith K (fun t => (V t i : X → ℝ) x) := lipschitz_time (hv i) x
  have hd : ∀ᵐ t ∂volume, HasDerivAt (fun s => hcur.fullMultilinear (V s))
      (∑ i, (-1:ℝ)^i.val * BorelCoefficients.borelAction μ hcur
        (fun x => deriv (fun s => v i (s,x)) t) (fun j x => v (i.succAbove j) (t,x))) t := by
    have ha : ∀ᵐ t ∂volume, ∀ i, ∀ᵐ x ∂μ, HasDerivAt (fun s => v i (s,x))
        (deriv (fun s => v i (s,x)) t) t :=
      ae_all_iff.mpr (fun i => ae_time_hasDeriv (hv i) μ)
    filter_upwards [ha] with t ha
    exact hcur.hasDeriv_cycle_path hT hz μ hμ V K hx ht t _
      (fun i => integrable_timeDeriv (hv i) μ t) ha
  have heq : (∫ t in a..b, ∑ i, (-1:ℝ)^i.val * BorelCoefficients.borelAction μ hcur
      (fun x => deriv (fun s => v i (s,x)) t)
      (fun j x => v (i.succAbove j) (t,x))) =
      ∫ t in a..b, deriv (fun s => hcur.fullMultilinear (V s)) t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hd] with t ht _
    exact ht.deriv.symm
  rw [heq,LipschitzWith.integral_deriv_eq_sub (hcur.cycle_time_lipschitz hT hz V K hx ht)]
  rfl

end CAT0Fillings

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_PushBoundary
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

universe u
namespace CurrentOperations
attribute [local instance] Classical.propDecidable
variable {X : Type u} {Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in

lemma pushCurrent_boundarySucc {k : ℕ} (T : Functional X (k+1))
    {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) :
    boundarySucc (pushCurrent f T) = pushCurrent f (boundarySucc T) := by
  funext b π
  by_cases h : Admissible b π
  · have hcons : Admissible (fun _ : Y => (1 : ℝ)) (Matrix.vecCons b π) := by
      refine ⟨BoundedLip.const 1, ?_⟩
      intro i
      refine Fin.cases h.1.1 (fun j => h.2 j) i
    rw [boundarySucc, ite_eq_left h, pushCurrent_apply f T hcons,
      pushCurrent_apply f (boundarySucc T) h, boundarySucc,
      ite_eq_left (admissible_comp h hf)]
    congr 1
    funext i x
    exact Fin.cases rfl (fun _ => rfl) i
  · simp only [boundarySucc, pushCurrent, ite_eq_right h]

omit [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
lemma pushCurrent_zero {k : ℕ} (f : X → Y) :
    pushCurrent f (fun (_ : X → ℝ) (_ : Fin k → X → ℝ) => 0) = 0 := by
  funext b π
  simp only [pushCurrent, ite_self, Pi.zero_apply]

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
lemma pushCurrent_cycle {k : ℕ} {T : Functional X (k+1)}
    (hT : boundarySucc T = 0) {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) :
    boundarySucc (pushCurrent f T) = 0 := by
  rw [pushCurrent_boundarySucc T hf, hT]
  exact pushCurrent_zero f

lemma mass_pushCurrent_le [CompactSpace X] {k : ℕ} {T : Functional X k}
    (hT : IsMetricCurrent T) {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) :
    mass (pushCurrent f T) ≤ (K : ℝ)^k * mass T := by
  obtain ⟨μ, hμ, hc, hm⟩ := hT.exists_controls_mass_eq
  let := hμ
  have hfin : IsFiniteMeasure ((↑(K^k) : ℝ≥0∞) • μ.map f) := by
    constructor
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top (μ.map f) univ)
  calc
    mass (pushCurrent f T) ≤ (((↑(K^k) : ℝ≥0∞) • μ.map f)).real univ :=
      mass_le_measure hfin (pushCurrent_controls hT hc hf)
    _ = (K : ℝ)^k * mass T := by
      rw [hm]
      simp only [Measure.real, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
        ENNReal.coe_toReal, NNReal.coe_pow, Measure.map_apply hf.continuous.measurable
          MeasurableSet.univ, preimage_univ]

end CurrentOperations
end CAT0Fillings

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_GeneralPush
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set MeasureTheory Filter BorelRestriction CurrentOperations
open scoped Topology

namespace IntegerChart
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]
  [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [Nonempty X] [Nonempty Y] {k : ℕ} (C : IntegerChart X k)
theorem push_integerRectifiable (hC : IsMetricCurrent C.action)
    {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) :
    IntegerRectifiable (pushCurrent f C.action) := by
  classical
  obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
  obtain ⟨t,J,hts,ht,hd,hbilip,hzero⟩ :=
    MetricDifferentiation.exists_lipschitz_chart_decomposition C.borel C.bounded.measure_lt_top.ne (hf.comp hL)
  let E i := C.paramExtended '' t i
  have hE i : MeasurableSet (E i) := C.measurableSet_paramExtended_image (ht i) (hts i)
  have hEd : Pairwise (fun i j => Disjoint (E i) (E j)) :=
    fun i j hij => C.paramExtended_disjoint_images (hts i) (hts j) (hd hij)
  let R i := C.restrictDomain (ht i) (hts i)
  have hR i : IsMetricCurrent (R i).action := C.restrictDomain_isMetricCurrent _ _ hC
  have hRact i : (R i).action = restrictCurrent hC (E i) := C.restrictDomain_action _ _ hC
  let D i := (R i).postcompose hf (hbilip i).2
  have hDact i : (D i).action = pushCurrent f (R i).action := (R i).postcompose_action hf (hbilip i).2
  have hD i : IsMetricCurrent (D i).action := by rw [hDact]; exact pushCurrent_isMetricCurrent (hR i) hf
  have hRs : Summable (fun i => mass (R i).action) := by
    simp_rw [hRact]
    exact summable_restriction_mass hC E hE hEd
  have hDs : Summable (fun i => mass (D i).action) := by
    apply (hRs.mul_left ((K : ℝ)^k)).of_nonneg_of_le (fun i => mass_nonneg _)
    intro i
    rw [hDact]
    exact mass_pushCurrent_le (hR i) hf
  have heq : pushCurrent f C.action = fun b π => ∑' i, (D i).action b π := by
    funext b π
    by_cases hab : Admissible b π
    · simp_rw [hDact,pushCurrent_apply f _ hab,hRact]
      rw [←restrictCurrent_iUnion hC E hE hEd,
        ←C.restrictMultiplicity_action hC (MeasurableSet.iUnion hE)]
      rw [action,action,ite_eq_left (admissible_comp hab hf),ite_eq_left (admissible_comp hab hf)]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem C.borel,hzero π hab.2] with z hz hzeroz
      change (C.multiplicity z : ℝ)*C.scalar (b ∘ f) z*C.jacobian (fun i => π i ∘ f) z =
        ↑((C.paramExtended ⁻¹' ⋃ i, E i).indicator C.multiplicity z)*
          C.scalar (b ∘ f) z*C.jacobian (fun i => π i ∘ f) z
      by_cases hzi : z ∈ ⋃ i, t i
      · have him : z ∈ C.paramExtended ⁻¹' ⋃ i, E i := by
          obtain ⟨i,hi⟩ := mem_iUnion.mp hzi
          exact mem_iUnion.mpr ⟨i,⟨z,hi,rfl⟩⟩
        rw [indicator_of_mem him]
      · have hj : C.jacobian (fun i => π i ∘ f) z = 0 := hzeroz hzi
        rw [hj,mul_zero,mul_zero]
    · rw [(pushCurrent_isMetricCurrent hC hf).offDomain b π hab]
      symm
      calc (∑' i, (D i).action b π) = ∑' (_i : ℕ), (0 : ℝ) :=
              tsum_congr fun i => (hD i).offDomain b π hab
        _ = 0 := tsum_zero
  rw [heq]
  exact integerRectifiable_chartSum D hD hDs

end IntegerChart
end CAT0Fillings

namespace CAT0Fillings
open Set MeasureTheory Filter CurrentOperations

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X] [CompactSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [Nonempty X] [Nonempty Y] {k : ℕ}

theorem integerRectifiable_push {T : Functional X k} (hT : IntegerRectifiable T)
    {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) :
    IntegerRectifiable (pushCurrent f T) := by
  classical
  obtain ⟨C,hd,hC,hCS,heq⟩ := hT
  have hP i : IsMetricCurrent (pushCurrent f (C i).action) := pushCurrent_isMetricCurrent (hC i) hf
  have hPI i : IntegerRectifiable (pushCurrent f (C i).action) := (C i).push_integerRectifiable (hC i) hf
  have hPS : Summable (fun i => mass (pushCurrent f (C i).action)) :=
    (hCS.mul_left ((K : ℝ)^k)).of_nonneg_of_le (fun i => mass_nonneg _) (fun i => mass_pushCurrent_le (hC i) hf)
  have hEq : pushCurrent f T = (fun b π => ∑' i, pushCurrent f (C i).action b π) := by
    funext b π
    by_cases hab : Admissible b π
    · simp_rw [pushCurrent_apply f _ hab]
      exact heq _ _
    · simp only [pushCurrent,ite_eq_right hab,tsum_zero]
  rw [hEq]
  exact integerRectifiable_tsum hP hPI hPS

theorem integral_push {T : Functional X k} (hT : IsIntegral k T)
    {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f) :
    IsIntegral k (pushCurrent f T) := by
  cases k with
  | zero => exact ⟨pushCurrent_isMetricCurrent hT.1 hf,integerRectifiable_push hT.2 hf⟩
  | succ k =>
    refine ⟨pushCurrent_isMetricCurrent hT.1 hf,integerRectifiable_push hT.2.1 hf,?_,?_⟩
    · rw [pushCurrent_boundarySucc T hf]
      exact pushCurrent_isMetricCurrent hT.2.2.1 hf
    · rw [pushCurrent_boundarySucc T hf]
      exact integerRectifiable_push hT.2.2.2 hf

end CAT0Fillings

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Prism_Action
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)
lemma prism_action_eq (b : ℝ × X → ℝ) (π : Fin (k+1) → ℝ × X → ℝ)
    (h : Admissible b π) :
    C.prism.action b π =
      ∫ p, (C.multiplicity p.2 : ℝ) * C.scalar (fun x => b (p.1,x)) p.2 *
        C.prism.jacobian π ((Prism.split k).symm p)
          ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain) := by
  rw [action,ite_eq_left h,← C.prism_split_measurePreserving.integral_comp (Prism.split k).symm.toHomeomorph.measurableEmbedding]
  apply integral_congr_ae
  have hp : ∀ᵐ p ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain),
      p ∈ Icc (0:ℝ) 1 ×ˢ C.domain := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Icc.prod C.borel)
  filter_upwards [hp] with p hp
  have hb : C.prism.scalar b ((Prism.split k).symm p) =
      C.scalar (fun x => b (p.1,x)) p.2 := by
    rw [C.prism_scalar_eq hp,C.scalar_eq hp.2]
  rw [hb]
  congr 2

end CAT0Fillings.IntegerChart

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)

lemma integrable_prism_formula (b : ℝ × X → ℝ) (π : Fin (k+1) → ℝ × X → ℝ)
    (h : Admissible b π) :
    Integrable (fun p => (C.multiplicity p.2 : ℝ) * C.scalar (fun x => b (p.1,x)) p.2 *
        C.prism.jacobian π ((Prism.split k).symm p))
      ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain)) := by
  have hi := (C.prism_split_measurePreserving.integrable_comp_emb
    (Prism.split k).symm.toHomeomorph.measurableEmbedding).mpr
      (C.prism.integrable_action_integrand h.1 h.2)
  apply hi.congr
  have hp : ∀ᵐ p ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain),
      p ∈ Icc (0:ℝ) 1 ×ˢ C.domain := by
    rw [Measure.prod_restrict]
    exact ae_restrict_mem (measurableSet_Icc.prod C.borel)
  filter_upwards [hp] with p hp
  have hb : C.prism.scalar b ((Prism.split k).symm p) =
      C.scalar (fun x => b (p.1,x)) p.2 := by
    rw [C.prism_scalar_eq hp,C.scalar_eq hp.2]
  dsimp only [Function.comp_apply]
  rw [hb]
  congr 2

lemma integrable_prism_slice (b : ℝ × X → ℝ) (π : Fin k → ℝ × X → ℝ)
    (h : Admissible b π) :
    Integrable (fun p => (C.multiplicity p.2 : ℝ) * C.scalar (fun x => b (p.1,x)) p.2 *
        C.jacobian (fun i x => π i (p.1,x)) p.2)
      ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain)) := by
  have hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (Matrix.vecCons Prod.fst π i) :=
    Fin.cases ⟨1,LipschitzWith.prod_fst⟩ h.2
  apply (C.integrable_prism_formula b _ ⟨h.1,hπ⟩).congr
  filter_upwards [C.ae_prism_jacobian_time π h.2] with p hp
  rw [hp]

end CAT0Fillings.IntegerChart
end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Prism_Mass
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint _root_.OAI.CAT0Fillings.EuclideanStraightening.replaceMap_apply _root_.OAI.CAT0Fillings.EuclideanStraightening.straightenMap_zero _root_.OAI.CAT0Fillings.EuclideanStraightening.switchZero_apply_zero _root_.OAI.CAT0Fillings.Prism.tail_apply _root_.OAI.CAT0Fillings.Prism.tail_single_succ _root_.OAI.CAT0Fillings.Prism.tail_single_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)
lemma chart_abs_integrand_le [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    [Nonempty X] {ν : Measure X} [IsFiniteMeasure ν] (hν : Controls C.action ν)
    {b : X → ℝ} {π : Fin k → X → ℝ} (hb : BoundedLip b)
    (hπ : ∀ i, LipschitzWith 1 (π i)) :
    (∫ z in C.domain, |(C.multiplicity z : ℝ)*C.scalar b z*C.jacobian π z|) ≤
      ∫ x, |b x| ∂ν := by
  have hw := C.integrable_weighted_jacobian (fun i => ⟨1,hπ i⟩)
  have hm : densityPush (volume.restrict C.domain) C.paramExtended
      (fun z => |(C.multiplicity z : ℝ)*C.jacobian π z|) ≤ ν := by
    simpa using C.weighted_jacobian_le_measure C.action_isMetricCurrent hν π (fun _ => 1) hπ
  have hib : Integrable (fun x => |b x|) ν :=
    hb.continuous.abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc _ = ∫ x, |b x| ∂(densityPush (volume.restrict C.domain) C.paramExtended
      (fun z => |(C.multiplicity z : ℝ)*C.jacobian π z|)) := by
        rw [integral_densityPush _ C.measurable_paramExtended hw.abs
          (Eventually.of_forall fun _ => abs_nonneg _) hb.continuous.abs]
        apply integral_congr_ae
        filter_upwards [C.scalar_ae_paramExtended b] with z hz
        dsimp only [Function.comp_apply] at hz
        rw [hz,abs_mul,abs_mul,abs_mul]
        ring
    _ ≤ _ := integral_mono_measure hm (Eventually.of_forall fun _ => abs_nonneg _) hib

lemma ae_prism_jacobian_bound (π : Fin (k+1) → ℝ × X → ℝ)
    (hπ : ∀ i, LipschitzWith 1 (π i)) :
    ∀ᵐ p ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain),
      |C.prism.jacobian π ((Prism.split k).symm p)| ≤
        ∑ i : Fin (k+1), |C.jacobian (fun j x => π (i.succAbove j) (p.1,x)) p.2| := by
  have hpz := Measure.quasiMeasurePreserving_snd (μ := volume.restrict (Icc (0:ℝ) 1)) |>.ae
    (ae_restrict_mem (μ := volume) C.borel)
  filter_upwards [C.ae_prism_jacobian_decompose π (fun i => ⟨1,hπ i⟩),hpz] with p hd hz
  rw [hd]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  have hl : LipschitzWith 1 (fun t => C.scalar (fun x => π i (t,x)) p.2) := by
    have heq : (fun t => C.scalar (fun x => π i (t,x)) p.2) =
        (fun t => π i (t,C.param ⟨p.2,hz⟩)) := funext fun _ => C.scalar_eq hz
    rw [heq]
    exact lipschitz_time (hπ i) _
  have hD : |deriv (fun t => C.scalar (fun x => π i (t,x)) p.2) p.1| ≤ 1 := by
    simpa only [Real.norm_eq_abs,NNReal.coe_one] using norm_deriv_le_of_lipschitz hl
  simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
  exact mul_le_of_le_one_left (abs_nonneg _) hD

lemma prism_controls [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    [Nonempty X] {ν : Measure X} [IsFiniteMeasure ν] (hν : Controls C.action ν) :
    Controls C.prism.action ((k+1 : ℝ≥0) • (volume.restrict (Icc (0:ℝ) 1)).prod ν) := by
  intro b π hb hπ
  let F (i : Fin (k+1)) (p : ℝ × Euc k) :=
    |(C.multiplicity p.2 : ℝ) * C.scalar (fun x => b (p.1,x)) p.2 *
      C.jacobian (fun j x => π (i.succAbove j) (p.1,x)) p.2|
  have hF (i : Fin (k+1)) : Integrable (F i)
      ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain)) :=
    (C.integrable_prism_slice b (fun j => π (i.succAbove j))
      ⟨hb,fun j => ⟨1,hπ _⟩⟩).abs
  have hib : Integrable (fun p : ℝ × X => |b p|)
      ((volume.restrict (Icc (0:ℝ) 1)).prod ν) := by
    obtain ⟨M,hM⟩ := hb.2
    exact Integrable.of_bound hb.continuous.abs.aestronglyMeasurable M
      (Eventually.of_forall fun p => by simpa using hM p)
  have hinner (i : Fin (k+1)) :
      (∫ p, F i p ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain)) ≤
      ∫ p : ℝ × X, |b p| ∂(volume.restrict (Icc (0:ℝ) 1)).prod ν := by
    rw [integral_prod _ (hF i),integral_prod _ hib]
    apply integral_mono_ae (hF i).integral_prod_left hib.integral_prod_left
    exact Eventually.of_forall fun t => C.chart_abs_integrand_le hν
      (boundedLip_slice hb t) (fun j => lipschitz_slice (hπ (i.succAbove j)) t)
  rw [C.prism_action_eq b π ⟨hb,fun i => ⟨1,hπ i⟩⟩]
  calc _ ≤ ∫ p, |(C.multiplicity p.2 : ℝ)*C.scalar (fun x => b (p.1,x)) p.2*
        C.prism.jacobian π ((Prism.split k).symm p)|
        ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain) := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
            (μ := ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain)))
            (fun p => (C.multiplicity p.2 : ℝ)*C.scalar (fun x => b (p.1,x)) p.2*
              C.prism.jacobian π ((Prism.split k).symm p))
    _ ≤ ∫ p, ∑ i, F i p
        ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain) := by
      apply integral_mono_ae (C.integrable_prism_formula b π ⟨hb,fun i => ⟨1,hπ i⟩⟩).abs
        (integrable_finsetSum _ fun i _ => hF i)
      filter_upwards [C.ae_prism_jacobian_bound π hπ] with p hp
      simp only [F,abs_mul,← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hp (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = ∑ i, ∫ p, F i p
        ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain) :=
      integral_finsetSum _ fun i _ => hF i
    _ ≤ ∑ _i : Fin (k+1), ∫ p : ℝ × X, |b p|
        ∂(volume.restrict (Icc (0:ℝ) 1)).prod ν := Finset.sum_le_sum fun i _ => hinner i
    _ = _ := by
      rw [integral_smul_nnreal_measure]
      simp [NNReal.smul_def]

end CAT0Fillings.IntegerChart

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Prism_Family
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped NNReal ENNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}

lemma prismFamily_current (C : ℕ → IntegerChart X k)
    (hs : Summable (fun i => mass (C i).action)) : IsMetricCurrent (prismFamily C) := by
  choose μ hfin hμ heq using fun i => (C i).action_isMetricCurrent.exists_controls_mass_eq
  let : ∀ i, IsFiniteMeasure (μ i) := hfin
  let ν : ℕ → Measure (ℝ × X) := fun i =>
    (k+1:ℝ≥0) • (volume.restrict (Icc (0:ℝ) 1)).prod (μ i)
  have hν (i) : Controls (C i).prism.action (ν i) := (C i).prism_controls (hμ i)
  have hvreal (i) : (ν i).real univ = (k+1:ℝ)*mass (C i).action := by
    rw [heq i]
    dsimp [ν]
    rw [measureReal_nnreal_smul_apply]
    simp [measureReal_def,←Set.univ_prod_univ,Measure.prod_prod]
  apply isMetricCurrent_tsum_controlled (μ := ν) (fun i => (C i).prism.action_isMetricCurrent) hν
  simpa only [hvreal] using hs.mul_left (k+1:ℝ)

end CAT0Fillings
end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Prism_IntegralAction
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint _root_.OAI.CAT0Fillings.EuclideanStraightening.replaceMap_apply _root_.OAI.CAT0Fillings.EuclideanStraightening.straightenMap_zero _root_.OAI.CAT0Fillings.EuclideanStraightening.switchZero_apply_zero _root_.OAI.CAT0Fillings.Prism.tail_apply _root_.OAI.CAT0Fillings.Prism.tail_single_succ _root_.OAI.CAT0Fillings.Prism.tail_single_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal

namespace CAT0Fillings.IntegerChart
open Set MeasureTheory Measure Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)
omit [CompactSpace X] in
lemma integrable_prism_minor_derivative (v : Fin (k+1) → ℝ × X → ℝ) (K : ℝ≥0)
    (hv : ∀ i, LipschitzWith K (v i)) (i : Fin (k+1)) :
    Integrable (fun p : ℝ × Euc k => (C.multiplicity p.2 : ℝ) *
      C.jacobian (fun j x => v (i.succAbove j) (p.1,x)) p.2 *
      deriv (fun s => v i (s,C.paramExtended p.2)) p.1)
      ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain)) := by
  have hi := C.integrable_prism_slice (fun _ => 1) (fun j => v (i.succAbove j))
    ⟨BoundedLip.const 1,fun j => ⟨K,hv _⟩⟩
  have hi' : Integrable (fun p : ℝ × Euc k => (C.multiplicity p.2 : ℝ) *
      C.jacobian (fun j x => v (i.succAbove j) (p.1,x)) p.2)
      ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain)) := by
    apply hi.congr
    have hz := (Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict (Icc (0:ℝ) 1))).ae
        (ae_restrict_mem (μ := volume) C.borel)
    filter_upwards [hz] with p hp
    rw [C.scalar_eq hp]
    simp
  have hm : Measurable (fun p : ℝ × Euc k =>
      deriv (fun s => v i (s,C.paramExtended p.2)) p.1) :=
    (measurable_timeDeriv (hv i).continuous).comp
      (measurable_fst.prodMk (C.measurable_paramExtended.comp measurable_snd))
  exact hi'.mul_bdd hm.aestronglyMeasurable
    (Eventually.of_forall fun p => norm_deriv_le_of_lipschitz
      (CAT0Fillings.lipschitz_time (hv i) (C.paramExtended p.2)))

lemma prism_action_one_eq_integral (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : Controls C.action μ) (v : Fin (k+1) → ℝ × X → ℝ) (K : ℝ≥0)
    (hv : ∀ i, LipschitzWith K (v i)) :
    C.prism.action (fun _ => 1) v =
      ∫ t in (0:ℝ)..1, ∑ i, (-1:ℝ)^i.val *
        BorelCoefficients.borelAction μ C.action_isMetricCurrent
          (fun x => deriv (fun s => v i (s,x)) t)
          (fun j x => v (i.succAbove j) (t,x)) := by
  let F (i : Fin (k+1)) (p : ℝ × Euc k) : ℝ :=
    (C.multiplicity p.2 : ℝ) * C.jacobian (fun j x => v (i.succAbove j) (p.1,x)) p.2 *
      deriv (fun s => v i (s,C.paramExtended p.2)) p.1
  have hFi i : Integrable (F i)
      ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain)) :=
    C.integrable_prism_minor_derivative v K hv i
  have hF : Integrable (fun p => ∑ i, (-1:ℝ)^i.val * F i p)
      ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain)) :=
    integrable_finsetSum _ (fun i _ => (hFi i).const_mul _)
  have hi (t i) : BorelCoefficients.borelAction μ C.action_isMetricCurrent
      (fun x => deriv (fun s => v i (s,x)) t) (fun j x => v (i.succAbove j) (t,x)) =
      ∫ z, F i (t,z) ∂volume.restrict C.domain := by
    apply C.borelAction_eq_integral C.action_isMetricCurrent hμ
      ((measurable_timeDeriv (hv i).continuous).comp (measurable_const.prodMk measurable_id))
      ⟨K,fun x => norm_deriv_le_of_lipschitz
        (CAT0Fillings.lipschitz_time (hv i) x)⟩
      _ (fun j => ⟨K,CAT0Fillings.lipschitz_slice (hv _) t⟩)
  rw [C.prism_action_eq (fun _ => 1) v ⟨BoundedLip.const 1,fun i => ⟨K,hv i⟩⟩]
  calc
    _ = ∫ p, ∑ i, (-1:ℝ)^i.val * F i p
        ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain) := by
      apply integral_congr_ae
      have hz := (Measure.quasiMeasurePreserving_snd
        (μ := volume.restrict (Icc (0:ℝ) 1))).ae (ae_restrict_mem (μ := volume) C.borel)
      filter_upwards [C.ae_prism_jacobian_decompose v (fun i => ⟨K,hv i⟩),hz] with p hp hz
      rw [C.scalar_eq hz,hp,mul_one,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have he : (fun t => C.scalar (fun x => v i (t,x)) p.2) =
          (fun t => v i (t,C.paramExtended p.2)) := by
        funext t
        simp only [C.scalar_eq hz,paramExtended,dite_eq_left hz]
      rw [he]
      dsimp [F]
      ring
    _ = ∫ t, ∫ z, ∑ i, (-1:ℝ)^i.val * F i (t,z)
        ∂volume.restrict C.domain ∂volume.restrict (Icc (0:ℝ) 1) := integral_prod _ hF
    _ = ∫ t in (0:ℝ)..1, ∑ i, (-1:ℝ)^i.val *
        BorelCoefficients.borelAction μ C.action_isMetricCurrent
          (fun x => deriv (fun s => v i (s,x)) t)
          (fun j x => v (i.succAbove j) (t,x)) := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),←integral_Icc_eq_integral_Ioc]
      apply integral_congr_ae
      have ha := ae_all_iff.mpr (fun i => (hFi i).prod_right_ae)
      filter_upwards [ha] with t ht
      rw [integral_finsetSum Finset.univ (fun i _ => (ht i).const_mul _)]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_const_mul,hi]

end CAT0Fillings.IntegerChart

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Prism_TimeAction
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal

namespace CAT0Fillings
open Set MeasureTheory Measure Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] {k : ℕ}

lemma timeAction_bound {T : Functional X k} (μ : Measure X) [IsFiniteMeasure μ]
    (hT : IsMetricCurrent T) (hμ : Controls T μ)
    (v : Fin (k+1) → ℝ × X → ℝ) (K : ℝ≥0) (hv : ∀ i, LipschitzWith K (v i)) (t : ℝ) :
    |timeAction μ hT v t| ≤ ((k+1:ℝ)*(K:ℝ)^(k+1))*μ.real univ := by
  have hi (i : Fin (k+1)) : |BorelCoefficients.borelAction μ hT
      (fun x => deriv (fun s => v i (s,x)) t) (fun j x => v (i.succAbove j) (t,x))| ≤
      (K:ℝ)^(k+1)*μ.real univ := by
    have hb := BorelCoefficients.borelAction_bound μ hT hμ
      (integrable_timeDeriv (hv i) μ t) (fun j x => v (i.succAbove j) (t,x)) (fun _ => K)
      (fun j => lipschitz_slice (hv _) t)
    have hI : (∫ x, |deriv (fun s => v i (s,x)) t| ∂μ) ≤ μ.real univ*(K:ℝ) := by
      have H := integral_mono (integrable_timeDeriv (hv i) μ t).abs
        (integrable_const (K:ℝ)) (fun x => norm_deriv_le_of_lipschitz (lipschitz_time (hv i) x))
      simpa only [integral_const,smul_eq_mul] using H
    calc
      _ ≤ (K:ℝ)^k * ∫ x, |deriv (fun s => v i (s,x)) t| ∂μ := by simpa using hb
      _ ≤ (K:ℝ)^k*(μ.real univ*(K:ℝ)) := mul_le_mul_of_nonneg_left hI (pow_nonneg K.coe_nonneg _)
      _ = _ := by rw [pow_succ]; ring
  calc
    _ ≤ ∑ i : Fin (k+1), |(-1:ℝ)^i.val * BorelCoefficients.borelAction μ hT
      (fun x => deriv (fun s => v i (s,x)) t) (fun j x => v (i.succAbove j) (t,x))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (k+1), (K:ℝ)^(k+1)*μ.real univ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul] using hi i
    _ = _ := by simp; ring

lemma IntegerChart.integrable_timeAction [Nonempty X] (C : IntegerChart X k)
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : Controls C.action μ)
    (v : Fin (k+1) → ℝ × X → ℝ) (K : ℝ≥0) (hv : ∀ i, LipschitzWith K (v i)) :
    Integrable (timeAction μ C.action_isMetricCurrent v) (volume.restrict (Icc (0:ℝ) 1)) := by
  apply integrable_finsetSum
  intro i _
  apply Integrable.const_mul
  have hi := (C.integrable_prism_minor_derivative v K hv i).integral_prod_left
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  apply C.borelAction_eq_integral C.action_isMetricCurrent hμ
    ((measurable_timeDeriv (hv i).continuous).comp (measurable_const.prodMk measurable_id))
    ⟨K,fun x => norm_deriv_le_of_lipschitz (lipschitz_time (hv i) x)⟩
    _ (fun j => ⟨K,lipschitz_slice (hv _) t⟩)

end CAT0Fillings

namespace CAT0Fillings
open Set MeasureTheory Measure Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}

lemma prismFamily_action_one {T : Functional X k} (hT : IsMetricCurrent T)
    (C : ℕ → IntegerChart X k) (hs : Summable (fun i => mass (C i).action))
    (heq : ∀ b π, T b π = ∑' i, (C i).action b π)
    (v : Fin (k+1) → ℝ × X → ℝ) (K : ℝ≥0) (hv : ∀ i, LipschitzWith K (v i)) :
    ∃ (μ : Measure X) (_ : IsFiniteMeasure μ), Controls T μ ∧
      prismFamily C (fun _ => 1) v = ∫ t in (0:ℝ)..1, timeAction μ hT v t := by
  choose μ hfin hμ he using fun j => (C j).action_isMetricCurrent.exists_controls_mass_eq
  let : ∀ j, IsFiniteMeasure (μ j) := hfin
  have hsμ : Summable (fun j => (μ j).real univ) := by simpa only [←he] using hs
  let : IsFiniteMeasure (Measure.sum μ) := finite_sum_measure_of_summable_total μ hsμ
  refine ⟨Measure.sum μ,inferInstance,controls_sum_general hμ heq,?_⟩
  let F (j : ℕ) (t : ℝ) := timeAction (μ j) (C j).action_isMetricCurrent v t
  have hFi (j) : Integrable (F j) (volume.restrict (Icc (0:ℝ) 1)) :=
    (C j).integrable_timeAction (μ j) (hμ j) v K hv
  have hsF : Summable (fun j => ∫ t, ‖F j t‖ ∂volume.restrict (Icc (0:ℝ) 1)) := by
    apply (hsμ.mul_left ((k+1:ℝ)*(K:ℝ)^(k+1))).of_nonneg_of_le
      (fun j => integral_nonneg (fun _ => norm_nonneg _))
    intro j
    have H := integral_mono (hFi j).norm
      (integrable_const (((k+1:ℝ)*(K:ℝ)^(k+1))*(μ j).real univ))
      (fun t => timeAction_bound (μ j) (C j).action_isMetricCurrent (hμ j) v K hv t)
    simpa [measureReal_def] using H
  have hsum (t) : (∑' j, F j t) = timeAction (Measure.sum μ) hT v t := by
    have hS (i : Fin (k+1)) : Summable (fun j =>
        BorelCoefficients.borelAction (μ j) (C j).action_isMetricCurrent
          (fun x => deriv (fun s => v i (s,x)) t) (fun l x => v (i.succAbove l) (t,x))) :=
      BorelCoefficients.summable_borelAction μ (fun j => (C j).action_isMetricCurrent) hμ
        (integrable_timeDeriv (hv i) (Measure.sum μ) t) _
        (fun l => ⟨K,lipschitz_slice (hv _) t⟩)
    dsimp only [F,timeAction]
    rw [Summable.tsum_finsetSum (fun i _ => (hS i).mul_left _)]
    apply Finset.sum_congr rfl
    intro i _
    rw [tsum_mul_left]
    congr 1
    exact (BorelCoefficients.borelAction_sum μ hT
      (fun j => (C j).action_isMetricCurrent) hμ heq
        (integrable_timeDeriv (hv i) (Measure.sum μ) t) _
        (fun l => ⟨K,lipschitz_slice (hv _) t⟩)).symm
  calc
    _ = ∑' j, ∫ t, F j t ∂volume.restrict (Icc (0:ℝ) 1) := by
      apply tsum_congr
      intro j
      rw [(C j).prism_action_one_eq_integral (μ j) (hμ j) v K hv,
        intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),←integral_Icc_eq_integral_Ioc]
      rfl
    _ = ∫ t, ∑' j, F j t ∂volume.restrict (Icc (0:ℝ) 1) :=
      (hasSum_integral_of_summable_integral_norm hFi hsF).tsum_eq
    _ = _ := by
      simp only [hsum]
      rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),←integral_Icc_eq_integral_Ioc]

end CAT0Fillings
end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Prism_Boundary
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal

namespace CAT0Fillings
open Set MeasureTheory Measure Filter
open scoped Topology NNReal ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}
lemma prismFamily_boundary_cycle {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hrect : IntegerRectifiable T) (hz : IsCycle T)
    (C : ℕ → IntegerChart X (k+1)) (hs : Summable (fun i => mass (C i).action))
    (heq : ∀ b π, T b π = ∑' i, (C i).action b π)
    (b : ℝ × X → ℝ) (π : Fin (k+1) → ℝ × X → ℝ) (hab : Admissible b π) :
    boundarySucc (prismFamily C) b π =
      T (fun x => b (1,x)) (fun j x => π j (1,x)) -
      T (fun x => b (0,x)) (fun j x => π j (0,x)) := by
  let v : Fin (k+2) → ℝ × X → ℝ := Matrix.vecCons b π
  have hV : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (v i) := by
    intro i
    exact Fin.cases hab.1.1 (fun j => hab.2 j) i
  choose K hK using hV
  let L : ℝ≥0 := ∑ i, K i
  have hL i : LipschitzWith L (v i) :=
    (hK i).weaken (Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ i))
  obtain ⟨μ,hfin,hμ,hformula⟩ := prismFamily_action_one hT C hs heq v L hL
  let : IsFiniteMeasure μ := hfin
  rw [boundarySucc,ite_eq_left hab,hformula]
  exact hT.cycle_time_FTC hrect hz μ hμ v L hL 0 1

end CAT0Fillings

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Prism_ClosedCylinder
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal

namespace CAT0Fillings
open Set MeasureTheory CurrentOperations
open scoped NNReal ENNReal Topology

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)

lemma closedPrism_action : C.closedPrism.action = pushCurrent cylinderClamp C.prism.action :=
  C.prism.postcompose_action _ _

lemma closedPrism_image : C.closedPrism.image = cylinderClamp '' C.prism.image :=
  C.prism.postcompose_image _ _

lemma closedPrism_image_disjoint {D : IntegerChart X k} (hCD : Disjoint C.image D.image) :
    Disjoint C.closedPrism.image D.closedPrism.image := by
  rw [C.closedPrism_image,D.closedPrism_image]
  apply Set.disjoint_left.mpr
  rintro p ⟨x,hx,rfl⟩ ⟨y,hy,heq⟩
  have hxI : x.1 ∈ Icc (0:ℝ) 1 := (C.prism_image ▸ hx).1
  have hyI : y.1 ∈ Icc (0:ℝ) 1 := (D.prism_image ▸ hy).1
  have hxy : y = x := by
    simpa only [cylinderEmbed_clamp _ hxI,cylinderEmbed_clamp _ hyI] using
      congrArg cylinderEmbed heq
  exact (Set.disjoint_left.mp (C.prism_image_disjoint hCD) hx) (hxy ▸ hy)

lemma mass_closedPrism_le [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    [Nonempty X] : mass C.closedPrism.action ≤ (k+1:ℝ)*mass C.action := by
  obtain ⟨μ,hfin,hμ,heq⟩ := C.action_isMetricCurrent.exists_controls_mass_eq
  let : IsFiniteMeasure μ := hfin
  let ν : Measure (ℝ × X) := (k+1:ℝ≥0) • (volume.restrict (Icc (0:ℝ) 1)).prod μ
  have hν : Controls C.prism.action ν := C.prism_controls hμ
  have hc := pushCurrent_controls C.prism.action_isMetricCurrent hν cylinderClamp_lipschitz
  simp only [one_pow,ENNReal.coe_one,one_smul] at hc
  rw [C.closedPrism_action]
  apply (mass_le_measure (inferInstance : IsFiniteMeasure (ν.map cylinderClamp)) hc).trans_eq
  rw [Measure.real,Measure.map_apply cylinderClamp_lipschitz.continuous.measurable
    MeasurableSet.univ,preimage_univ]
  change ν.real univ = _
  dsimp [ν]
  rw [heq,measureReal_nnreal_smul_apply]
  simp [measureReal_def,←Set.univ_prod_univ,Measure.prod_prod]

end IntegerChart

end CAT0Fillings
end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Prism_ClosedFamily
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal

namespace CAT0Fillings
open Set MeasureTheory CurrentOperations
open scoped NNReal ENNReal Topology

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X] in
lemma closedPrismFamily_action (C : ℕ → IntegerChart X k) (b : ClosedCylinder X → ℝ)
    (π : Fin (k+1) → ClosedCylinder X → ℝ) :
    closedPrismFamily C b π = ∑' i, (C i).closedPrism.action b π := by
  simp_rw [IntegerChart.closedPrism_action]
  by_cases hab : Admissible b π
  · simp only [closedPrismFamily,pushCurrent_apply _ _ hab,prismFamily]
  · simp only [closedPrismFamily,pushCurrent,ite_eq_right hab,tsum_zero]

lemma closedPrismFamily_current (C : ℕ → IntegerChart X k)
    (hs : Summable (fun i => mass (C i).action)) : IsMetricCurrent (closedPrismFamily C) :=
  pushCurrent_isMetricCurrent (prismFamily_current C hs) cylinderClamp_lipschitz

lemma closedPrismFamily_rectifiable (C : ℕ → IntegerChart X k)
    (hd : Pairwise (fun i j => Disjoint (C i).image (C j).image))
    (hs : Summable (fun i => mass (C i).action)) : IntegerRectifiable (closedPrismFamily C) := by
  refine ⟨fun i => (C i).closedPrism,fun i j hij => (C i).closedPrism_image_disjoint (hd hij),
    fun i => (C i).closedPrism.action_isMetricCurrent,?_,closedPrismFamily_action C⟩
  exact (hs.mul_left (k+1:ℝ)).of_nonneg_of_le
    (fun i => mass_nonneg _) (fun i => (C i).mass_closedPrism_le)

end CAT0Fillings

namespace CAT0Fillings
open Set MeasureTheory CurrentOperations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma closedPrismFamily_boundary_cycle {k : ℕ} {T : Functional X (k+1)}
    (hT : IsMetricCurrent T) (hrect : IntegerRectifiable T) (hz : boundarySucc T = 0)
    (C : ℕ → IntegerChart X (k+1)) (hs : Summable (fun i => mass (C i).action))
    (heq : ∀ b π, T b π = ∑' i, (C i).action b π)
    (b : ClosedCylinder X → ℝ) (π : Fin (k+1) → ClosedCylinder X → ℝ)
    (hab : Admissible b π) :
    boundarySucc (closedPrismFamily C) b π =
      T (fun x => b (⟨1,by constructor <;> norm_num⟩,x))
        (fun j x => π j (⟨1,by constructor <;> norm_num⟩,x)) -
      T (fun x => b (⟨0,by constructor <;> norm_num⟩,x))
        (fun j x => π j (⟨0,by constructor <;> norm_num⟩,x)) := by
  rw [closedPrismFamily,pushCurrent_boundarySucc _ cylinderClamp_lipschitz,
    pushCurrent_apply _ _ hab,
    prismFamily_boundary_cycle hT hrect hz C hs heq _ _
      (admissible_comp hab cylinderClamp_lipschitz)]
  simp only [Function.comp_apply,cylinderClamp,projIcc_of_mem (by norm_num : (0:ℝ) ≤ 1)
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num),
    projIcc_of_mem (by norm_num : (0:ℝ) ≤ 1)
    (show (0:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)]

end CAT0Fillings

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_PushMajorant
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
open MeasureTheory Set Filter CurrentOperations

namespace IntegerChart
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [Nonempty X] [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  {k : ℕ} (C : IntegerChart X k)

theorem push_majorant_controls {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f)
    {J : Euc k → ℝ}
    (hρ : Integrable (fun z => |(C.multiplicity z : ℝ)| *J z) (volume.restrict C.domain))
    (hJ : 0 ≤ᵐ[volume.restrict C.domain] J)
    (hdet : ∀ π : Fin k → Y → ℝ, (∀ i, LipschitzWith 1 (π i)) →
      ∀ᵐ z ∂volume.restrict C.domain, |C.jacobian (fun i => π i ∘ f) z| ≤ J z) :
    Controls (pushCurrent f C.action)
      (densityPush (volume.restrict C.domain) (f ∘ C.paramExtended)
        (fun z => |(C.multiplicity z : ℝ)| *J z)) := by
  intro b π hb hπ
  let μ := volume.restrict C.domain
  have hφ := hf.continuous.measurable.comp C.measurable_paramExtended
  have hbmeas := hb.continuous.measurable.comp hφ
  obtain ⟨M,hM⟩ := hb.2
  have hupper : Integrable
      (fun z => (|(C.multiplicity z : ℝ)| *J z)*|b (f (C.paramExtended z))|) μ :=
    hρ.mul_bdd hbmeas.abs.aestronglyMeasurable
      (Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs,abs_abs] using hM _)
  have hρ0 : 0 ≤ᵐ[μ] fun z => |(C.multiplicity z : ℝ)| *J z :=
    hJ.mono fun z hz => mul_nonneg (abs_nonneg _) hz
  rw [integral_densityPush μ hφ hρ hρ0 hb.continuous.abs]
  rw [pushCurrent_apply f C.action ⟨hb,fun i => ⟨1,hπ i⟩⟩,
    action,ite_eq_left (admissible_comp ⟨hb,fun i => ⟨1,hπ i⟩⟩ hf)]
  rw [←Real.norm_eq_abs]
  apply le_trans (norm_integral_le_integral_norm _) ?_
  change (∫ z, |(C.multiplicity z : ℝ)*C.scalar (b ∘ f) z*
    C.jacobian (fun i => π i ∘ f) z| ∂μ) ≤ _
  apply integral_mono_ae
    (C.integrable_action_integrand (boundedLip_comp hb hf)
      (admissible_comp ⟨hb,fun i => ⟨1,hπ i⟩⟩ hf).2).abs hupper
  filter_upwards [hdet π hπ,C.scalar_ae_paramExtended (b ∘ f)] with z hz hbz
  rw [abs_mul,abs_mul,hbz]
  change |(C.multiplicity z : ℝ)| *|b (f (C.paramExtended z))| *
    |C.jacobian (fun i => π i ∘ f) z| ≤ _
  calc _ ≤ (|(C.multiplicity z : ℝ)| *|b (f (C.paramExtended z))|)*J z :=
      mul_le_mul_of_nonneg_left hz (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = _ := by ring

theorem push_mass_le_majorant {f : X → Y} {K : ℝ≥0} (hf : LipschitzWith K f)
    {J : Euc k → ℝ}
    (hρ : Integrable (fun z => |(C.multiplicity z : ℝ)| *J z) (volume.restrict C.domain))
    (hJ : 0 ≤ᵐ[volume.restrict C.domain] J)
    (hdet : ∀ π : Fin k → Y → ℝ, (∀ i, LipschitzWith 1 (π i)) →
      ∀ᵐ z ∂volume.restrict C.domain, |C.jacobian (fun i => π i ∘ f) z| ≤ J z) :
    mass (pushCurrent f C.action) ≤
      ∫ z, |(C.multiplicity z : ℝ)| *J z ∂volume.restrict C.domain := by
  let ν := densityPush (volume.restrict C.domain) (f ∘ C.paramExtended)
    (fun z => |(C.multiplicity z : ℝ)| *J z)
  have hfin : IsFiniteMeasure ν := densityPush_finite _ _ hρ
  have hc := C.push_majorant_controls hf hρ hJ hdet
  have hu : ν.real univ = ∫ z, |(C.multiplicity z : ℝ)| *J z ∂volume.restrict C.domain := by
    have hi := integral_densityPush (volume.restrict C.domain)
      (hf.continuous.measurable.comp C.measurable_paramExtended) hρ
      (hJ.mono fun z hz => mul_nonneg (abs_nonneg _) hz) continuous_const (b := fun _ => (1:ℝ))
    simpa only [integral_const,smul_eq_mul,mul_one] using hi
  exact (mass_le_measure hfin hc).trans_eq hu
end IntegerChart
end CAT0Fillings

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Fillings_Attainment
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings
open Foundations Slicing

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma fillingVolume_le {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] {k : ℕ}
    {T : Functional X (k+1)} {S : Functional X (k+2)}
    (hS : IsIntegral (k+2) S) (hb : boundarySucc S = T) : fillingVolume T ≤ mass S := by
  apply csInf_le
  · exact ⟨0,by rintro r ⟨U,_,_,rfl⟩; exact mass_nonneg U⟩
  · exact ⟨S,hS,hb,rfl⟩

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_SpatialForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma det_updateRow_identity (j : ι) (v : ι → ℝ) :
    (Matrix.updateRow (1 : Matrix ι ι ℝ) j v).det = v j := by
  have he : (∑ i : ι, v i • (1 : Matrix ι ι ℝ) i) = v := by
    ext l
    simp [Matrix.one_apply]
  rw [←he,Matrix.det_updateRow_sum]
  simp [Matrix.one_apply]

theorem hasDerivAt_det_at_identity {A : ℝ → Matrix ι ι ℝ}
    {B : Matrix ι ι ℝ} {t : ℝ} (hA : A t = 1) (hd : HasDerivAt A B t) :
    HasDerivAt (fun s => (A s).det) B.trace t := by
  let D : ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ :=
    ⟨Matrix.detRowAlternating.toMultilinearMap,continuous_id.matrix_det⟩
  have hD := (D.hasFDerivAt (A t)).comp_hasDerivAt t hd
  change HasDerivAt (fun s => (A s).det) (D.linearDeriv (A t) B) t at hD
  have hv : D.linearDeriv (fun i j => A t i j) (fun i j => B i j) = B.trace := by
    rw [ContinuousMultilinearMap.linearDeriv_apply]
    change (∑ i, (Matrix.updateRow (A t) i (B i)).det) = B.trace
    rw [hA]
    simp only [det_updateRow_identity,Matrix.trace,Matrix.diag]
  exact hD.congr_deriv hv

end CAT0Fillings

open Matrix
open scoped RealInnerProductSpace MatrixOrder

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_MetricDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Matrix
open scoped BigOperators Matrix.Norms.Elementwise

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] in
lemma hasDerivAt_matrix_mul_const {A : ℝ → Matrix ι ι ℝ} {B : Matrix ι ι ℝ}
    {t : ℝ} (hd : HasDerivAt A B t) (G : Matrix ι ι ℝ) :
    HasDerivAt (fun s => A s*G) (B*G) t := by
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro j
  simp only [Matrix.mul_apply]
  exact HasDerivAt.fun_sum fun l _ =>
    ((hasDerivAt_pi.mp (hasDerivAt_pi.mp hd i)) l).mul_const (G l j)

theorem hasDerivAt_det_at_nonsingular {A : ℝ → Matrix ι ι ℝ}
    {B G : Matrix ι ι ℝ} {t : ℝ} (hA : A t = G) (hG : G.det ≠ 0)
    (hd : HasDerivAt A B t) :
    HasDerivAt (fun s => (A s).det) ((B*G⁻¹).trace*G.det) t := by
  have hid : A t*G⁻¹ = 1 := by rw [hA,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hG)]
  have h := (hasDerivAt_det_at_identity (A := fun s => A s*G⁻¹) hid (hasDerivAt_matrix_mul_const hd G⁻¹)).mul_const G.det
  have he : (fun s => (A s).det) = (fun s => (A s*G⁻¹).det*G.det) := by
    funext s
    rw [Matrix.det_mul,Matrix.det_nonsing_inv,Ring.inverse_eq_inv]
    field_simp
  rw [he]
  exact h

omit [DecidableEq ι] in
lemma metricSpatialRadialForm_hasDerivAt_zero (G : Matrix ι ι ℝ) (g r : ℝ) (α γ : ι → ℝ) :
    HasDerivAt (fun t => metricSpatialRadialForm G g r t α γ)
      ((-2*g) • G-r • (vecMulVec α γ+vecMulVec γ α)) 0 := by
  apply hasDerivAt_pi.2
  intro i
  apply hasDerivAt_pi.2
  intro j
  have hl := (hasDerivAt_const (0:ℝ) 1).sub ((hasDerivAt_id (0:ℝ)).mul_const g)
  have ht := hasDerivAt_id (0:ℝ)
  have h := (((hl.fun_pow 2).mul_const (G i j)).sub
    (((hl.mul ht).mul_const r).mul_const (α i*γ j+γ i*α j))).add
    (((ht.fun_pow 2).mul_const (r^2)).mul_const (γ i*γ j))
  refine (h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv (Eq.symm ?_)
  · beta_reduce
    simp [metricSpatialRadialForm,Matrix.vecMulVec_apply,mul_add]
  · simp [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,mul_add]

lemma trace_radial_matrix_derivative (G : Matrix ι ι ℝ) (g r : ℝ) (α γ : ι → ℝ)
    (hG : G.det ≠ 0) (hs : G⁻¹.IsSymm) :
    (((-2*g) • G-r • (vecMulVec α γ+vecMulVec γ α))*G⁻¹).trace =
      -2*((Fintype.card ι : ℝ)*g+r*(α ⬝ᵥ G⁻¹.mulVec γ)) := by
  rw [Matrix.sub_mul,Matrix.smul_mul,Matrix.smul_mul,Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hG),
    Matrix.trace_sub,Matrix.trace_smul,Matrix.trace_smul,Matrix.add_mul,Matrix.trace_add]
  have htr (u v : ι → ℝ) : (vecMulVec u v*G⁻¹).trace = u ⬝ᵥ G⁻¹.mulVec v := by
    rw [Matrix.vecMulVec_mul,Matrix.trace_vecMulVec]
    congr 1
    exact (Matrix.mulVec_transpose G⁻¹ v).symm.trans (congrArg (fun A => A.mulVec v) hs)
  rw [htr,htr]
  have hsym : γ ⬝ᵥ G⁻¹.mulVec α = α ⬝ᵥ G⁻¹.mulVec γ := by
    rw [dotProduct_mulVec,←Matrix.mulVec_transpose,hs,dotProduct_comm]
  rw [hsym]
  simp only [Matrix.trace_one]
  ring

theorem metricSpatialRadialForm_normalized_sqrt_det_hasDerivAt_zero
    (G : Matrix ι ι ℝ) (g r : ℝ) (α γ : ι → ℝ)
    (hG : G.PosDef) :
    HasDerivAt (fun t => Real.sqrt (metricSpatialRadialForm G g r t α γ).det /
      Real.sqrt G.det)
      (-((Fintype.card ι : ℝ)*g+r*(α ⬝ᵥ G⁻¹.mulVec γ))) 0 := by
  have hpos : 0 < G.det := hG.det_pos
  have hz : metricSpatialRadialForm G g r 0 α γ = G := by simp [metricSpatialRadialForm]
  have hd := hasDerivAt_det_at_nonsingular hz hpos.ne'
    (metricSpatialRadialForm_hasDerivAt_zero G g r α γ)
  have hs : G⁻¹.IsSymm := by
    have hi := hG.isHermitian.inv
    exact Matrix.isHermitian_iff_isSymm.mp hi
  rw [trace_radial_matrix_derivative G g r α γ hpos.ne' hs] at hd
  have h := (hd.sqrt (by rw [hz]; exact hpos.ne')).div_const (Real.sqrt G.det)
  apply h.congr_deriv
  rw [hz]
  have hsq := Real.sq_sqrt hpos.le
  have hn : Real.sqrt G.det ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
  field_simp
  rw [hsq]
end CAT0Fillings
end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_SpatialBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma dotProduct_vecMulVec_self (u v : ι → ℝ) :
    v ⬝ᵥ (vecMulVec u u).mulVec v = (u ⬝ᵥ v)^2 := by
  rw [Matrix.vecMulVec_mulVec,dotProduct_smul,op_smul_eq_smul,smul_eq_mul,
    dotProduct_comm v u,pow_two]

end CAT0Fillings

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_MetricBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι] in
lemma metricSpatialRadialForm_rankOne_decomposition
    (G : Matrix ι ι ℝ) (g r t : ℝ) (α γ : ι → ℝ) :
    metricSpatialRadialForm G g r t α γ =
      (1-t*g)^2 • (G-vecMulVec α α) +
        vecMulVec ((1-t*g) • α-(t*r) • γ) ((1-t*g) • α-(t*r) • γ) := by
  ext i j
  simp only [metricSpatialRadialForm,Matrix.add_apply,Matrix.sub_apply,
    Matrix.smul_apply,Matrix.vecMulVec_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring

omit [DecidableEq ι] in
lemma metricSpatialRadialForm_quadratic
    (G : Matrix ι ι ℝ) (g r t : ℝ) (α γ v : ι → ℝ) :
    v ⬝ᵥ (metricSpatialRadialForm G g r t α γ).mulVec v =
      ((1-t*g)*(α ⬝ᵥ v)-t*r*(γ ⬝ᵥ v))^2+
        (1-t*g)^2*(v ⬝ᵥ G.mulVec v-(α ⬝ᵥ v)^2) := by
  rw [metricSpatialRadialForm_rankOne_decomposition,Matrix.add_mulVec,dotProduct_add,
    dotProduct_vecMulVec_self,Matrix.smul_mulVec,dotProduct_smul,Matrix.sub_mulVec,
    dotProduct_sub,dotProduct_vecMulVec_self,sub_dotProduct,smul_dotProduct,smul_dotProduct]
  simp only [smul_eq_mul]
  ring

omit [DecidableEq ι] in
lemma metricSpatialRadialForm_posSemidef
    (G : Matrix ι ι ℝ) (g r t : ℝ) (α γ : ι → ℝ)
    (hG : G.PosSemidef) (hα : ∀ v : ι → ℝ, (α ⬝ᵥ v)^2 ≤ v ⬝ᵥ G.mulVec v) :
    (metricSpatialRadialForm G g r t α γ).PosSemidef := by
  have hQ : (G-vecMulVec α α).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · apply Matrix.IsHermitian.sub hG.isHermitian
      simpa only [star_trivial] using (Matrix.posSemidef_vecMulVec_self_star α).isHermitian
    · intro v
      simp only [star_trivial]
      rw [Matrix.sub_mulVec,dotProduct_sub,dotProduct_vecMulVec_self]
      exact sub_nonneg.mpr (hα v)
  rw [metricSpatialRadialForm_rankOne_decomposition]
  apply Matrix.PosSemidef.add (hQ.smul (sq_nonneg _))
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star
    ((1-t*g) • α-(t*r) • γ)

theorem abs_det_le_metricSpatialRadialJacobian {n : ℕ}
    (L G : Matrix (Fin n) (Fin n) ℝ) (g r t : ℝ) (α γ : Fin n → ℝ)
    (hG : G.PosSemidef)
    (hα : ∀ v : Fin n → ℝ, (α ⬝ᵥ v)^2 ≤ v ⬝ᵥ G.mulVec v)
    (hL : ∀ i v, (L i ⬝ᵥ v)^2 ≤
      ((1-t*g)*(α ⬝ᵥ v)-t*r*(γ ⬝ᵥ v))^2+
        (1-t*g)^2*(v ⬝ᵥ G.mulVec v-(α ⬝ᵥ v)^2)) :
    |L.det| ≤ Real.sqrt (metricSpatialRadialForm G g r t α γ).det := by
  apply abs_det_le_sqrt_det_of_posSemidef L _ (metricSpatialRadialForm_posSemidef G g r t α γ hG hα)
  intro i v
  have hn : 0 ≤ v ⬝ᵥ (metricSpatialRadialForm G g r t α γ).mulVec v := by
    rw [metricSpatialRadialForm_quadratic]
    exact (sq_nonneg _).trans (hL i v)
  apply (Real.le_sqrt (abs_nonneg _) hn).2
  simpa only [sq_abs,metricSpatialRadialForm_quadratic] using hL i v
end CAT0Fillings
end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_ScalarDerivative
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.Foundations.testClass_nonempty _root_.OAI.CAT0Fillings.Foundations.unitTestClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Filter MeasureTheory Set Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {X : Type*} [MetricSpace X]
omit [MeasurableSpace E] [BorelSpace E] in
lemma tendsto_scaled_metric_differential {s : Set E} {x v : E}
    {r : E → ℝ} {p : Seminorm ℝ E}
    (hr : (fun y => r y-p (y-x)) =o[𝓝[s] x] (fun y => y-x))
    {c : ℕ → ℝ} {d : ℕ → E} (hd : ∀ᶠ j in atTop, x+d j ∈ s)
    (hd0 : Tendsto d atTop (𝓝 0))
    (hcd : Tendsto (fun j => c j • d j) atTop (𝓝 v)) :
    Tendsto (fun j => ‖c j‖*r (x+d j)) atTop (𝓝 (p v)) := by
  have ht : Tendsto (fun j => x+d j) atTop (𝓝[s] x) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using tendsto_const_nhds.add hd0,hd⟩
  have hsmall := (hr.comp_tendsto ht).norm_right.mul_isBigO
    (Asymptotics.isBigO_refl (fun j => ‖c j‖) atTop)
  have hnorm : Tendsto (fun j => ‖(x+d j)-x‖*‖c j‖) atTop (𝓝 ‖v‖) := by
    simpa only [norm_smul,add_sub_cancel_left,mul_comm] using hcd.norm
  have hzero := hsmall.tendsto_zero_of_tendsto hnorm
  have hp := (seminorm_continuous_finiteDimensional p).tendsto v |>.comp hcd
  convert hzero.add hp using 1
  · ext j
    simp only [Function.comp_apply,add_sub_cancel_left,map_smul_eq_mul]
    ring
  · simp

theorem radial_scalar_derivative_sq_le
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (seg : X → X → ℝ → X)
    (hcomp : ∀ o x y a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o y b)^2 ≤ (a*dist o x-b*dist o y)^2+
        a*b*(dist x y^2-(dist o x-dist o y)^2))
    {s : Set E} {x : E} (hxs : x ∈ s)
    (hx : Tendsto (fun t => μ (s ∩ closedBall x t) / μ (closedBall x t))
      (𝓝[>] 0) (𝓝 1))
    (f : E → X) (o : X) (p : Seminorm ℝ E)
    (hp : (fun y => dist (f y) (f x)-p (y-x)) =o[𝓝[s] x] (fun y => y-x))
    {lam F : E → ℝ} {α β ℓ : E →L[ℝ] ℝ}
    (hlam : ∀ y ∈ s, lam y ∈ Icc (0:ℝ) 1)
    (hα : HasFDerivWithinAt (fun y => dist o (f y)) α s x)
    (hβ : HasFDerivWithinAt lam β s x)
    (hℓ : HasFDerivWithinAt F ℓ s x)
    {u : X → ℝ} (hu : LipschitzWith 1 u)
    (hF : ∀ y ∈ s, F y = u (seg o (f y) (lam y))) (v : E) :
    (ℓ v)^2 ≤ (lam x*α v+dist o (f x)*β v)^2+
      (lam x)^2*((p v)^2-(α v)^2) := by
  have hv : v ∈ tangentConeAt ℝ s x := by
    rw [tangentConeAt_eq_univ_of_density_one μ s x hx]
    exact mem_univ v
  obtain ⟨c,d,hc,hd,hcd⟩ := mem_tangentConeAt_iff_exists_seq_norm_tendsto_atTop.mp hv
  have hd0 := tangentConeAt.lim_zero atTop hc hcd
  have ht : Tendsto (fun j => x+d j) atTop (𝓝[s] x) :=
    tendsto_nhdsWithin_iff.2 ⟨by simpa using tendsto_const_nhds.add hd0,hd⟩
  have hmetric := tendsto_scaled_metric_differential hp hd hd0 hcd
  have hflim : Tendsto (fun j => c j*(F (x+d j)-F x)) atTop (𝓝 (ℓ v)) := by
    simpa only [smul_eq_mul] using hℓ.lim hd0 hd hcd
  have hrlim : Tendsto (fun j => c j*(dist o (f (x+d j))-dist o (f x)))
      atTop (𝓝 (α v)) := by simpa only [smul_eq_mul] using hα.lim hd0 hd hcd
  have hplim : Tendsto (fun j => c j*(lam (x+d j)*dist o (f (x+d j))-lam x*dist o (f x)))
      atTop (𝓝 (lam x*α v+dist o (f x)*β v)) := by
    simpa only [Pi.mul_apply,smul_eq_mul,_root_.add_apply,_root_.smul_apply]
      using (hβ.mul hα).lim hd0 hd hcd
  have hllim := hβ.continuousWithinAt.tendsto.comp ht
  have hrhs := (hplim.pow 2).add
    ((hllim.mul (tendsto_const_nhds (x := lam x))).mul ((hmetric.pow 2).sub (hrlim.pow 2)))
  apply le_of_tendsto_of_tendsto (hflim.pow 2) (by simpa only [←pow_two] using hrhs)
  filter_upwards [hd] with j hj
  have hb : |F (x+d j)-F x| ≤ dist (seg o (f (x+d j)) (lam (x+d j))) (seg o (f x) (lam x)) := by
    simpa only [Real.dist_eq,NNReal.coe_one,one_mul,←hF (x+d j) hj,←hF x hxs]
      using hu.dist_le_mul (seg o (f (x+d j)) (lam (x+d j))) (seg o (f x) (lam x))
  have hb2 := (sq_le_sq₀ (abs_nonneg _) dist_nonneg).2 hb
  rw [sq_abs] at hb2
  have hh := hb2.trans (hcomp o (f (x+d j)) (f x) (lam (x+d j)) (lam x) (hlam _ hj) (hlam _ hxs))
  have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg (c j))
  convert hmul using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [Function.comp_apply,mul_pow,Real.norm_eq_abs,sq_abs])
  ring

end CAT0Fillings

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_TestBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Filter MeasureTheory Set Metric Matrix
open scoped Topology NNReal BigOperators

theorem radial_test_det_le {n : ℕ} {X : Type*} [MetricSpace X]
    (seg : X → X → ℝ → X)
    (hcomp : ∀ o x y a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o y b)^2 ≤ (a*dist o x-b*dist o y)^2+
        a*b*(dist x y^2-(dist o x-dist o y)^2))
    {s : Set (EuclideanSpace ℝ (Fin n))} {x : EuclideanSpace ℝ (Fin n)}
    (hxs : x ∈ s)
    (hx : Tendsto (fun t => volume (s ∩ closedBall x t) / volume (closedBall x t))
      (𝓝[>] 0) (𝓝 1))
    (f : EuclideanSpace ℝ (Fin n) → X) (o : X)
    (p : Seminorm ℝ (EuclideanSpace ℝ (Fin n)))
    (hp : (fun y => dist (f y) (f x)-p (y-x)) =o[𝓝[s] x] (fun y => y-x))
    (hpos : ∀ v, p v = 0 ↔ v = 0)
    (hpar : ∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (t : ℝ)
    (htg : ∀ y ∈ s, 1-t*g y ∈ Icc (0:ℝ) 1)
    (α γ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hα : HasFDerivWithinAt (fun y => dist o (f y)) α s x)
    (hγ : HasFDerivWithinAt g γ s x)
    (F : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (L : Fin n → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hL : ∀ i, HasFDerivWithinAt (F i) (L i) s x)
    (u : Fin n → X → ℝ) (hu : ∀ i, LipschitzWith 1 (u i))
    (hF : ∀ i y, y ∈ s → F i y = u i (seg o (f y) (1-t*g y))) :
    |(Matrix.of fun i j => differentialRow (L i) j).det| ≤
      Real.sqrt (metricSpatialRadialForm
        (polarizationMatrix p (EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
        (g x) (dist o (f x)) t (differentialRow α) (differentialRow γ)).det := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hG := polarizationMatrix_posDef b p hpos hpar
  have hquadratic (v : Fin n → ℝ) :
      v ⬝ᵥ (polarizationMatrix p b).mulVec v = p (WithLp.toLp 2 v)^2 := by
    have hrepr : b.repr (WithLp.toLp 2 v) = v := by ext j; simp [b]
    simpa only [hrepr] using polarizationMatrix_quadratic b p hpos hpar (WithLp.toLp 2 v)
  have hcontract (v : Fin n → ℝ) :
      (differentialRow α ⬝ᵥ v)^2 ≤ v ⬝ᵥ (polarizationMatrix p b).mulVec v := by
    rw [hquadratic,differentialRow_dot]
    have hr := scalar_derivative_bound_of_metric_differential volume hx hα hp
      (K := 1) (by
        intro y _
        simpa only [one_mul,dist_comm o] using abs_dist_sub_le (f y) (f x) o)
      (WithLp.toLp 2 v)
    have hh := (sq_le_sq₀ (abs_nonneg _) (apply_nonneg p _)).2 (by simpa using hr)
    simpa only [sq_abs] using hh
  apply abs_det_le_metricSpatialRadialJacobian _ _ _ _ _ _ _ hG.posSemidef hcontract
  intro i v
  have hr := radial_scalar_derivative_sq_le volume seg hcomp hxs hx f o p hp htg hα
    ((hγ.const_mul t).const_sub 1) (hL i) (hu i) (hF i) (WithLp.toLp 2 v)
  change (differentialRow (L i) ⬝ᵥ v)^2 ≤ _
  rw [differentialRow_dot,hquadratic,differentialRow_dot,differentialRow_dot]
  convert hr using 1
  all_goals try with_reducible_and_instances rfl
  simp only [_root_.neg_apply,_root_.smul_apply,smul_eq_mul]
  ring

end CAT0Fillings
end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_ChartMass
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open MeasureTheory Set Filter Metric Matrix CurrentOperations
open scoped Topology NNReal

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [Nonempty X] {k : ℕ} (C : IntegerChart X k)

omit [MeasurableSpace X] [BorelSpace X] in
theorem ae_radial_jacobian_bound
    (seg : X → X → ℝ → X)
    (hcomp : ∀ o x y a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o y b)^2 ≤ (a*dist o x-b*dist o y)^2+
        a*b*(dist x y^2-(dist o x-dist o y)^2))
    (o : X) (g : X → ℝ) {Kg Kf : ℝ≥0} (hg : LipschitzWith Kg g)
    (t : ℝ) (htg : ∀ y, 1-t*g y ∈ Icc (0:ℝ) 1)
    (hf : LipschitzWith Kf (fun y => seg o y (1-t*g y)))
    (p : Euc k → Seminorm ℝ (Euc k))
    (hp : ∀ᵐ z ∂volume.restrict C.domain,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
      (∀ v, p z v = 0 ↔ v = 0))
    (π : Fin k → X → ℝ) (hπ : ∀ i, LipschitzWith 1 (π i)) :
    ∀ᵐ z ∂volume.restrict C.domain,
      |C.jacobian (fun i y => π i (seg o y (1-t*g y))) z| ≤
        C.radialJacobian
          (fun z => polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
          o g t z := by
  have htests : ∀ᵐ z ∂volume.restrict C.domain, ∀ i,
      DifferentiableWithinAt ℝ (C.scalar (fun y => π i (seg o y (1-t*g y))))
        C.domain z := ae_all_iff.mpr fun i =>
    C.ae_differentiableWithinAt_scalar ((hπ i).comp hf)
  filter_upwards [hp,ae_restrict_mem C.borel,
    Besicovitch.ae_tendsto_measure_inter_div volume C.domain,
    C.ae_differentiableWithinAt_scalar (LipschitzWith.dist_right o),
    C.ae_differentiableWithinAt_scalar hg,htests] with z hpz hzs hden hr hgz htests
  have hpe : (fun y => dist (C.paramExtended y) (C.paramExtended z)-p z (y-z))
      =o[𝓝[C.domain] z] (fun y => y-z) := by
    rw [nhdsWithin_eq_map_subtype_coe hzs,Asymptotics.isLittleO_map]
    have hh := hpz.1 hzs
    change (fun y : C.domain => dist (C.param y) (C.param ⟨z,hzs⟩)-
      p z ((y : Euc k)-z)) =o[𝓝 (⟨z,hzs⟩ : C.domain)]
      (fun y : C.domain => (y : Euc k)-z) at hh
    convert hh using 1
    · ext y
      simp only [Function.comp_apply,paramExtended,dite_eq_left y.property,dite_eq_left hzs,
        Subtype.coe_eta]
    · rfl
  have heq (b : X → ℝ) : EqOn (fun y => b (C.paramExtended y)) (C.scalar b) C.domain := by
    intro y hy
    simp only [paramExtended,scalar,dite_eq_left hy]
  have hR := hr.hasFDerivWithinAt.congr (heq (dist o)) (heq (dist o) hzs)
  have hG := hgz.hasFDerivWithinAt.congr (heq g) (heq g hzs)
  have hh := radial_test_det_le seg hcomp hzs hden C.paramExtended o (p z) hpe
    hpz.2.2 hpz.2.1 (fun y => g (C.paramExtended y)) t (fun y _ => htg _)
    (fderivWithin ℝ (C.scalar (dist o)) C.domain z)
    (fderivWithin ℝ (C.scalar g) C.domain z) hR hG
    (fun i => C.scalar (fun y => π i (seg o y (1-t*g y))))
    (fun i => fderivWithin ℝ (C.scalar (fun y => π i (seg o y (1-t*g y)))) C.domain z)
    (fun i => (htests i).hasFDerivWithinAt) π hπ (by
      intro i y hy
      simp only [paramExtended,scalar,dite_eq_left hy])
  convert hh using 1
  · congr 2
  · simp only [radialJacobian,←heq g hzs,←heq (dist o) hzs]

theorem radial_push_mass_le
    (seg : X → X → ℝ → X)
    (hcomp : ∀ o x y a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o y b)^2 ≤ (a*dist o x-b*dist o y)^2+
        a*b*(dist x y^2-(dist o x-dist o y)^2))
    (o : X) (g : X → ℝ) {Kg Kf : ℝ≥0} (hg : LipschitzWith Kg g)
    (t : ℝ) (htg : ∀ y, 1-t*g y ∈ Icc (0:ℝ) 1)
    (hf : LipschitzWith Kf (fun y => seg o y (1-t*g y)))
    (p : Euc k → Seminorm ℝ (Euc k))
    (hp : ∀ᵐ z ∂volume.restrict C.domain,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
      (∀ v, p z v = 0 ↔ v = 0))
    (hρ : Integrable (fun z => |(C.multiplicity z : ℝ)| *
      C.radialJacobian
        (fun z => polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
        o g t z) (volume.restrict C.domain)) :
    mass (pushCurrent (fun y => seg o y (1-t*g y)) C.action) ≤
      ∫ z, |(C.multiplicity z : ℝ)| *
        C.radialJacobian
          (fun z => polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
          o g t z ∂volume.restrict C.domain := by
  apply C.push_mass_le_majorant hf hρ
    (Eventually.of_forall fun _ => Real.sqrt_nonneg _)
  intro π hπ
  exact C.ae_radial_jacobian_bound seg hcomp o g hg t htg hf p hp π hπ
end IntegerChart
end CAT0Fillings

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_UniformSlope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set Metric Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma abs_sqrt_sub_one_le (a : ℝ) : |Real.sqrt a-1| ≤ |a-1| := by
  by_cases ha : 0 ≤ a
  · have hs := Real.sq_sqrt ha
    have hn := Real.sqrt_nonneg a
    by_cases h : 1 ≤ Real.sqrt a
    · rw [abs_of_nonneg (sub_nonneg.mpr h),abs_of_nonneg (by nlinarith : 0 ≤ a-1)]
      nlinarith
    · have h' : Real.sqrt a ≤ 1 := le_of_not_ge h
      rw [abs_of_nonpos (sub_nonpos.mpr h'),abs_of_nonpos (by nlinarith : a-1 ≤ 0)]
      nlinarith [sq_nonneg (Real.sqrt a-1)]
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge ha)]
    rw [abs_of_nonpos (by norm_num : (0:ℝ)-1 ≤ 0),
      abs_of_nonpos (by linarith : a-1 ≤ 0)]
    linarith

omit [Fintype ι] in
lemma continuous_spatialRadialSlope :
    Continuous (fun q : ℝ × RadialParameters ι => spatialRadialSlope q.1 q.2) := by
  unfold spatialRadialSlope
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fun_prop

omit [Fintype ι] in
lemma spatialRadialForm_sub_identity (t : ℝ) (p : RadialParameters ι) :
    spatialRadialForm p.1.1 p.1.2 t p.2.1 p.2.2 - 1 = t • spatialRadialSlope t p := by
  ext i j
  simp only [spatialRadialForm,spatialRadialSlope,Matrix.sub_apply,Matrix.one_apply,
    Matrix.smul_apply,Matrix.of_apply,smul_eq_mul]
  split_ifs <;> ring

theorem spatialRadialForm_uniform_slope_bound (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : RadialParameters ι, ‖p‖ ≤ B →
      ∀ t ∈ Icc (0:ℝ) 1,
        |Real.sqrt (spatialRadialForm p.1.1 p.1.2 t p.2.1 p.2.2).det-1| ≤ C*t := by
  let K : Set (ℝ × RadialParameters ι) := Icc (0:ℝ) 1 ×ˢ closedBall 0 B
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall 0 B)
  obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn
    (f := fun q : ℝ × RadialParameters ι => (fun i j => spatialRadialSlope q.1 q.2 i j))
    continuous_spatialRadialSlope.continuousOn
  let R : ℝ := max D 0
  have hR : 0 ≤ R := le_max_right _ _
  let detM : ContinuousMultilinearMap ℝ (fun _ : ι => ι → ℝ) ℝ :=
    ⟨Matrix.detRowAlternating.toMultilinearMap,continuous_id.matrix_det⟩
  let C := ‖detM‖*(Fintype.card ι : ℝ)*(R+1)^(Fintype.card ι-1)*R
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro p hp t ht
  have hQ : ‖spatialRadialSlope t p‖ ≤ R :=
    (hD (t,p) ⟨ht,by simpa only [mem_closedBall,dist_zero_right] using hp⟩).trans (le_max_left _ _)
  let A := spatialRadialForm p.1.1 p.1.2 t p.2.1 p.2.2
  have hdiff : ‖A-1‖ ≤ R*t := by
    rw [show A-1 = t • spatialRadialSlope t p from spatialRadialForm_sub_identity t p,
      norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hQ ht.1
  have hId : ‖(1 : Matrix ι ι ℝ)‖ ≤ 1 := by
    apply (Matrix.norm_le_iff zero_le_one).2
    intro i j
    simp only [Matrix.one_apply]
    split_ifs <;> norm_num
  have hA : ‖A‖ ≤ R+1 := by
    have hh := norm_add_le (A-1) (1 : Matrix ι ι ℝ)
    rw [sub_add_cancel] at hh
    have hRt : R*t ≤ R := (mul_le_mul_of_nonneg_left ht.2 hR).trans_eq (mul_one R)
    linarith
  have hmax : max ‖A‖ ‖(1 : Matrix ι ι ℝ)‖ ≤ R+1 := max_le hA (by linarith)
  have hh := detM.norm_image_sub_le (fun i j => A i j) (fun i j => (1 : Matrix ι ι ℝ) i j)
  change ‖A.det-(1 : Matrix ι ι ℝ).det‖ ≤
    ‖detM‖*(Fintype.card ι : ℝ)*max ‖A‖ ‖(1 : Matrix ι ι ℝ)‖^(Fintype.card ι-1)*‖A-1‖ at hh
  rw [Matrix.det_one,Real.norm_eq_abs] at hh
  calc
    _ ≤ |A.det-1| := abs_sqrt_sub_one_le A.det
    _ ≤ ‖detM‖*(Fintype.card ι : ℝ)*max ‖A‖ ‖(1 : Matrix ι ι ℝ)‖^(Fintype.card ι-1)*‖A-1‖ := hh
    _ ≤ ‖detM‖*(Fintype.card ι : ℝ)*(R+1)^(Fintype.card ι-1)*(R*t) := by gcongr
    _ = C*t := by dsimp [C]; ring

end CAT0Fillings

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_IntrinsicSlope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Matrix Set Metric
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
lemma metricSpatialRadialForm_congruence (G Q : Matrix ι ι ℝ)
    (hQ : Q.transpose = Q) (hi : IsUnit Q.det) (hG : G = Q*Q)
    (g r t : ℝ) (α γ : ι → ℝ) :
    Q⁻¹ * metricSpatialRadialForm G g r t α γ * Q⁻¹ =
      spatialRadialForm g r t (Q⁻¹.mulVec α) (Q⁻¹.mulVec γ) := by
  have hs : (Q⁻¹).transpose = Q⁻¹ := by rw [Matrix.transpose_nonsing_inv,hQ]
  have h0 : Q⁻¹*G*Q⁻¹ = 1 := by
    rw [hG,←mul_assoc,Matrix.nonsing_inv_mul Q hi,one_mul,Matrix.mul_nonsing_inv Q hi]
  have ho (a b : ι → ℝ) : Q⁻¹*vecMulVec a b*Q⁻¹ =
      vecMulVec (Q⁻¹.mulVec a) (Q⁻¹.mulVec b) := by
    rw [Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,←Matrix.mulVec_transpose,hs]
  have he : spatialRadialForm g r t (Q⁻¹.mulVec α) (Q⁻¹.mulVec γ) =
      (1-t*g)^2 • (1 : Matrix ι ι ℝ)-((1-t*g)*t*r) •
        (vecMulVec (Q⁻¹.mulVec α) (Q⁻¹.mulVec γ)+
          vecMulVec (Q⁻¹.mulVec γ) (Q⁻¹.mulVec α))+
        (t^2*r^2) • vecMulVec (Q⁻¹.mulVec γ) (Q⁻¹.mulVec γ) := by
    ext i j
    simp only [spatialRadialForm,Matrix.of_apply,Matrix.add_apply,Matrix.sub_apply,
      Matrix.smul_apply,Matrix.one_apply,Matrix.vecMulVec_apply,smul_eq_mul]
    ring
  rw [he,metricSpatialRadialForm]
  simp only [mul_add,mul_sub,add_mul,sub_mul,Matrix.mul_smul,Matrix.smul_mul,ho,h0]

lemma metricSpatialRadialForm_normalized_by_sqrt (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (g r t : ℝ) (α γ : ι → ℝ) :
    Real.sqrt (metricSpatialRadialForm G g r t α γ).det / Real.sqrt G.det =
      Real.sqrt (spatialRadialForm g r t ((CFC.sqrt G)⁻¹.mulVec α)
        ((CFC.sqrt G)⁻¹.mulVec γ)).det := by
  let Q := CFC.sqrt G
  have hs : Q.transpose = Q :=
    (Matrix.isHermitian_iff_isSymm.mp (CFC.sqrt_nonneg G).posSemidef.isHermitian).eq
  have hQ : Q.det = Real.sqrt G.det := by
    simpa only [RCLike.sqrt_real] using hG.posSemidef.det_sqrt
  have hi : IsUnit Q.det := isUnit_iff_ne_zero.mpr (by rw [hQ]; exact (Real.sqrt_pos.2 hG.det_pos).ne')
  have hh := congrArg Matrix.det (metricSpatialRadialForm_congruence G Q hs hi
    (by simpa only [pow_two] using (CFC.sq_sqrt G hG.posSemidef.nonneg).symm) g r t α γ)
  simp only [Matrix.det_mul,Matrix.det_nonsing_inv,Ring.inverse_eq_inv] at hh
  have hn : Real.sqrt G.det ≠ 0 := (Real.sqrt_pos.2 hG.det_pos).ne'
  have he : (spatialRadialForm g r t (Q⁻¹.mulVec α) (Q⁻¹.mulVec γ)).det =
      (metricSpatialRadialForm G g r t α γ).det / G.det := by
    rw [←hh,hQ]
    calc
      _ = (metricSpatialRadialForm G g r t α γ).det / (Real.sqrt G.det)^2 := by
        field_simp
      _ = _ := by rw [Real.sq_sqrt hG.det_pos.le]
  change _ = Real.sqrt (spatialRadialForm g r t (Q⁻¹.mulVec α) (Q⁻¹.mulVec γ)).det
  rw [he,Real.sqrt_div' _ hG.det_pos.le]

lemma inverse_sqrt_mulVec_norm_le (G : Matrix ι ι ℝ) (hG : G.PosDef)
    (a : ι → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (ha : ∀ v : ι → ℝ, (a ⬝ᵥ v)^2 ≤ K^2*(v ⬝ᵥ G.mulVec v)) :
    ‖(CFC.sqrt G)⁻¹.mulVec a‖ ≤ K := by
  let Q := CFC.sqrt G
  have hs : Q.transpose = Q :=
    (Matrix.isHermitian_iff_isSymm.mp (CFC.sqrt_nonneg G).posSemidef.isHermitian).eq
  have hsi : (Q⁻¹).transpose = Q⁻¹ := by rw [Matrix.transpose_nonsing_inv,hs]
  have hQ : Q.det = Real.sqrt G.det := by
    simpa only [RCLike.sqrt_real] using hG.posSemidef.det_sqrt
  have hi : IsUnit Q.det := isUnit_iff_ne_zero.mpr (by rw [hQ]; exact (Real.sqrt_pos.2 hG.det_pos).ne')
  have hv (v : ι → ℝ) : (Q⁻¹.mulVec v) ⬝ᵥ G.mulVec (Q⁻¹.mulVec v) = v ⬝ᵥ v := by
    have hGQ : G = Q*Q := by
      simpa only [pow_two] using (CFC.sq_sqrt G hG.posSemidef.nonneg).symm
    rw [hGQ,←Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,←Matrix.mulVec_transpose,hs,
      Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv Q hi,Matrix.one_mulVec]
  apply (pi_norm_le_iff_of_nonneg hK).2
  intro j
  have hh := ha (Q⁻¹.mulVec (Pi.single j 1))
  rw [hv] at hh
  have he : a ⬝ᵥ Q⁻¹.mulVec (Pi.single j 1) = Q⁻¹.mulVec a j := by
    rw [Matrix.dotProduct_mulVec,←Matrix.mulVec_transpose,hsi]
    simp
  rw [he] at hh
  have he' : (Pi.single j (1:ℝ)) ⬝ᵥ Pi.single j 1 = 1 := by simp
  rw [he',mul_one] at hh
  exact (sq_le_sq₀ (norm_nonneg _) hK).1 (by simpa only [Real.norm_eq_abs,sq_abs] using hh)

theorem metricSpatialRadialForm_intrinsic_uniform_slope_bound (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : Matrix ι ι ℝ), G.PosDef →
      ∀ g r : ℝ, |g| ≤ B → |r| ≤ B → ∀ α γ : ι → ℝ,
      (∀ v : ι → ℝ, (α ⬝ᵥ v)^2 ≤ B^2*(v ⬝ᵥ G.mulVec v)) →
      (∀ v : ι → ℝ, (γ ⬝ᵥ v)^2 ≤ B^2*(v ⬝ᵥ G.mulVec v)) →
      ∀ t ∈ Icc (0:ℝ) 1,
      |Real.sqrt (metricSpatialRadialForm G g r t α γ).det / Real.sqrt G.det-1| ≤ C*t := by
  obtain ⟨C,hC,hbound⟩ := spatialRadialForm_uniform_slope_bound (ι := ι) B
  refine ⟨C,hC,?_⟩
  intro G hG g r hg hr α γ hα hγ t ht
  rw [metricSpatialRadialForm_normalized_by_sqrt G hG]
  apply hbound ⟨⟨g,r⟩,⟨_,_⟩⟩ _ t ht
  simp only [Prod.norm_def,Real.norm_eq_abs,max_le_iff]
  exact ⟨⟨hg,hr⟩,inverse_sqrt_mulVec_norm_le G hG α B hB hα,
    inverse_sqrt_mulVec_norm_le G hG γ B hB hγ⟩

end CAT0Fillings
end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_MeasurableBound
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings.IntegerChart
open MeasureTheory Set Filter Metric Matrix
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [Nonempty X] {k : ℕ} (C : IntegerChart X k)
omit [MeasurableSpace X] [BorelSpace X] [Nonempty X] in
lemma aestronglyMeasurable_radialJacobian
    (P : Euc k → Matrix (Fin k) (Fin k) ℝ)
    (hP : ∀ i j, Measurable (fun z => P z i j))
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) (t : ℝ) :
    AEStronglyMeasurable (C.radialJacobian P o g t) (volume.restrict C.domain) := by
  obtain ⟨L,U,hL,_⟩ := C.bilipschitz
  obtain ⟨R,hR,heR⟩ := (C.scalar_lipschitzOn hL (LipschitzWith.dist_right o)).extend_real
  obtain ⟨G,hG,heG⟩ := (C.scalar_lipschitzOn hL hg).extend_real
  have hrm := C.measurable_scalar (LipschitzWith.dist_right o)
  have hgm := C.measurable_scalar hg
  let J : Euc k → ℝ := fun z => Real.sqrt (metricSpatialRadialForm (P z)
    (C.scalar g z) (C.scalar (dist o) z) t
    (differentialRow (fderiv ℝ R z)) (differentialRow (fderiv ℝ G z))).det
  have hRd (i : Fin k) : Measurable (fun z => differentialRow (fderiv ℝ R z) i) := by
    simp only [differentialRow]
    fun_prop
  have hGd (i : Fin k) : Measurable (fun z => differentialRow (fderiv ℝ G z) i) := by
    simp only [differentialRow]
    fun_prop
  have hEntry (i j : Fin k) : Measurable (fun z => (metricSpatialRadialForm (P z)
      (C.scalar g z) (C.scalar (dist o) z) t
      (differentialRow (fderiv ℝ R z)) (differentialRow (fderiv ℝ G z))) i j) := by
    change Measurable (fun z =>
      (1-t*C.scalar g z)^2*(P z i j)-
      ((1-t*C.scalar g z)*t*C.scalar (dist o) z)*
        (differentialRow (fderiv ℝ R z) i*differentialRow (fderiv ℝ G z) j+
         differentialRow (fderiv ℝ G z) i*differentialRow (fderiv ℝ R z) j)+
      (t^2*C.scalar (dist o) z^2)*
        (differentialRow (fderiv ℝ G z) i*differentialRow (fderiv ℝ G z) j))
    exact (((measurable_const.sub (hgm.const_mul t)).pow_const 2).mul (hP i j) |>.sub
      ((((measurable_const.sub (hgm.const_mul t)).mul_const t).mul hrm).mul
        (((hRd i).mul (hGd j)).add ((hGd i).mul (hRd j))))).add
      (((hrm.pow_const 2).const_mul (t^2)).mul ((hGd i).mul (hGd j)))
  have hJ : Measurable J := by
    dsimp [J]
    apply Measurable.sqrt
    simp only [Matrix.det_apply']
    apply Finset.measurable_sum
    intro σ _
    apply Measurable.const_mul
    exact Finset.measurable_prod Finset.univ (fun i _ => hEntry (σ i) i)
  apply hJ.aestronglyMeasurable.congr
  filter_upwards [ae_fderivWithin_eq_fderiv_extension volume C.borel hR heR,
    ae_fderivWithin_eq_fderiv_extension volume C.borel hG heG] with z hRz hGz
  simp only [J,radialJacobian,hRz,hGz]

omit [MeasurableSpace X] [BorelSpace X] [Nonempty X] in
lemma ae_scalar_row_quadratic_bound
    (p : Euc k → Seminorm ℝ (Euc k))
    (hp : ∀ᵐ z ∂volume.restrict C.domain,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
      (∀ v, p z v = 0 ↔ v = 0))
    {u : X → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    ∀ᵐ z ∂volume.restrict C.domain, ∀ v : Fin k → ℝ,
      (differentialRow (fderivWithin ℝ (C.scalar u) C.domain z) ⬝ᵥ v)^2 ≤
        (K:ℝ)^2*(v ⬝ᵥ (polarizationMatrix (p z)
          (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).mulVec v) := by
  obtain ⟨L,U,hL,_⟩ := C.bilipschitz
  have hrow : ∀ᵐ z ∂volume.restrict C.domain, ∀ v,
      |fderivWithin ℝ (C.scalar u) C.domain z v| ≤ K*p z v :=
    MetricDifferentiation.ae_scalarOn_derivative_bound volume C.borel hL
      (hp.mono fun z hz => hz.1) hu
  filter_upwards [hp,hrow] with z hpz hrowz v
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  have hrepr : b.repr (WithLp.toLp 2 v) = v := by ext j; simp [b]
  have hquad : v ⬝ᵥ (polarizationMatrix (p z) b).mulVec v = p z (WithLp.toLp 2 v)^2 := by
    simpa only [hrepr] using
      polarizationMatrix_quadratic b (p z) hpz.2.2 hpz.2.1 (WithLp.toLp 2 v)
  rw [differentialRow_dot,hquad]
  have hh := (sq_le_sq₀ (abs_nonneg _)
    (mul_nonneg K.coe_nonneg (apply_nonneg (p z) _))).2 (hrowz (WithLp.toLp 2 v))
  simpa only [sq_abs,mul_pow] using hh

omit [MeasurableSpace X] [BorelSpace X] [Nonempty X] in
theorem radialJacobian_le_intrinsic_majorant
    (p : Euc k → Seminorm ℝ (Euc k))
    (hp : ∀ᵐ z ∂volume.restrict C.domain,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
      (∀ v, p z v = 0 ↔ v = 0))
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {B : ℝ} (hB : 1 ≤ B) (hK : (K:ℝ) ≤ B)
    (hgb : ∀ x, |g x| ≤ B) (hrb : ∀ x, dist o x ≤ B) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ t ∈ Icc (0:ℝ) 1,
      ∀ᵐ z ∂volume.restrict C.domain,
        C.radialJacobian
          (fun z => polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
          o g t z ≤ A*Real.sqrt (polarizationMatrix (p z)
            (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det := by
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  obtain ⟨A,hA,hbound⟩ := metricSpatialRadialForm_intrinsic_uniform_slope_bound (ι := Fin k) B hB0
  refine ⟨A+1,by linarith,?_⟩
  intro t ht
  filter_upwards [hp,ae_restrict_mem C.borel,
    C.ae_scalar_row_quadratic_bound p hp (LipschitzWith.dist_right o),
    C.ae_scalar_row_quadratic_bound p hp hg] with z hpz hzs hR hG
  let P := polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  have hP : P.PosDef := polarizationMatrix_posDef _ _ hpz.2.2 hpz.2.1
  have hPr (v : Fin k → ℝ) : 0 ≤ v ⬝ᵥ P.mulVec v := hP.posSemidef.dotProduct_mulVec_nonneg v
  have hα : ∀ v : Fin k → ℝ,
      (differentialRow (fderivWithin ℝ (C.scalar (dist o)) C.domain z) ⬝ᵥ v)^2 ≤
        B^2*(v ⬝ᵥ P.mulVec v) := by
    intro v
    have hh := hR v
    simp only [NNReal.coe_one,one_pow,one_mul] at hh
    exact hh.trans (le_mul_of_one_le_left (hPr v) (by nlinarith))
  have hγ : ∀ v : Fin k → ℝ,
      (differentialRow (fderivWithin ℝ (C.scalar g) C.domain z) ⬝ᵥ v)^2 ≤
        B^2*(v ⬝ᵥ P.mulVec v) := by
    intro v
    exact (hG v).trans (mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ K.coe_nonneg hB0).2 hK) (hPr v))
  have hh := hbound P hP (C.scalar g z) (C.scalar (dist o) z)
    (by simpa only [C.scalar_eq hzs] using hgb (C.param ⟨z,hzs⟩))
    (by simpa only [C.scalar_eq hzs,abs_of_nonneg dist_nonneg] using hrb (C.param ⟨z,hzs⟩))
    _ _ hα hγ t ht
  have hpos : 0 < Real.sqrt P.det := Real.sqrt_pos.2 hP.det_pos
  apply (div_le_iff₀ hpos).1
  change C.radialJacobian _ o g t z / Real.sqrt P.det ≤ A+1
  have hAt : A*t ≤ A := (mul_le_mul_of_nonneg_left ht.2 hA).trans_eq (mul_one A)
  change |C.radialJacobian (fun z => polarizationMatrix (p z)
    (EuclideanSpace.basisFun (Fin k) ℝ).toBasis) o g t z / Real.sqrt P.det-1| ≤ A*t at hh
  have hs := (le_abs_self _).trans hh
  linarith

end CAT0Fillings.IntegerChart
end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_Integrability
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings.IntegerChart
open MeasureTheory Set Filter Metric Matrix
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [Nonempty X] {k : ℕ} (C : IntegerChart X k)
omit [MeasurableSpace X] [BorelSpace X] [Nonempty X] in
theorem integrable_radialJacobian
    (p : Euc k → Seminorm ℝ (Euc k)) (hpm : ∀ v, Measurable (fun z => p z v))
    (hp : ∀ᵐ z ∂volume.restrict C.domain,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
      (∀ v, p z v = 0 ↔ v = 0))
    (hρ : Integrable (fun z => |(C.multiplicity z : ℝ)| *Real.sqrt
      (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det)
      (volume.restrict C.domain))
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {B : ℝ} (hB : 1 ≤ B) (hK : (K:ℝ) ≤ B)
    (hgb : ∀ x, |g x| ≤ B) (hrb : ∀ x, dist o x ≤ B)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    Integrable (fun z => |(C.multiplicity z : ℝ)| *
      C.radialJacobian
        (fun z => polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
        o g t z) (volume.restrict C.domain) := by
  obtain ⟨A,hA,hbound⟩ := C.radialJacobian_le_intrinsic_majorant p hp o hg hB hK hgb hrb
  have hmeas := C.aestronglyMeasurable_radialJacobian
    (fun z => polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
    (measurable_polarizationMatrix p (EuclideanSpace.basisFun (Fin k) ℝ).toBasis hpm) o hg t
  apply (hρ.const_mul A).mono' (C.integrable.abs.aestronglyMeasurable.mul hmeas)
  filter_upwards [hbound t ht] with z hz
  rw [Real.norm_eq_abs,Pi.mul_apply,abs_mul,abs_abs]
  rw [abs_of_nonneg (show 0 ≤ C.radialJacobian _ o g t z from Real.sqrt_nonneg _)]
  calc
    _ ≤ |(C.multiplicity z : ℝ)| * (A * Real.sqrt
      (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det) :=
        mul_le_mul_of_nonneg_left hz (abs_nonneg _)
    _ = _ := by ring
end CAT0Fillings.IntegerChart
namespace CAT0Fillings
open Set Metric
open scoped NNReal

variable {E X : Type*} [MetricSpace E] [MetricSpace X]

theorem radial_lipschitzOnWith
    (seg : X → X → ℝ → X)
    (hseg : ∀ o x a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o x b) = |a-b| *dist o x)
    (hcomp : ∀ o x y a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o y b)^2 ≤ (a*dist o x-b*dist o y)^2+
        a*b*(dist x y^2-(dist o x-dist o y)^2))
    {s : Set E} {f : E → X} {lam : E → ℝ} {K L R : ℝ≥0}
    (hf : LipschitzOnWith K f s) (hl : LipschitzOnWith L lam s)
    (hla : ∀ x ∈ s, lam x ∈ Icc (0:ℝ) 1)
    (o : X) (hR : ∀ x ∈ s, dist o (f x) ≤ R) :
    LipschitzOnWith (K+R*L) (fun x => seg o (f x) (lam x)) s := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  have hsame : dist (seg o (f x) (lam x)) (seg o (f y) (lam x)) ≤
      lam x*dist (f x) (f y) := by
    apply (sq_le_sq₀ dist_nonneg (mul_nonneg (hla _ hx).1 dist_nonneg)).mp
    calc
      _ ≤ (lam x*dist o (f x)-lam x*dist o (f y))^2+
        lam x*lam x*(dist (f x) (f y)^2-(dist o (f x)-dist o (f y))^2) :=
          hcomp o (f x) (f y) (lam x) (lam x) (hla _ hx) (hla _ hx)
      _ = _ := by ring
  have hlxy : |lam x-lam y| ≤ (L:ℝ)*dist x y := by
    simpa only [Real.dist_eq] using hl.dist_le_mul x hx y hy
  calc
    _ ≤ dist (seg o (f x) (lam x)) (seg o (f y) (lam x))+
        dist (seg o (f y) (lam x)) (seg o (f y) (lam y)) := dist_triangle _ _ _
    _ ≤ lam x*dist (f x) (f y)+|lam x-lam y| *dist o (f y) := by
      rw [hseg o (f y) (lam x) (lam y) (hla _ hx) (hla _ hy)]
      exact add_le_add hsame le_rfl
    _ ≤ dist (f x) (f y)+|lam x-lam y| *(R:ℝ) :=
      add_le_add (mul_le_of_le_one_left dist_nonneg (hla _ hx).2)
        (mul_le_mul_of_nonneg_left (hR _ hy) (abs_nonneg _))
    _ ≤ (K:ℝ)*dist x y+((L:ℝ)*dist x y)*(R:ℝ) :=
      add_le_add (hf.dist_le_mul x hx y hy) (mul_le_mul_of_nonneg_right hlxy R.coe_nonneg)
    _ = _ := by push_cast; ring

end CAT0Fillings
namespace CAT0Fillings
open Set Metric
open scoped NNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X]

theorem radial_lipschitzWith
    (seg : X → X → ℝ → X)
    (hseg : ∀ o x a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o x b) = |a-b| *dist o x)
    (hcomp : ∀ o x y a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o y b)^2 ≤ (a*dist o x-b*dist o y)^2+
        a*b*(dist x y^2-(dist o x-dist o y)^2))
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    (t : ℝ) (htg : ∀ y, 1-t*g y ∈ Icc (0:ℝ) 1) :
    ∃ L : ℝ≥0, LipschitzWith L (fun y => seg o y (1-t*g y)) := by
  let R : ℝ≥0 := ⟨Metric.diam (univ : Set X),Metric.diam_nonneg⟩
  have hR : ∀ x : X, dist o x ≤ R := fun x =>
    Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ o) (mem_univ x)
  have hfrac : LipschitzWith (‖t‖₊*K) (fun x => 1-t*g x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, show 1-t*g x-(1-t*g y) = -(t*(g x-g y)) by ring,
      abs_neg,abs_mul]
    have hh := mul_le_mul_of_nonneg_left (hg.dist_le_mul x y) (abs_nonneg t)
    simpa only [NNReal.coe_mul,coe_nnnorm,Real.norm_eq_abs,Real.dist_eq,mul_assoc] using hh
  refine ⟨1+R*(‖t‖₊*K),?_⟩
  rw [←lipschitzOnWith_univ]
  exact radial_lipschitzOnWith seg hseg hcomp
    (LipschitzWith.id.lipschitzOnWith) hfrac.lipschitzOnWith (fun x _ => htg x) o
    (fun x _ => hR x)
end CAT0Fillings
end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_TotalForm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CAT0Fillings
open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma totalRankOneForm_det (H : Matrix ι ι ℝ) (c : ℝ) (u : ι → ℝ) :
    (totalRankOneForm H c u).det = c^2*H.det := by
  let E : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℝ :=
    fromBlocks (Matrix.of fun _ _ => c) 0 (replicateCol Unit u) 1
  let D : Matrix (Unit ⊕ ι) (Unit ⊕ ι) ℝ := fromBlocks 1 0 0 H
  have he : totalRankOneForm H c u = E*D*E.transpose := by
    dsimp [E,D]
    rw [Matrix.fromBlocks_transpose,Matrix.fromBlocks_multiply,Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_one,Matrix.one_mul,Matrix.mul_zero,Matrix.zero_mul,
      add_zero,zero_add,Matrix.transpose_zero,Matrix.transpose_one]
    ext i j
    cases i <;> cases j <;>
      simp [totalRankOneForm,Matrix.mul_apply,Matrix.vecMulVec_apply,
        Matrix.replicateCol,Matrix.transpose_apply, mul_comm,add_comm]
  have hd : D.det = H.det := by simp [D,Matrix.det_fromBlocks_zero₂₁]
  have hE : E.det = c := by simp [E,Matrix.det_unique]
  rw [he,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,hE,hd]
  ring

lemma det_sub_vecMulVec (G : Matrix ι ι ℝ) (α : ι → ℝ) (hG : G.det ≠ 0) :
    (G-vecMulVec α α).det = G.det*(1-α ⬝ᵥ G⁻¹.mulVec α) := by
  have he : G-vecMulVec α α =
      G+replicateCol Unit (-α)*replicateRow Unit α := by
    ext i j
    simp [Matrix.mul_apply,Matrix.vecMulVec_apply,Matrix.replicateCol,Matrix.replicateRow,
      sub_eq_add_neg]
  rw [he,Matrix.det_add_replicateCol_mul_replicateRow (isUnit_iff_ne_zero.mpr hG)]
  congr 1
  rw [Matrix.det_unique]
  simp only [Matrix.add_apply,Matrix.one_apply_eq,Matrix.mul_apply,
    Matrix.replicateRow_apply,Matrix.replicateCol_apply,Pi.neg_apply]
  simp only [Finset.sum_neg_distrib,mul_neg]
  simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [sub_eq_add_neg,mul_assoc]

omit [DecidableEq ι] in

lemma totalRankOneForm_quadratic (H : Matrix ι ι ℝ) (c : ℝ) (u : ι → ℝ)
    (v : Unit ⊕ ι → ℝ) :
    v ⬝ᵥ (totalRankOneForm H c u).mulVec v =
      (c*v (Sum.inl ()) + u ⬝ᵥ (v ∘ Sum.inr))^2 +
        (v ∘ Sum.inr) ⬝ᵥ H.mulVec (v ∘ Sum.inr) := by
  rw [totalRankOneForm,Matrix.add_mulVec,dotProduct_add,Matrix.vecMulVec_mulVec,
    dotProduct_smul,op_smul_eq_smul,smul_eq_mul,dotProduct_comm v]
  rw [Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec,zero_add,add_zero]
  have hsplit : v = Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) := by ext x; cases x <;> rfl
  conv_lhs => rw [hsplit]
  simp only [sumElim_dotProduct_sumElim]
  simp [dotProduct,Function.comp_def,pow_two,mul_comm,add_comm]

omit [DecidableEq ι] in

lemma totalRankOneForm_posSemidef (H : Matrix ι ι ℝ) (c : ℝ) (u : ι → ℝ)
    (hH : H.PosSemidef) : (totalRankOneForm H c u).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.add
    · rw [Matrix.IsHermitian]
      simpa only [Matrix.fromBlocks_conjTranspose,Matrix.conjTranspose_zero]
        using congrArg (fun A => fromBlocks (0 : Matrix Unit Unit ℝ) 0 0 A) hH.isHermitian.eq
    · simpa only [star_trivial] using (Matrix.posSemidef_vecMulVec_self_star
        (Sum.elim (fun _ => c) u)).isHermitian
  · intro v
    simp only [star_trivial,totalRankOneForm_quadratic]
    exact add_nonneg (sq_nonneg _) (hH.dotProduct_mulVec_nonneg _)

end CAT0Fillings
end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_TotalDeterminant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CAT0Fillings
open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma metricTotalRadialForm_det (G : Matrix ι ι ℝ) (g r t : ℝ) (α γ : ι → ℝ)
    (hG : G.det ≠ 0) :
    (metricTotalRadialForm G g r t α γ).det =
      (r*g)^2*(1-t*g)^(2*Fintype.card ι)*G.det*(1-α ⬝ᵥ G⁻¹.mulVec α) := by
  rw [metricTotalRadialForm,totalRankOneForm_det,Matrix.det_smul,det_sub_vecMulVec G α hG]
  simp only [neg_mul,neg_sq,←pow_mul]
  ring

lemma metricTotalRadialForm_normalized_sqrt_det
    (G : Matrix ι ι ℝ) (g r t : ℝ) (α γ : ι → ℝ)
    (hG : G.PosDef) (hr : 0 ≤ r) (hg : 0 ≤ g) (hscale : 0 ≤ 1-t*g) :
    Real.sqrt (metricTotalRadialForm G g r t α γ).det / Real.sqrt G.det =
      r*g*(1-t*g)^Fintype.card ι * Real.sqrt (1-α ⬝ᵥ G⁻¹.mulVec α) := by
  have he : (metricTotalRadialForm G g r t α γ).det =
      (r*g*(1-t*g)^Fintype.card ι)^2 * G.det *(1-α ⬝ᵥ G⁻¹.mulVec α) := by
    rw [metricTotalRadialForm_det G g r t α γ hG.det_pos.ne']
    simp only [mul_pow,←pow_mul]
    ring
  rw [he,Real.sqrt_mul (mul_nonneg (sq_nonneg _) hG.det_pos.le),
    Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (mul_nonneg (mul_nonneg hr hg) (pow_nonneg hscale _))]
  have hJ : Real.sqrt G.det ≠ 0 := (Real.sqrt_pos.2 hG.det_pos).ne'
  field_simp

end CAT0Fillings

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_TotalBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma metricTotalRadialForm_posSemidef
    (G : Matrix ι ι ℝ) (g r t : ℝ) (α γ : ι → ℝ)
    (hG : G.PosSemidef) (hα : ∀ v : ι → ℝ, (α ⬝ᵥ v)^2 ≤ v ⬝ᵥ G.mulVec v) :
    (metricTotalRadialForm G g r t α γ).PosSemidef := by
  have hQ : (G-vecMulVec α α).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · apply Matrix.IsHermitian.sub hG.isHermitian
      simpa only [star_trivial] using (Matrix.posSemidef_vecMulVec_self_star α).isHermitian
    · intro v
      simp only [star_trivial]
      rw [Matrix.sub_mulVec,dotProduct_sub,dotProduct_vecMulVec_self]
      exact sub_nonneg.mpr (hα v)
  exact totalRankOneForm_posSemidef _ _ _ (hQ.smul (sq_nonneg _))

omit [DecidableEq ι] in
lemma metricTotalRadialForm_quadratic
    (G : Matrix ι ι ℝ) (g r t : ℝ) (α γ : ι → ℝ) (v : Unit ⊕ ι → ℝ) :
    v ⬝ᵥ (metricTotalRadialForm G g r t α γ).mulVec v =
      ((1-t*g)*(α ⬝ᵥ (v ∘ Sum.inr))-t*r*(γ ⬝ᵥ (v ∘ Sum.inr))-r*g*v (Sum.inl ()))^2+
        (1-t*g)^2*((v ∘ Sum.inr) ⬝ᵥ G.mulVec (v ∘ Sum.inr)-
          (α ⬝ᵥ (v ∘ Sum.inr))^2) := by
  rw [metricTotalRadialForm,totalRankOneForm_quadratic,
    Matrix.smul_mulVec,dotProduct_smul,Matrix.sub_mulVec,dotProduct_sub,
    dotProduct_vecMulVec_self,sub_dotProduct,smul_dotProduct,smul_dotProduct]
  simp only [smul_eq_mul]
  ring

end CAT0Fillings

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Swept_RadialChart
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint _root_.OAI.CAT0Fillings.EuclideanStraightening.replaceMap_apply _root_.OAI.CAT0Fillings.EuclideanStraightening.straightenMap_zero _root_.OAI.CAT0Fillings.EuclideanStraightening.switchZero_apply_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
namespace Prism

lemma radialForm_quadratic {k : ℕ} (G : Matrix (Fin k) (Fin k) ℝ)
    (g r t : ℝ) (α γ : Fin k → ℝ) (v : Fin (k+1) → ℝ) :
    v ⬝ᵥ (radialForm G g r t α γ).mulVec v =
      ((1-t*g)*(α ⬝ᵥ (fun j => v j.succ))-t*r*(γ ⬝ᵥ (fun j => v j.succ))-r*g*v 0)^2+
      (1-t*g)^2*((fun j => v j.succ) ⬝ᵥ G.mulVec (fun j => v j.succ)-
        (α ⬝ᵥ (fun j => v j.succ))^2) := by
  rw [radialForm,Matrix.reindex_apply,Matrix.submatrix_mulVec_equiv,
    dotProduct_comp_equiv_symm]
  simpa only [Equiv.symm_symm,Function.comp_def,zeroSumEquiv_symm_inl,
    zeroSumEquiv_symm_inr] using
    metricTotalRadialForm_quadratic G g r t α γ (v ∘ (zeroSumEquiv k).symm)
end Prism

theorem swept_radial_test_normalized_det_le
    {k : ℕ} {X : Type*} [MetricSpace X]
    (seg : X → X → ℝ → X)
    (hcomp : ∀ o x y a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o y b)^2 ≤ (a*dist o x-b*dist o y)^2+
        a*b*(dist x y^2-(dist o x-dist o y)^2))
    {s : Set (Euc (k+1))} {x : Euc (k+1)} (hxs : x ∈ s)
    (hx : Tendsto (fun t => volume (s ∩ closedBall x t) / volume (closedBall x t))
      (𝓝[>] 0) (𝓝 1))
    (f : Euc (k+1) → X) (o : X) (p : Seminorm ℝ (Euc (k+1)))
    (hp : (fun y => dist (f y) (f x)-p (y-x)) =o[𝓝[s] x] (fun y => y-x))
    (G : Matrix (Fin k) (Fin k) ℝ) (hG : G.PosDef)
    (hmetric : ∀ v : Fin (k+1) → ℝ, p (WithLp.toLp 2 v)^2 =
      (fun j => v j.succ) ⬝ᵥ G.mulVec (fun j => v j.succ))
    (g : Euc (k+1) → ℝ) (hg : 0 ≤ g x)
    (hscale : ∀ y ∈ s, 1-y 0*g y ∈ Icc (0:ℝ) 1)
    (α γ : Euc k →L[ℝ] ℝ)
    (hα : HasFDerivWithinAt (fun y => dist o (f y)) (α.comp (Prism.tail k)) s x)
    (hγ : HasFDerivWithinAt g (γ.comp (Prism.tail k)) s x)
    (F : Fin (k+1) → Euc (k+1) → ℝ)
    (L : Fin (k+1) → Euc (k+1) →L[ℝ] ℝ)
    (hL : ∀ i, HasFDerivWithinAt (F i) (L i) s x)
    (u : Fin (k+1) → X → ℝ) (hu : ∀ i, LipschitzWith 1 (u i))
    (hF : ∀ i y, y ∈ s → F i y = u i (seg o (f y) (1-y 0*g y))) :
    |(Matrix.of fun i j => differentialRow (L i) j).det| / Real.sqrt G.det ≤
      dist o (f x)*g x*(1-x 0*g x)^k *
        Real.sqrt (1-differentialRow α ⬝ᵥ G⁻¹.mulVec (differentialRow α)) := by
  have hcontract (v : Fin k → ℝ) :
      (differentialRow α ⬝ᵥ v)^2 ≤ v ⬝ᵥ G.mulVec v := by
    let w : Fin (k+1) → ℝ := Matrix.vecCons 0 v
    have hr := scalar_derivative_bound_of_metric_differential volume hx hα hp
      (K := 1) (by
        intro y _
        simpa only [one_mul,dist_comm o] using abs_dist_sub_le (f y) (f x) o)
      (WithLp.toLp 2 w)
    have hh := (sq_le_sq₀ (abs_nonneg _) (apply_nonneg p _)).2 (by simpa using hr)
    simpa only [sq_abs,ContinuousLinearMap.comp_apply,Prism.tail_apply,w,
      Matrix.cons_val_succ,hmetric,differentialRow_dot] using hh
  let P := Prism.radialForm G (g x) (dist o (f x)) (x 0)
    (differentialRow α) (differentialRow γ)
  have hP : P.PosSemidef := (metricTotalRadialForm_posSemidef G _ _ _
    (differentialRow α) (differentialRow γ) hG.posSemidef hcontract).submatrix (Prism.zeroSumEquiv k)
  have ht : HasFDerivWithinAt (fun y : Euc (k+1) => y 0)
      (PiLp.proj 2 (fun _ : Fin (k+1) => ℝ) 0) s x :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (k+1) => ℝ) 0).hasFDerivWithinAt
  have hd : |(Matrix.of fun i j => differentialRow (L i) j).det| ≤ Real.sqrt P.det := by
    apply abs_det_le_sqrt_det_of_posSemidef _ _ hP
    intro i v
    have hr := radial_scalar_derivative_sq_le volume seg hcomp hxs hx f o p hp hscale hα
      ((ht.mul hγ).const_sub 1) (hL i) (hu i) (hF i) (WithLp.toLp 2 v)
    have heq : (L i (WithLp.toLp 2 v))^2 ≤ v ⬝ᵥ P.mulVec v := by
      change _ ≤ v ⬝ᵥ (Prism.radialForm G (g x) (dist o (f x)) (x 0) _ _).mulVec v
      rw [Prism.radialForm_quadratic]
      convert hr using 1
      all_goals try with_reducible_and_instances rfl
      simp only [differentialRow_dot,ContinuousLinearMap.comp_apply,Prism.tail_apply,
        hmetric,_root_.neg_apply,_root_.add_apply,_root_.smul_apply,smul_eq_mul,PiLp.proj_apply]
      ring
    change |differentialRow (L i) ⬝ᵥ v| ≤ _
    rw [differentialRow_dot]
    exact (Real.le_sqrt (abs_nonneg _) (hP.dotProduct_mulVec_nonneg v)).2 (by simpa using heq)
  have hdiv := div_le_div_of_nonneg_right hd (Real.sqrt_nonneg G.det)
  have hdet : P.det = (metricTotalRadialForm G (g x) (dist o (f x)) (x 0)
      (differentialRow α) (differentialRow γ)).det := det_reindex_self _ _
  rw [hdet] at hdiv
  exact hdiv.trans_eq (by
    simpa using (metricTotalRadialForm_normalized_sqrt_det G (g x)
      (dist o (f x)) (x 0) (differentialRow α) (differentialRow γ) hG dist_nonneg hg
      (hscale x hxs).1))

lemma metric_differential_pullback
    {E F X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [PseudoMetricSpace X]
    (A : E →L[ℝ] F) {s : Set E} {t : Set F} {x : E}
    (hst : MapsTo A s t) (f : F → X) (p : Seminorm ℝ F)
    (hp : (fun y => dist (f y) (f (A x))-p (y-A x)) =o[𝓝[t] (A x)] (fun y => y-A x)) :
    (fun y => dist (f (A y)) (f (A x))-(p.comp A.toLinearMap) (y-x))
      =o[𝓝[s] x] (fun y => y-x) := by
  have ht : Tendsto A (𝓝[s] x) (𝓝[t] (A x)) :=
    A.continuous.continuousWithinAt.tendsto_nhdsWithin hst
  have hB : ((fun y => y-A x) ∘ A) =O[𝓝[s] x] (fun y => y-x) := by
    simpa only [Function.comp_def,map_sub] using (A.isBigO_sub (𝓝[s] x) x)
  have h := (hp.comp_tendsto ht).trans_isBigO hB
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (try rfl)
  all_goals try { ext y; simp only [Function.comp_def,Seminorm.comp_apply,ContinuousLinearMap.coe_coe,map_sub] }
end CAT0Fillings
end

section

open Set Filter MeasureTheory Metric Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
open CurrentOperations

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)

lemma ae_prism_tail {X : Type*} [MetricSpace X] [Nonempty X] {k : ℕ}
    (C : IntegerChart X k) {P : Euc k → Prop}
    (h : ∀ᵐ z ∂volume.restrict C.domain, P z) :
    ∀ᵐ z ∂volume.restrict C.prism.domain, P (Prism.tail k z) := by
  have hh := Measure.quasiMeasurePreserving_snd (μ := volume.restrict (Icc (0:ℝ) 1)) |>.ae h
  rw [Measure.prod_restrict] at hh
  exact ((Prism.split_measurePreserving k).restrict_preimage
    (measurableSet_Icc.prod C.borel)).quasiMeasurePreserving.ae hh

lemma paramExtended_metric_differential {z : Euc k} (hz : z ∈ C.domain)
    {p : Seminorm ℝ (Euc k)}
    (hp : MetricDifferentiation.HasCenteredMetricDifferentialWithin C.domain C.param p ⟨z,hz⟩) :
    (fun y => dist (C.paramExtended y) (C.paramExtended z)-p (y-z))
      =o[𝓝[C.domain] z] (fun y => y-z) := by
  rw [nhdsWithin_eq_map_subtype_coe hz,Asymptotics.isLittleO_map]
  change (fun y : C.domain => dist (C.param y) (C.param ⟨z,hz⟩)-p ((y : Euc k)-z))
    =o[𝓝 (⟨z,hz⟩ : C.domain)] (fun y : C.domain => (y : Euc k)-z) at hp
  convert hp using 1
  · ext y
    simp only [Function.comp_apply,paramExtended,dite_eq_left y.property,dite_eq_left hz,Subtype.coe_eta]
  · rfl

lemma scalar_paramExtended_eqOn (b : X → ℝ) :
    EqOn (fun z => b (C.paramExtended z)) (C.scalar b) C.domain := by
  intro z hz; simp only [paramExtended,scalar,dite_eq_left hz]

lemma ae_swept_jacobian_bound
    (seg : X → X → ℝ → X)
    (hcomp : ∀ o x y a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o y b)^2 ≤ (a*dist o x-b*dist o y)^2+
        a*b*(dist x y^2-(dist o x-dist o y)^2))
    (o : X) (g : X → ℝ) {Kg KF : ℝ≥0} (hg : LipschitzWith Kg g)
    (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1)
    (F : ℝ × X → X) (hF : LipschitzWith KF F)
    (hFeq : ∀ t ∈ Icc (0:ℝ) 1, ∀ y, F (t,y) = seg o y (1-t*g y))
    (p : Euc k → Seminorm ℝ (Euc k))
    (hp : ∀ᵐ z ∂volume.restrict C.domain,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
      (∀ v, p z v = 0 ↔ v = 0))
    (π : Fin (k+1) → X → ℝ) (hπ : ∀ i, LipschitzWith 1 (π i)) :
    ∀ᵐ z ∂volume.restrict C.prism.domain,
      |C.prism.jacobian (fun i => π i ∘ F) z| ≤ C.sweptWeight p o g (Prism.tail k z) := by
  have htests : ∀ᵐ z ∂volume.restrict C.prism.domain, ∀ i,
      DifferentiableWithinAt ℝ (C.prism.scalar (π i ∘ F)) C.prism.domain z :=
    ae_all_iff.mpr fun i => C.prism.ae_differentiableWithinAt_scalar ((hπ i).comp hF)
  filter_upwards [C.ae_prism_tail hp,ae_restrict_mem C.prism.borel,
    Besicovitch.ae_tendsto_measure_inter_div volume C.prism.domain,
    C.ae_prism_tail (C.ae_differentiableWithinAt_scalar (LipschitzWith.dist_right o)),
    C.ae_prism_tail (C.ae_differentiableWithinAt_scalar hg),htests]
    with z hpz hzs hden hr hgz htests
  have hzt : z 0 ∈ Icc (0:ℝ) 1 := hzs.1
  have hzw : Prism.tail k z ∈ C.domain := hzs.2
  have hmap : MapsTo (Prism.tail k) C.prism.domain C.domain := fun _ hy => hy.2
  let w := Prism.tail k z
  let G := polarizationMatrix (p w) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  have hG : G.PosDef := polarizationMatrix_posDef _ _ hpz.2.2 hpz.2.1
  have hquad (v : Fin k → ℝ) : v ⬝ᵥ G.mulVec v = p w (WithLp.toLp 2 v)^2 := by
    have hrepr : (EuclideanSpace.basisFun (Fin k) ℝ).toBasis.repr (WithLp.toLp 2 v) = v := by
      ext j; simp
    simpa only [hrepr] using polarizationMatrix_quadratic
      (EuclideanSpace.basisFun (Fin k) ℝ).toBasis (p w) hpz.2.2 hpz.2.1 (WithLp.toLp 2 v)
  have hpe := metric_differential_pullback (Prism.tail k) hmap C.paramExtended (p w)
    (C.paramExtended_metric_differential hzw (hpz.1 hzw))
  have hR := (hr.hasFDerivWithinAt.congr (C.scalar_paramExtended_eqOn (dist o))
    (C.scalar_paramExtended_eqOn (dist o) hzw)).comp z (Prism.tail k).hasFDerivWithinAt hmap
  have hDg := (hgz.hasFDerivWithinAt.congr (C.scalar_paramExtended_eqOn g)
    (C.scalar_paramExtended_eqOn g hzw)).comp z (Prism.tail k).hasFDerivWithinAt hmap
  have hscale : ∀ y ∈ C.prism.domain, 1-y 0*g (C.paramExtended (Prism.tail k y)) ∈ Icc (0:ℝ) 1 := by
    intro y hy
    have ht : y 0 ∈ Icc (0:ℝ) 1 := hy.1
    have h0 := hg0 (C.paramExtended (Prism.tail k y))
    have h1 := hg1 (C.paramExtended (Prism.tail k y))
    constructor
    · exact sub_nonneg.mpr (((mul_le_mul_of_nonneg_right ht.2 h0).trans_eq (one_mul _)).trans h1)
    · exact sub_le_self _ (mul_nonneg ht.1 h0)
  have hh := swept_radial_test_normalized_det_le seg hcomp hzs hden
    (fun y => C.paramExtended (Prism.tail k y)) o ((p w).comp (Prism.tail k).toLinearMap) hpe
    G hG (by intro v; simpa only [Seminorm.comp_apply,ContinuousLinearMap.coe_coe,Prism.tail_apply] using (hquad (fun j => v j.succ)).symm)
    (fun y => g (C.paramExtended (Prism.tail k y))) (hg0 _) hscale
    (fderivWithin ℝ (C.scalar (dist o)) C.domain w)
    (fderivWithin ℝ (C.scalar g) C.domain w) hR hDg
    (fun i => C.prism.scalar (π i ∘ F))
    (fun i => fderivWithin ℝ (C.prism.scalar (π i ∘ F)) C.prism.domain z)
    (fun i => (htests i).hasFDerivWithinAt) π hπ (by
      intro i y hy
      rw [C.prism.scalar_eq hy]
      have hyt : y 0 ∈ Icc (0:ℝ) 1 := hy.1
      have hyw : Prism.tail k y ∈ C.domain := hy.2
      change π i (F (y 0,C.param ⟨Prism.tail k y,hyw⟩)) = _
      rw [hFeq (y 0) hyt]
      simp only [paramExtended,dite_eq_left hyw])
  have hs := (div_le_iff₀ (Real.sqrt_pos.2 hG.det_pos)).mp hh
  change |C.prism.jacobian (fun i => π i ∘ F) z| ≤ _ at hs
  have hlam := hscale z hzs
  have hpow : (1-z 0*g (C.paramExtended w))^k ≤ 1 := pow_le_one₀ hlam.1 hlam.2
  have hn : 0 ≤ dist o (C.paramExtended w)*g (C.paramExtended w) := mul_nonneg dist_nonneg (hg0 _)
  calc
    _ ≤ _ := hs
    _ ≤ dist o (C.paramExtended w)*g (C.paramExtended w)*
        Real.sqrt (1-differentialRow (fderivWithin ℝ (C.scalar (dist o)) C.domain w) ⬝ᵥ
          G⁻¹.mulVec (differentialRow (fderivWithin ℝ (C.scalar (dist o)) C.domain w))) * Real.sqrt G.det := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          ((mul_le_mul_of_nonneg_left hpow hn).trans_eq (mul_one _)) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)
    _ = _ := by
      simp only [sweptWeight,←C.scalar_paramExtended_eqOn (dist o) hzw,
        ←C.scalar_paramExtended_eqOn g hzw,w,G]
end IntegerChart
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Swept_Measure
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [nonemptyX : Nonempty X] {k : ℕ} (C : IntegerChart X k)

include nonemptyX

attribute [local instance] OAI.CAT0Fillings.instMeasurableSpaceMatrixFinReal_solutions
attribute [local instance] OAI.CAT0Fillings.instBorelSpaceMatrixFinReal_solutions
omit nonemptyX in
lemma aestronglyMeasurable_sweptWeight [Nonempty X]
    (p : Euc k → Seminorm ℝ (Euc k)) (hpm : ∀ v, Measurable (fun z => p z v))
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    AEStronglyMeasurable (C.sweptWeight p o g) (volume.restrict C.domain) := by
  obtain ⟨L,U,hL,_⟩ := C.bilipschitz
  obtain ⟨R,hR,heR⟩ := (C.scalar_lipschitzOn hL (LipschitzWith.dist_right o)).extend_real
  let P (z : Euc k) := polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  have hPm : Measurable P := by
    have hh : Measurable (fun z i j => P z i j) :=
      measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
        measurable_polarizationMatrix p (EuclideanSpace.basisFun (Fin k) ℝ).toBasis hpm i j
    have heq : _root_.borel (Fin k → Fin k → ℝ) = MeasurableSpace.pi :=
      BorelSpace.measurable_eq.symm
    change @Measurable (Euc k) (Fin k → Fin k → ℝ) _ (_root_.borel _) P
    rw [heq]
    exact hh
  have hRd : Measurable (fun z => differentialRow (fderiv ℝ R z)) := by
    apply measurable_pi_iff.mpr
    intro i
    simp only [differentialRow]
    fun_prop
  have hPi := measurable_matrix_inverse P hPm
  let J (z : Euc k) := C.scalar (dist o) z*C.scalar g z*
    Real.sqrt (1-differentialRow (fderiv ℝ R z) ⬝ᵥ
      (P z)⁻¹.mulVec (differentialRow (fderiv ℝ R z)))*Real.sqrt (P z).det
  have hJ : Measurable J := by
    have hprod : Measurable (fun z => differentialRow (fderiv ℝ R z) ⬝ᵥ
        (P z)⁻¹.mulVec (differentialRow (fderiv ℝ R z))) := by
      have hc : Continuous (fun q : (Fin k → ℝ) × Matrix (Fin k) (Fin k) ℝ =>
          q.1 ⬝ᵥ q.2.mulVec q.1) := by fun_prop
      exact hc.measurable.comp (hRd.prodMk hPi)
    exact (((C.measurable_scalar (LipschitzWith.dist_right o)).mul (C.measurable_scalar hg)).mul
      ((measurable_const.sub hprod).sqrt)).mul
      ((continuous_id.matrix_det.measurable.comp hPm).sqrt)
  apply hJ.aestronglyMeasurable.congr
  filter_upwards [ae_fderivWithin_eq_fderiv_extension volume C.borel hR heR] with z hz
  simp only [J,sweptWeight,hz,P]

omit nonemptyX in
lemma ae_sweptWeight_nonneg [Nonempty X]
    (p : Euc k → Seminorm ℝ (Euc k)) (o : X) {g : X → ℝ}
    (hg0 : ∀ x, 0 ≤ g x) : 0 ≤ᵐ[volume.restrict C.domain] C.sweptWeight p o g := by
  filter_upwards [ae_restrict_mem C.borel] with z hz
  simp only [sweptWeight,C.scalar_eq hz]
  exact mul_nonneg (mul_nonneg (mul_nonneg dist_nonneg (hg0 _)) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

omit nonemptyX in
lemma ae_sweptWeight_bound [Nonempty X]
    (p : Euc k → Seminorm ℝ (Euc k))
    (hp : ∀ᵐ z ∂volume.restrict C.domain,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
      (∀ v, p z v = 0 ↔ v = 0))
    (o : X) {g : X → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    {B : ℝ} (hB : ∀ x, dist o x*g x ≤ B) :
    ∀ᵐ z ∂volume.restrict C.domain,
      C.sweptWeight p o g z ≤ B*Real.sqrt
        (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det := by
  filter_upwards [hp,ae_restrict_mem C.borel] with z hpz hz
  let G := polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let α := differentialRow (fderivWithin ℝ (C.scalar (dist o)) C.domain z)
  have hG : G.PosDef := polarizationMatrix_posDef _ _ hpz.2.2 hpz.2.1
  have hq : 0 ≤ α ⬝ᵥ G⁻¹.mulVec α := hG.inv.posSemidef.dotProduct_mulVec_nonneg α
  have hs : Real.sqrt (1-α ⬝ᵥ G⁻¹.mulVec α) ≤ 1 := by
    apply (Real.sqrt_le_left zero_le_one).mpr
    linarith
  change C.scalar (dist o) z*C.scalar g z*Real.sqrt (1-α ⬝ᵥ G⁻¹.mulVec α)*Real.sqrt G.det ≤ _
  rw [C.scalar_eq hz,C.scalar_eq hz]
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact ((mul_le_mul_of_nonneg_left hs (mul_nonneg dist_nonneg (hg0 _))).trans_eq
    (mul_one _)).trans (hB _)

theorem integrable_sweptWeight
    (p : Euc k → Seminorm ℝ (Euc k)) (hpm : ∀ v, Measurable (fun z => p z v))
    (hp : ∀ᵐ z ∂volume.restrict C.domain,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
      (∀ v, p z v = 0 ↔ v = 0))
    (hρ : Integrable (fun z => |(C.multiplicity z : ℝ)| *Real.sqrt
      (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det)
      (volume.restrict C.domain))
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    (hg0 : ∀ x, 0 ≤ g x) {B : ℝ} (hB : ∀ x, dist o x*g x ≤ B) :
    Integrable (fun z => |(C.multiplicity z : ℝ)| * C.sweptWeight p o g z)
      (volume.restrict C.domain) := by
  apply (hρ.const_mul B).mono'
    (C.integrable.abs.aestronglyMeasurable.mul (C.aestronglyMeasurable_sweptWeight p hpm o hg))
  filter_upwards [C.ae_sweptWeight_nonneg p o hg0,C.ae_sweptWeight_bound p hp o hg0 hB] with z hn hb
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs,abs_mul,abs_abs,abs_of_nonneg hn]
  exact (mul_le_mul_of_nonneg_left hb (abs_nonneg _)).trans_eq (by ring)
end IntegerChart
end CAT0Fillings
end

section

open Set Filter MeasureTheory Metric Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
open CurrentOperations

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)

lemma integrable_prism_tail {f : Euc k → ℝ}
    (hf : Integrable f (volume.restrict C.domain)) :
    Integrable (fun z => f (Prism.tail k z)) (volume.restrict C.prism.domain) := by
  have hi := hf.comp_snd (volume.restrict (Icc (0:ℝ) 1))
  rw [Measure.prod_restrict] at hi
  exact ((Prism.split_measurePreserving k).restrict_preimage
    (measurableSet_Icc.prod C.borel)).integrable_comp_emb
      (Prism.split k).toHomeomorph.measurableEmbedding |>.mpr hi

lemma integral_prism_tail {f : Euc k → ℝ}
    (hf : Integrable f (volume.restrict C.domain)) :
    (∫ z, f (Prism.tail k z) ∂volume.restrict C.prism.domain) =
      ∫ z, f z ∂volume.restrict C.domain := by
  rw [←C.prism_split_measurePreserving.integral_comp
    (Prism.split k).symm.toHomeomorph.measurableEmbedding]
  have heq (q : ℝ × Euc k) : Prism.tail k ((Prism.split k).symm q) = q.2 := by
    change (Prism.split k ((Prism.split k).symm q)).2 = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
  simp_rw [heq]
  rw [integral_prod _ (hf.comp_snd _)]
  simp [integral_const,Measure.real,Real.volume_Icc]

variable [Nonempty X] [MeasurableSpace X] [BorelSpace X]

theorem swept_prism_mass_le
    (seg : X → X → ℝ → X)
    (hcomp : ∀ o x y a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o y b)^2 ≤ (a*dist o x-b*dist o y)^2+
        a*b*(dist x y^2-(dist o x-dist o y)^2))
    (o : X) (g : X → ℝ) {Kg KF : ℝ≥0} (hg : LipschitzWith Kg g)
    (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1)
    (F : ℝ × X → X) (hF : LipschitzWith KF F)
    (hFeq : ∀ t ∈ Icc (0:ℝ) 1, ∀ y, F (t,y) = seg o y (1-t*g y))
    (p : Euc k → Seminorm ℝ (Euc k))
    (hI : Integrable (fun z => |(C.multiplicity z : ℝ)| *C.sweptWeight p o g z)
      (volume.restrict C.domain))
    (hp : ∀ᵐ z ∂volume.restrict C.domain,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
      (∀ v, p z v = 0 ↔ v = 0)) :
    mass (pushCurrent F C.prism.action) ≤
      ∫ z, |(C.multiplicity z : ℝ)| *C.sweptWeight p o g z ∂volume.restrict C.domain := by
  have hi : Integrable (fun z => |(C.prism.multiplicity z : ℝ)| *
      C.sweptWeight p o g (Prism.tail k z)) (volume.restrict C.prism.domain) :=
    C.integrable_prism_tail hI
  have hm := C.prism.push_mass_le_majorant hF hi
    (C.ae_prism_tail (C.ae_sweptWeight_nonneg p o hg0))
    (C.ae_swept_jacobian_bound seg hcomp o g hg hg0 hg1 F hF hFeq p hp)
  exact hm.trans_eq (C.integral_prism_tail hI)

end IntegerChart
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Swept_WholeMass
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings
variable {X : Type*} [MetricSpace X] [CompactSpace X]

omit [CompactSpace X] in
lemma swept_fraction_lipschitz [CompactSpace X] {g : X → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1) :
    LipschitzWith (K+1) (fun p : ClosedCylinder X => 1-p.1.val*g p.2) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have hp : |p.1.val| ≤ 1 := by rw [abs_of_nonneg p.1.2.1]; exact p.1.2.2
  have hq : |g q.2| ≤ 1 := by rw [abs_of_nonneg (hg0 _)]; exact hg1 _
  have ht : |p.1.val-q.1.val| ≤ dist p q := le_max_left _ _
  have hx : dist p.2 q.2 ≤ dist p q := le_max_right _ _
  rw [Real.dist_eq,show 1-p.1.val*g p.2-(1-q.1.val*g q.2) =
    -(p.1.val*(g p.2-g q.2)+(p.1.val-q.1.val)*g q.2) by ring,abs_neg]
  calc _ ≤ |p.1.val*(g p.2-g q.2)|+|(p.1.val-q.1.val)*g q.2| := abs_add_le _ _
    _ ≤ |g p.2-g q.2|+|p.1.val-q.1.val| := by
      simp only [abs_mul]
      exact add_le_add (mul_le_of_le_one_left (abs_nonneg _) hp)
        (mul_le_of_le_one_right (abs_nonneg _) hq)
    _ ≤ (K:ℝ)*dist p q+dist p q := by
      exact add_le_add ((hg.dist_le_mul p.2 q.2).trans
        (mul_le_mul_of_nonneg_left hx K.coe_nonneg)) ht
    _ = _ := by push_cast; ring

theorem exists_swept_radial_map
    (seg : X → X → ℝ → X)
    (hseg : ∀ o x a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o x b) = |a-b| *dist o x)
    (hcomp : ∀ o x y a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o y b)^2 ≤ (a*dist o x-b*dist o y)^2+
        a*b*(dist x y^2-(dist o x-dist o y)^2))
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1) :
    ∃ F : ClosedCylinder X → X, (∃ L, LipschitzWith L F) ∧
      (∀ p, F p = seg o p.2 (1-p.1.val*g p.2)) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ y,
        F (cylinderClamp (t,y)) = seg o y (1-t*g y)) := by
  let R : ℝ≥0 := ⟨Metric.diam (univ : Set X),Metric.diam_nonneg⟩
  have hl := swept_fraction_lipschitz hg hg0 hg1
  have hR : ∀ p : ClosedCylinder X, dist o p.2 ≤ R := fun p =>
    Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ _) (mem_univ _)
  have hs (p : ClosedCylinder X) : 1-p.1.val*g p.2 ∈ Icc (0:ℝ) 1 := by
    constructor
    · exact sub_nonneg.mpr (((mul_le_mul_of_nonneg_right p.1.2.2 (hg0 _)).trans_eq
        (one_mul _)).trans (hg1 _))
    · exact sub_le_self _ (mul_nonneg p.1.2.1 (hg0 _))
  refine ⟨fun p => seg o p.2 (1-p.1.val*g p.2),⟨1+R*(K+1),?_⟩,
    fun _ => rfl,?_⟩
  · rw [←lipschitzOnWith_univ]
    exact radial_lipschitzOnWith seg hseg hcomp LipschitzWith.prod_snd.lipschitzOnWith
      hl.lipschitzOnWith (fun x _ => hs x) o (fun x _ => hR x)
  · intro t ht y
    simp only [cylinderClamp,projIcc_of_mem (by norm_num : (0:ℝ) ≤ 1) ht]

end CAT0Fillings
end

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
open CurrentOperations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}

theorem whole_swept_mass_le
    (C : ℕ → IntegerChart X k) (_hs : Summable (fun i => mass (C i).action))
    (seg : X → X → ℝ → X)
    (hcomp : ∀ o x y a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o y b)^2 ≤ (a*dist o x-b*dist o y)^2+
        a*b*(dist x y^2-(dist o x-dist o y)^2))
    (o : X) (g : X → ℝ) {Kg KF : ℝ≥0} (hg : LipschitzWith Kg g)
    (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1)
    (F : ClosedCylinder X → X) (hF : LipschitzWith KF F)
    (hFeq : ∀ t ∈ Icc (0:ℝ) 1, ∀ y,
      F (cylinderClamp (t,y)) = seg o y (1-t*g y))
    (p : ℕ → Euc k → Seminorm ℝ (Euc k))
    (hI : ∀ i, Integrable (fun z => |((C i).multiplicity z : ℝ)| *(C i).sweptWeight (p i) o g z)
      (volume.restrict (C i).domain))
    (hIs : Summable (fun i => ∫ z, |((C i).multiplicity z : ℝ)| *(C i).sweptWeight (p i) o g z
      ∂volume.restrict (C i).domain))
    (hp : ∀ i, ∀ᵐ z ∂volume.restrict (C i).domain,
      (∀ hz : z ∈ (C i).domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        (C i).domain (C i).param (p i z) ⟨z,hz⟩) ∧
      (∀ u v, p i z (u+v)^2+p i z (u-v)^2 = 2*p i z u^2+2*p i z v^2) ∧
      (∀ v, p i z v = 0 ↔ v = 0)) :
    mass (pushCurrent F (closedPrismFamily C)) ≤
      ∑' i, ∫ z, |((C i).multiplicity z : ℝ)| *(C i).sweptWeight (p i) o g z
      ∂volume.restrict (C i).domain := by
  let I (i : ℕ) := ∫ z, |((C i).multiplicity z : ℝ)| *(C i).sweptWeight (p i) o g z
    ∂volume.restrict (C i).domain
  let S (i : ℕ) := pushCurrent F (C i).closedPrism.action
  have hS (i : ℕ) : IsMetricCurrent (S i) :=
    pushCurrent_isMetricCurrent (C i).closedPrism.action_isMetricCurrent hF
  have hle (i : ℕ) : mass (S i) ≤ I i := by
    dsimp only [S]
    rw [(C i).closedPrism_action,←pushCurrent_comp hF]
    exact (C i).swept_prism_mass_le seg hcomp o g hg hg0 hg1
      (F ∘ cylinderClamp) (hF.comp cylinderClamp_lipschitz) hFeq (p i) (hI i) (hp i)
  have hsum : Summable (fun i => mass (S i)) :=
    hIs.of_nonneg_of_le (fun _ => mass_nonneg _) hle
  have heq : pushCurrent F (closedPrismFamily C) = fun b π => ∑' i, S i b π := by
    funext b π
    by_cases hab : Admissible b π
    · simp only [S,pushCurrent_apply _ _ hab,closedPrismFamily_action]
    · simp only [S,pushCurrent,ite_eq_right hab,tsum_zero]
  rw [heq]
  exact (mass_tsum_le hS hsum).trans (hsum.tsum_le_tsum hle hIs)

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] in
lemma summable_swept_integrals [MeasurableSpace X] [BorelSpace X] [CompactSpace X]
    (C : ℕ → IntegerChart X k) (p : ℕ → Euc k → Seminorm ℝ (Euc k))
    (hpm : ∀ i v, Measurable (fun z => p i z v))
    (hp : ∀ i, ∀ᵐ z ∂volume.restrict (C i).domain,
      (∀ hz : z ∈ (C i).domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        (C i).domain (C i).param (p i z) ⟨z,hz⟩) ∧
      (∀ u v, p i z (u+v)^2+p i z (u-v)^2 = 2*p i z u^2+2*p i z v^2) ∧
      (∀ v, p i z v = 0 ↔ v = 0))
    (hρ : ∀ i, Integrable (fun z => |((C i).multiplicity z : ℝ)| *Real.sqrt
      (polarizationMatrix (p i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det)
      (volume.restrict (C i).domain))
    (hρs : Summable (fun i => ∫ z, |((C i).multiplicity z : ℝ)| *Real.sqrt
      (polarizationMatrix (p i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det
      ∂volume.restrict (C i).domain))
    (o : X) {g : X → ℝ} {Kg : ℝ≥0} (hg : LipschitzWith Kg g)
    (hg0 : ∀ y, 0 ≤ g y) {B : ℝ} (hB : ∀ y, dist o y*g y ≤ B) :
    (∀ i, Integrable (fun z => |((C i).multiplicity z : ℝ)| *(C i).sweptWeight (p i) o g z)
      (volume.restrict (C i).domain)) ∧
    Summable (fun i => ∫ z, |((C i).multiplicity z : ℝ)| *(C i).sweptWeight (p i) o g z
      ∂volume.restrict (C i).domain) := by
  have hI i := (C i).integrable_sweptWeight (p i) (hpm i) (hp i) (hρ i) o hg hg0 hB
  refine ⟨hI,(hρs.mul_left B).of_nonneg_of_le ?_ ?_⟩
  · intro i
    apply integral_nonneg_of_ae
    exact ((C i).ae_sweptWeight_nonneg (p i) o hg0).mono fun z hz => mul_nonneg (abs_nonneg _) hz
  · intro i
    rw [←integral_const_mul]
    apply integral_mono_ae (hI i) ((hρ i).const_mul B)
    filter_upwards [(C i).ae_sweptWeight_bound (p i) (hp i) o hg0 hB] with z hz
    exact (mul_le_mul_of_nonneg_left hz (abs_nonneg _)).trans_eq (by ring)

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Swept_Current
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
open CurrentOperations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}

namespace ChartGeometry
variable {T : Functional X k} {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma density_mass : mass T = ∑' i, ∫ z, q.density i z
    ∂volume.restrict (q.chart i).domain := by
  simpa only [density,gram,q.chart_mass] using q.total_mass

end ChartGeometry
end CAT0Fillings
end

section

open Set Filter MeasureTheory
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
open CurrentOperations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X] in
lemma endpoint_lipschitz [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X]
    (t : Icc (0:ℝ) 1) :
    LipschitzWith 1 (fun y : X => (t,y) : X → ClosedCylinder X) := by
  simpa using (LipschitzWith.const t).prodMk
    (LipschitzWith.id : LipschitzWith 1 (id : X → X))

theorem swept_boundary_integral
    {T : Functional X (k+1)} (hT : IsIntegral (k+1) T) (hz : boundarySucc T = 0)
    (C : ℕ → IntegerChart X (k+1))
    (hd : Pairwise (fun i j => Disjoint (C i).image (C j).image))
    (hs : Summable (fun i => mass (C i).action))
    (heq : ∀ b π, T b π = ∑' i, (C i).action b π)
    (F : ClosedCylinder X → X) {K : ℝ≥0} (hF : LipschitzWith K F)
    (hF0 : ∀ y, F (⟨0,by constructor <;> norm_num⟩,y) = y) :
    IsIntegral (k+2) (pushCurrent F (closedPrismFamily C)) ∧
    boundarySucc (pushCurrent F (closedPrismFamily C)) =
      pushCurrent (fun y => F (⟨1,by constructor <;> norm_num⟩,y)) T - T := by
  let f : X → X := fun y => F (⟨1,by constructor <;> norm_num⟩,y)
  have hf : LipschitzWith K f := by
    simpa only [mul_one,Function.comp_def,f] using
      hF.comp (endpoint_lipschitz (X := X) ⟨1,by constructor <;> norm_num⟩)
  let : Nonempty (ClosedCylinder X) := ⟨(⟨0,by constructor <;> norm_num⟩,Classical.choice inferInstance)⟩
  have hb : boundarySucc (pushCurrent F (closedPrismFamily C)) = pushCurrent f T - T := by
    funext b π
    by_cases hab : Admissible b π
    · rw [pushCurrent_boundarySucc _ hF,pushCurrent_apply _ _ hab,
        closedPrismFamily_boundary_cycle hT.1 hT.2.1 hz C hs heq _ _
          (admissible_comp hab hF)]
      simp only [Pi.sub_apply,pushCurrent_apply _ _ hab,Function.comp_apply,hF0,f]
      rfl
    · simp only [boundarySucc,Pi.sub_apply,pushCurrent,ite_eq_right hab,
        hT.1.offDomain b π hab,sub_self]
  have hbi := (integral_push hT hf).sub hT
  refine ⟨⟨pushCurrent_isMetricCurrent (closedPrismFamily_current C hs) hF,
    integerRectifiable_push (closedPrismFamily_rectifiable C hd hs) hF,?_,?_⟩,hb⟩
  · rw [hb]; exact hbi.1
  · rw [hb]; exact hbi.2.1

end CAT0Fillings
end

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
open CurrentOperations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}

namespace ChartGeometry
variable {T : Functional X k} {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma swept_integrable_summable (o : X) {g : X → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hg0 : ∀ y, 0 ≤ g y) :
    (∀ i, Integrable (fun z => |((q.chart i).multiplicity z : ℝ)| *
      (q.chart i).sweptWeight (q.field i) o g z)
      (volume.restrict (q.chart i).domain)) ∧
    Summable (fun i => ∫ z, |((q.chart i).multiplicity z : ℝ)| *
      (q.chart i).sweptWeight (q.field i) o g z ∂volume.restrict (q.chart i).domain) := by
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    ((continuous_const.dist continuous_id).mul hg.continuous).continuousOn
  apply summable_swept_integrals q.chart q.field q.measurable q.differential q.integrable
    q.density_summable o hg hg0
  intro y
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs,Pi.mul_apply,id_eq] using hB y (mem_univ y))

lemma sweptMass_const_mul (o : X) (g : X → ℝ) (h : ℝ) :
    q.sweptMass o (fun y => h*g y) = h*q.sweptMass o g := by
  have hs (C : IntegerChart X k) : C.scalar (fun y => h*g y) = fun z => h*C.scalar g z := by
    funext z
    by_cases hz : z ∈ C.domain <;> simp [IntegerChart.scalar,hz]
  simp only [sweptMass,IntegerChart.sweptWeight,hs]
  simp_rw [show ∀ (a b c d e : ℝ), a*(b*(h*c)*d*e) = h*(a*(b*c*d*e)) by intros; ring]
  simp only [integral_const_mul,tsum_mul_left]

end ChartGeometry

theorem exists_swept_current {T : Functional X (k+1)}
    (hT : IsIntegral (k+1) T) (hz : boundarySucc T = 0) (q : ChartGeometry hT.1)
    (seg : X → X → ℝ → X)
    (hseg : ∀ o x a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o x b) = |a-b| *dist o x)
    (hcomp : ∀ o x y a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o y b)^2 ≤ (a*dist o x-b*dist o y)^2+
        a*b*(dist x y^2-(dist o x-dist o y)^2))
    (hseg1 : ∀ o x, seg o x 1 = x)
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1) :
    ∃ S : Functional X (k+2), IsIntegral (k+2) S ∧
      boundarySucc S = pushCurrent (fun y => seg o y (1-g y)) T - T ∧
      mass S ≤ q.sweptMass o g := by
  obtain ⟨F,⟨L,hF⟩,hFeq,hFcl⟩ := exists_swept_radial_map seg hseg hcomp o hg hg0 hg1
  have hF0 : ∀ y, F (⟨0,by constructor <;> norm_num⟩,y) = y := by
    intro y
    rw [hFeq]
    simp only [zero_mul,sub_zero,hseg1]
  obtain ⟨hS,hb⟩ := swept_boundary_integral hT hz q.chart q.disjoint q.summable q.action F hF hF0
  obtain ⟨hI,hIs⟩ := q.swept_integrable_summable o hg hg0
  refine ⟨pushCurrent F (closedPrismFamily q.chart),hS,?_,?_⟩
  · simpa only [hFeq,one_mul] using hb
  · exact whole_swept_mass_le q.chart q.summable seg hcomp o g hg hg0 hg1 F hF hFcl
      q.field hI hIs q.differential

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_IntegralDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
attribute [local instance] OAI.CAT0Fillings.instMeasurableSpaceMatrixReal_solutions_1
local instance instBorelSpaceMatrixReal_solutions_1 : BorelSpace (Matrix ι ι ℝ) := ⟨rfl⟩
lemma measurable_metricSpatialRadialJacobian (t : ℝ) :
    Measurable (fun p : MetricRadialParameters ι =>
      Real.sqrt (metricSpatialRadialForm p.1 p.2.1.1 p.2.1.2 t p.2.2.1 p.2.2.2).det /
        Real.sqrt p.1.det) := by
  apply Measurable.div
  · apply Continuous.measurable
    apply Real.continuous_sqrt.comp
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [metricSpatialRadialForm,Matrix.add_apply,Matrix.sub_apply,
      Matrix.smul_apply,Matrix.vecMulVec_apply,smul_eq_mul]
    fun_prop
  · exact (Real.continuous_sqrt.comp continuous_fst.matrix_det).measurable

end CAT0Fillings

namespace CAT0Fillings
open MeasureTheory Set Filter Matrix
open scoped Topology BigOperators Matrix.Norms.Elementwise

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

attribute [local instance] OAI.CAT0Fillings.instMeasurableSpaceMatrixReal_solutions_2
local instance instBorelSpaceMatrixReal_solutions_2_r297a55_1 : BorelSpace (Matrix ι ι ℝ) := ⟨rfl⟩
theorem integrated_intrinsicRadialJacobian_hasDerivWithinAt_zero
    (μ : Measure Ω) [IsFiniteMeasure μ] (p : Ω → MetricRadialParameters ι)
    (hp : Measurable p) {B : ℝ} (hB : 0 ≤ B)
    (hdata : ∀ᵐ x ∂μ, |(p x).2.1.1| ≤ B ∧ |(p x).2.1.2| ≤ B ∧
      (∀ v : ι → ℝ, ((p x).2.2.1 ⬝ᵥ v)^2 ≤ B^2*(v ⬝ᵥ (p x).1.mulVec v)) ∧
      (∀ v : ι → ℝ, ((p x).2.2.2 ⬝ᵥ v)^2 ≤ B^2*(v ⬝ᵥ (p x).1.mulVec v)))
    (hG : ∀ᵐ x ∂μ, (p x).1.PosDef) :
    HasDerivWithinAt
      (fun t => ∫ x, Real.sqrt (metricSpatialRadialForm
        (p x).1 (p x).2.1.1 (p x).2.1.2 t (p x).2.2.1 (p x).2.2.2).det /
          Real.sqrt (p x).1.det ∂μ)
      (∫ x, -((Fintype.card ι : ℝ)*(p x).2.1.1+
        (p x).2.1.2*((p x).2.2.1 ⬝ᵥ ((p x).1)⁻¹.mulVec (p x).2.2.2)) ∂μ)
      (Ici 0) 0 := by
  let J : ℝ → Ω → ℝ := fun t x =>
    Real.sqrt (metricSpatialRadialForm
      (p x).1 (p x).2.1.1 (p x).2.1.2 t (p x).2.2.1 (p x).2.2.2).det /
        Real.sqrt (p x).1.det
  have hJm (t : ℝ) : Measurable (J t) :=
    (measurable_metricSpatialRadialJacobian t).comp hp
  have hJ0 : ∀ᵐ x ∂μ, J 0 x = 1 := by
    filter_upwards [hG] with x hx
    have hpos : 0 < (p x).1.det := hx.det_pos
    simp [J,metricSpatialRadialForm, (Real.sqrt_pos.2 hpos).ne']
  obtain ⟨C,hC,hbound⟩ := metricSpatialRadialForm_intrinsic_uniform_slope_bound (ι := ι) B hB
  have hJI {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : Integrable (J t) μ := by
    apply (integrable_const (C+1)).mono' (hJm t).aestronglyMeasurable
    filter_upwards [hdata,hG] with x hx hgx
    have he := hbound (p x).1 hgx (p x).2.1.1 (p x).2.1.2 hx.1 hx.2.1 (p x).2.2.1 (p x).2.2.2 hx.2.2.1 hx.2.2.2 t ht
    change |J t x-1| ≤ C*t at he
    have hnonneg : 0 ≤ J t x := div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [Real.norm_eq_abs,abs_of_nonneg hnonneg]
    have := le_abs_self (J t x-1)
    have hCt : C*t ≤ C := (mul_le_mul_of_nonneg_left ht.2 hC).trans_eq (mul_one C)
    linarith
  have hlim : Tendsto (fun t => ∫ x, (J t x-1)/t ∂μ) (𝓝[>] (0:ℝ))
      (𝓝 (∫ x, -((Fintype.card ι : ℝ)*(p x).2.1.1+
        (p x).2.1.2*((p x).2.2.1 ⬝ᵥ ((p x).1)⁻¹.mulVec (p x).2.2.2)) ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => C)
    · exact Eventually.of_forall fun t => ((hJm t).sub_const 1 |>.div_const t).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin,
        (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with t ht ht1
      filter_upwards [hdata,hG] with x hx hgx
      simp only [Real.norm_eq_abs,abs_div,abs_of_pos (show 0<t from ht)]
      exact (div_le_iff₀ ht).2 (hbound (p x).1 hgx (p x).2.1.1 (p x).2.1.2 hx.1 hx.2.1 (p x).2.2.1 (p x).2.2.2 hx.2.2.1 hx.2.2.2 t ⟨ht.le,ht1.le⟩)
    · exact integrable_const C
    · filter_upwards [hG,hJ0] with x hx hzero
      have hd := (metricSpatialRadialForm_normalized_sqrt_det_hasDerivAt_zero
        (p x).1 (p x).2.1.1 (p x).2.1.2 (p x).2.2.1 (p x).2.2.2 hx).hasDerivWithinAt (s := Ici 0)
      have ht := hasDerivWithinAt_iff_tendsto_slope.mp hd
      have hs : Ici (0:ℝ) \ {0} = Ioi 0 := by simp
      change Tendsto (fun t => slope (fun t => J t x) 0 t) _ _ at ht
      simpa only [hs,slope_def_field,sub_zero,hzero] using ht
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hs : Ici (0:ℝ) \ {0} = Ioi 0 := by simp
  rw [hs]
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with t ht ht1
  rw [slope_def_field,sub_zero]
  change (∫ x, (J t x-1)/t ∂μ) = ((∫ x, J t x ∂μ)-(∫ x, J 0 x ∂μ))/t
  rw [integral_div,integral_sub (hJI ⟨ht.le,ht1.le⟩) (integrable_const 1),
    integral_congr_ae hJ0]

end CAT0Fillings
end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_NormalizedDerivative
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings.IntegerChart
open MeasureTheory Set Filter Metric Matrix
open scoped Topology NNReal Matrix.Norms.Elementwise

variable {X : Type*} [MetricSpace X] [CompactSpace X] {k : ℕ} (C : IntegerChart X k)
attribute [local instance] OAI.CAT0Fillings.IntegerChart.instMeasurableSpaceMatrixFinReal_1
local instance instBorelSpaceMatrixFinReal_1_r297a55_1 : BorelSpace (Matrix (Fin k) (Fin k) ℝ) := ⟨rfl⟩
theorem radial_normalized_integral_hasDerivWithinAt_zero
    (p : Euc k → Seminorm ℝ (Euc k)) (hpm : ∀ v, Measurable (fun z => p z v))
    (hp : ∀ᵐ z ∂volume.restrict C.domain,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
      (∀ v, p z v = 0 ↔ v = 0))
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    (μ : Measure (Euc k)) [IsFiniteMeasure μ] (hμ : μ ≪ volume.restrict C.domain) :
    HasDerivWithinAt
      (fun t => ∫ z, C.radialJacobian
        (fun z => polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
        o g t z / Real.sqrt
        (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det ∂μ)
      (∫ z, -((k:ℝ)*C.scalar g z+C.scalar (dist o) z *
        (differentialRow (fderivWithin ℝ (C.scalar (dist o)) C.domain z) ⬝ᵥ
          (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)⁻¹.mulVec
          (differentialRow (fderivWithin ℝ (C.scalar g) C.domain z)))) ∂μ)
      (Ici 0) 0 := by
  obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuous.continuousOn
  let B : ℝ := max 1 (max (K:ℝ) (max M (Metric.diam (univ : Set X))))
  have hB : 1 ≤ B := le_max_left ..
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hK : (K:ℝ) ≤ B := (le_max_left ..).trans (le_max_right ..)
  have hgb : ∀ x, |g x| ≤ B := by
    intro x
    have hm : |g x| ≤ M := by simpa only [Real.norm_eq_abs] using hM x (mem_univ x)
    exact hm.trans ((le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..)))
  have hrb : ∀ x, dist o x ≤ B := by
    intro x
    exact (Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ o) (mem_univ x)).trans
      ((le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..)))
  obtain ⟨L,U,hL,_⟩ := C.bilipschitz
  obtain ⟨R,hR,heR⟩ := (C.scalar_lipschitzOn hL (LipschitzWith.dist_right o)).extend_real
  obtain ⟨G,hG,heG⟩ := (C.scalar_lipschitzOn hL hg).extend_real
  let P (z : Euc k) := polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let q : Euc k → MetricRadialParameters (Fin k) := fun z =>
    (P z,((C.scalar g z,C.scalar (dist o) z),
      (differentialRow (fderiv ℝ R z),differentialRow (fderiv ℝ G z))))
  have hPm : Measurable P := by
    have hh : Measurable (fun z i j => P z i j) :=
      measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
        measurable_polarizationMatrix p (EuclideanSpace.basisFun (Fin k) ℝ).toBasis hpm i j
    have heq : _root_.borel (Fin k → Fin k → ℝ) = MeasurableSpace.pi :=
      BorelSpace.measurable_eq.symm
    change @Measurable (Euc k) (Fin k → Fin k → ℝ) _ (_root_.borel _) P
    rw [heq]
    exact hh
  have hRd : Measurable (fun z => differentialRow (fderiv ℝ R z)) := by
    apply measurable_pi_iff.mpr
    intro i
    simp only [differentialRow]
    fun_prop
  have hGd : Measurable (fun z => differentialRow (fderiv ℝ G z)) := by
    apply measurable_pi_iff.mpr
    intro i
    simp only [differentialRow]
    fun_prop
  have hq : Measurable q := hPm.prodMk
    ((C.measurable_scalar hg).prodMk (C.measurable_scalar (LipschitzWith.dist_right o)) |>.prodMk
      (hRd.prodMk hGd))
  have hRae := ae_fderivWithin_eq_fderiv_extension volume C.borel hR heR
  have hGae := ae_fderivWithin_eq_fderiv_extension volume C.borel hG heG
  have hdata : ∀ᵐ z ∂volume.restrict C.domain,
      |(q z).2.1.1| ≤ B ∧ |(q z).2.1.2| ≤ B ∧
      (∀ v : Fin k → ℝ, ((q z).2.2.1 ⬝ᵥ v)^2 ≤ B^2*(v ⬝ᵥ (q z).1.mulVec v)) ∧
      (∀ v : Fin k → ℝ, ((q z).2.2.2 ⬝ᵥ v)^2 ≤ B^2*(v ⬝ᵥ (q z).1.mulVec v)) := by
    filter_upwards [hp,ae_restrict_mem C.borel,hRae,hGae,
      C.ae_scalar_row_quadratic_bound p hp (LipschitzWith.dist_right o),
      C.ae_scalar_row_quadratic_bound p hp hg] with z hpz hzs hRz hGz hRb hGb
    have hP : (P z).PosDef := polarizationMatrix_posDef _ _ hpz.2.2 hpz.2.1
    have hPr (v : Fin k → ℝ) : 0 ≤ v ⬝ᵥ (P z).mulVec v := hP.posSemidef.dotProduct_mulVec_nonneg v
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [q,C.scalar_eq hzs] using hgb (C.param ⟨z,hzs⟩)
    · simpa only [q,C.scalar_eq hzs,abs_of_nonneg dist_nonneg] using hrb (C.param ⟨z,hzs⟩)
    · intro v
      change (differentialRow (fderiv ℝ R z) ⬝ᵥ v)^2 ≤ B^2*(v ⬝ᵥ (P z).mulVec v)
      rw [hRz] at hRb
      have hh := hRb v
      simp only [NNReal.coe_one,one_pow,one_mul] at hh
      exact hh.trans (le_mul_of_one_le_left (hPr v) (by nlinarith))
    · intro v
      change (differentialRow (fderiv ℝ G z) ⬝ᵥ v)^2 ≤ B^2*(v ⬝ᵥ (P z).mulVec v)
      rw [hGz] at hGb
      exact (hGb v).trans (mul_le_mul_of_nonneg_right
        ((sq_le_sq₀ K.coe_nonneg hB0).2 hK) (hPr v))
  have hpos : ∀ᵐ z ∂μ, (q z).1.PosDef := by
    filter_upwards [hμ.ae_le hp] with z hz
    exact polarizationMatrix_posDef _ _ hz.2.2 hz.2.1
  have hh := integrated_intrinsicRadialJacobian_hasDerivWithinAt_zero μ q hq hB0
    (hμ.ae_le hdata) hpos
  convert hh using 1
  · funext t
    apply integral_congr_ae
    filter_upwards [hμ.ae_le hRae,hμ.ae_le hGae] with z hRz hGz
    simp only [radialJacobian,q,P,hRz,hGz]
  · apply integral_congr_ae
    filter_upwards [hμ.ae_le hRae,hμ.ae_le hGae] with z hRz hGz
    simp only [q,P,hRz,hGz,Fintype.card_fin]
end CAT0Fillings.IntegerChart

namespace CAT0Fillings.IntegerChart
open MeasureTheory Set Filter Metric Matrix
open scoped Topology NNReal Matrix.Norms.Elementwise

variable {X : Type*} [MetricSpace X] [CompactSpace X] {k : ℕ} (C : IntegerChart X k)

theorem radial_weighted_integral_hasDerivWithinAt_zero
    (p : Euc k → Seminorm ℝ (Euc k)) (hpm : ∀ v, Measurable (fun z => p z v))
    (hp : ∀ᵐ z ∂volume.restrict C.domain,
      (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        C.domain C.param (p z) ⟨z,hz⟩) ∧
      (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
      (∀ v, p z v = 0 ↔ v = 0))
    (hρ : Integrable (fun z => |(C.multiplicity z : ℝ)| * Real.sqrt
      (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det)
      (volume.restrict C.domain))
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    HasDerivWithinAt
      (fun t => ∫ z, |(C.multiplicity z : ℝ)| * C.radialJacobian
        (fun z => polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
        o g t z ∂volume.restrict C.domain)
      (∫ z, (|(C.multiplicity z : ℝ)| * Real.sqrt
        (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det) *
        -((k:ℝ)*C.scalar g z+C.scalar (dist o) z *
        (differentialRow (fderivWithin ℝ (C.scalar (dist o)) C.domain z) ⬝ᵥ
          (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)⁻¹.mulVec
          (differentialRow (fderivWithin ℝ (C.scalar g) C.domain z))))
        ∂volume.restrict C.domain)
      (Ici 0) 0 := by
  let ν := volume.restrict C.domain
  let ρ : Euc k → ℝ := fun z => |(C.multiplicity z : ℝ)| * Real.sqrt
    (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det
  let μ := ν.withDensity (fun z => ENNReal.ofReal (ρ z))
  have hρ0 (z) : 0 ≤ ρ z := mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  let : IsFiniteMeasure μ := isFiniteMeasure_withDensity_ofReal hρ.hasFiniteIntegral
  have hμ : μ ≪ ν := withDensity_absolutelyContinuous _ _
  have hh := C.radial_normalized_integral_hasDerivWithinAt_zero p hpm hp o hg μ hμ
  have hchange (f : Euc k → ℝ) : (∫ z, f z ∂μ) = ∫ z, ρ z*f z ∂ν := by
    rw [integral_withDensity_eq_integral_toReal_smul₀
      hρ.aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    change (∫ z, (ENNReal.ofReal (ρ z)).toReal • f z ∂ν) = _
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      change (ENNReal.ofReal (ρ z)).toReal • f z = ρ z * f z
      rw [ENNReal.toReal_ofReal (hρ0 z),smul_eq_mul]
  convert hh using 1
  · funext t
    rw [hchange]
    apply integral_congr_ae
    filter_upwards [hp] with z hz
    have hs : Real.sqrt
        (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (polarizationMatrix_posDef _ _ hz.2.2 hz.2.1).det_pos)
    dsimp only [ρ]
    field_simp
  · exact (hchange _).symm
end CAT0Fillings.IntegerChart

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_SeriesDerivative
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open MeasureTheory Set Filter Metric Matrix
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] {k : ℕ}
theorem uniform_chart_radialJacobian_slope
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {B : ℝ} (hB : 1 ≤ B) (hK : (K:ℝ) ≤ B)
    (hgb : ∀ x, |g x| ≤ B) (hrb : ∀ x, dist o x ≤ B) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (C : IntegerChart X k) (p : Euc k → Seminorm ℝ (Euc k)),
      (∀ᵐ z ∂volume.restrict C.domain,
        (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
          C.domain C.param (p z) ⟨z,hz⟩) ∧
        (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
        (∀ v, p z v = 0 ↔ v = 0)) →
      ∀ t ∈ Icc (0:ℝ) 1, ∀ᵐ z ∂volume.restrict C.domain,
        |C.radialJacobian
          (fun z => polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
          o g t z - Real.sqrt (polarizationMatrix (p z)
            (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det| ≤ A*t*Real.sqrt
            (polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det := by
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  obtain ⟨A,hA,hbound⟩ := metricSpatialRadialForm_intrinsic_uniform_slope_bound (ι := Fin k) B hB0
  refine ⟨A,hA,?_⟩
  intro C p hp t ht
  filter_upwards [hp,ae_restrict_mem C.borel,
    C.ae_scalar_row_quadratic_bound p hp (LipschitzWith.dist_right o),
    C.ae_scalar_row_quadratic_bound p hp hg] with z hpz hzs hR hG
  let P := polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  have hP : P.PosDef := polarizationMatrix_posDef _ _ hpz.2.2 hpz.2.1
  have hPr (v : Fin k → ℝ) : 0 ≤ v ⬝ᵥ P.mulVec v := hP.posSemidef.dotProduct_mulVec_nonneg v
  have hα : ∀ v : Fin k → ℝ,
      (differentialRow (fderivWithin ℝ (C.scalar (dist o)) C.domain z) ⬝ᵥ v)^2 ≤
        B^2*(v ⬝ᵥ P.mulVec v) := by
    intro v
    have hh := hR v
    simp only [NNReal.coe_one,one_pow,one_mul] at hh
    exact hh.trans (le_mul_of_one_le_left (hPr v) (by nlinarith))
  have hγ : ∀ v : Fin k → ℝ,
      (differentialRow (fderivWithin ℝ (C.scalar g) C.domain z) ⬝ᵥ v)^2 ≤
        B^2*(v ⬝ᵥ P.mulVec v) := by
    intro v
    exact (hG v).trans (mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ K.coe_nonneg hB0).2 hK) (hPr v))
  have hh := hbound P hP (C.scalar g z) (C.scalar (dist o) z)
    (by simpa only [C.scalar_eq hzs] using hgb (C.param ⟨z,hzs⟩))
    (by simpa only [C.scalar_eq hzs,abs_of_nonneg dist_nonneg] using hrb (C.param ⟨z,hzs⟩))
    _ _ hα hγ t ht
  have hpos : 0 < Real.sqrt P.det := Real.sqrt_pos.2 hP.det_pos
  change |C.radialJacobian (fun z => polarizationMatrix (p z)
    (EuclideanSpace.basisFun (Fin k) ℝ).toBasis) o g t z / Real.sqrt P.det-1| ≤ A*t at hh
  have he (r s : ℝ) (hs : s ≠ 0) : r/s-1 = (r-s)/s := by field_simp
  rw [he _ _ hpos.ne',abs_div,abs_of_pos hpos] at hh
  exact (div_le_iff₀ hpos).1 hh
end CAT0Fillings

namespace CAT0Fillings
open Set Filter
open scoped Topology

theorem hasDerivWithinAt_tsum_of_uniform_right_slope
    {ι : Type*} (F : ι → ℝ → ℝ) (d b : ι → ℝ)
    (h0 : Summable (fun i => F i 0)) (hb : Summable b)
    (hd : ∀ i, HasDerivWithinAt (F i) (d i) (Ici 0) 0)
    (hbound : ∀ t ∈ Icc (0:ℝ) 1, ∀ i, |F i t-F i 0| ≤ t*b i) :
    Summable d ∧ HasDerivWithinAt (fun t => ∑' i, F i t) (∑' i, d i) (Ici 0) 0 := by
  have hs : Ici (0:ℝ) \ {0} = Ioi 0 := by simp
  have hlim (i) : Tendsto (fun t => (F i t-F i 0)/t) (𝓝[>] (0:ℝ)) (𝓝 (d i)) := by
    have h := hasDerivWithinAt_iff_tendsto_slope.mp (hd i)
    change Tendsto (fun t => slope (F i) 0 t) _ _ at h
    simpa only [hs,slope_def_field,sub_zero] using h
  have hevent : ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ i, ‖(F i t-F i 0)/t‖ ≤ b i := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with t ht ht1
    intro i
    rw [Real.norm_eq_abs,abs_div,abs_of_pos (show 0<t from ht)]
    apply (div_le_iff₀ ht).2
    simpa only [mul_comm] using hbound t ⟨ht.le,ht1.le⟩ i
  have hdi (i) : ‖d i‖ ≤ b i :=
    le_of_tendsto (hlim i |>.norm) (hevent.mono fun t ht => ht i)
  refine ⟨hb.of_norm_bounded hdi,?_⟩
  have ht := tendsto_tsum_of_dominated_convergence hb hlim hevent
  rw [hasDerivWithinAt_iff_tendsto_slope,hs]
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds] with t ht ht1
  have hdiff : Summable (fun i => F i t-F i 0) :=
    (hb.mul_left t).of_norm_bounded fun i => by
      simpa only [Real.norm_eq_abs] using hbound t ⟨ht.le,ht1.le⟩ i
  have hFt : Summable (fun i => F i t) := by
    convert hdiff.add h0 using 1
    all_goals try with_reducible_and_instances rfl
    funext i
    ring
  rw [slope_def_field,sub_zero,tsum_div_const,hFt.tsum_sub h0]
end CAT0Fillings
namespace CAT0Fillings
open MeasureTheory Set Filter Metric Matrix
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X] {k : ℕ}

theorem countable_chart_radial_first_variation
    (C : ℕ → IntegerChart X k) (p : ℕ → Euc k → Seminorm ℝ (Euc k))
    (hpm : ∀ i v, Measurable (fun z => p i z v))
    (hp : ∀ i, ∀ᵐ z ∂volume.restrict (C i).domain,
      (∀ hz : z ∈ (C i).domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
        (C i).domain (C i).param (p i z) ⟨z,hz⟩) ∧
      (∀ u v, p i z (u+v)^2+p i z (u-v)^2 = 2*p i z u^2+2*p i z v^2) ∧
      (∀ v, p i z v = 0 ↔ v = 0))
    (hρ : ∀ i, Integrable (fun z => |((C i).multiplicity z : ℝ)| * Real.sqrt
      (polarizationMatrix (p i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det)
      (volume.restrict (C i).domain))
    (hsum : Summable (fun i => ∫ z, |((C i).multiplicity z : ℝ)| * Real.sqrt
      (polarizationMatrix (p i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det
      ∂volume.restrict (C i).domain))
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    let d : ℕ → ℝ := fun i => ∫ z,
      (|((C i).multiplicity z : ℝ)| * Real.sqrt
        (polarizationMatrix (p i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det) *
      -((k:ℝ)*(C i).scalar g z+(C i).scalar (dist o) z *
        (differentialRow (fderivWithin ℝ ((C i).scalar (dist o)) (C i).domain z) ⬝ᵥ
          (polarizationMatrix (p i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)⁻¹.mulVec
          (differentialRow (fderivWithin ℝ ((C i).scalar g) (C i).domain z))))
      ∂volume.restrict (C i).domain
    Summable d ∧ HasDerivWithinAt
      (fun t => ∑' i, ∫ z, |((C i).multiplicity z : ℝ)| * (C i).radialJacobian
        (fun z => polarizationMatrix (p i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
        o g t z ∂volume.restrict (C i).domain) (∑' i, d i) (Ici 0) 0 := by
  dsimp only
  let P (i : ℕ) (z : Euc k) :=
    polarizationMatrix (p i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let ρ (i : ℕ) (z : Euc k) := |((C i).multiplicity z : ℝ)| * Real.sqrt (P i z).det
  let F (i : ℕ) (t : ℝ) := ∫ z, |((C i).multiplicity z : ℝ)| *
    (C i).radialJacobian (P i) o g t z ∂volume.restrict (C i).domain
  have hF0 (i) : F i 0 = ∫ z, ρ i z ∂volume.restrict (C i).domain := by
    simp only [F,ρ,IntegerChart.radialJacobian,metricSpatialRadialForm]
    simp
  obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuous.continuousOn
  let B : ℝ := max 1 (max (K:ℝ) (max M (Metric.diam (univ : Set X))))
  have hB : 1 ≤ B := le_max_left ..
  have hK : (K:ℝ) ≤ B := (le_max_left ..).trans (le_max_right ..)
  have hgb : ∀ x, |g x| ≤ B := by
    intro x
    have hm : |g x| ≤ M := by simpa only [Real.norm_eq_abs] using hM x (mem_univ x)
    exact hm.trans ((le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..)))
  have hrb : ∀ x, dist o x ≤ B := by
    intro x
    exact (Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ o) (mem_univ x)).trans
      ((le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..)))
  obtain ⟨A,_,hbound⟩ := uniform_chart_radialJacobian_slope (k := k) o hg hB hK hgb hrb
  apply hasDerivWithinAt_tsum_of_uniform_right_slope F _
    (fun i => A*(∫ z, ρ i z ∂volume.restrict (C i).domain))
    (by simpa only [hF0,ρ,P] using hsum) (hsum.mul_left A)
  · intro i
    exact (C i).radial_weighted_integral_hasDerivWithinAt_zero
      (p i) (hpm i) (hp i) (hρ i) o hg
  · intro t ht i
    have hIt := (C i).integrable_radialJacobian (p i) (hpm i) (hp i) (hρ i)
      o hg hB hK hgb hrb ht
    rw [hF0]
    change |(∫ z, |((C i).multiplicity z : ℝ)| * (C i).radialJacobian (P i) o g t z
      ∂volume.restrict (C i).domain) - (∫ z, ρ i z ∂volume.restrict (C i).domain)| ≤ _
    rw [←integral_sub hIt (hρ i)]
    calc
      _ ≤ ∫ z, |(|((C i).multiplicity z : ℝ)| * (C i).radialJacobian (P i) o g t z - ρ i z)|
          ∂volume.restrict (C i).domain := by
            simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
              (fun z => |((C i).multiplicity z : ℝ)| * (C i).radialJacobian (P i) o g t z - ρ i z)
      _ ≤ ∫ z, (t*A)*ρ i z ∂volume.restrict (C i).domain := by
        apply integral_mono_ae (hIt.sub (hρ i)).abs ((hρ i).const_mul (t*A))
        filter_upwards [hbound (C i) (p i) (hp i) t ht] with z hz
        change |(|((C i).multiplicity z : ℝ)| * (C i).radialJacobian (P i) o g t z -
          |((C i).multiplicity z : ℝ)| * Real.sqrt (P i z).det)| ≤
          t*A*(|((C i).multiplicity z : ℝ)| * Real.sqrt (P i z).det)
        rw [←mul_sub,abs_mul,abs_abs]
        calc
          _ ≤ |((C i).multiplicity z : ℝ)| * (A*t*Real.sqrt (P i z).det) :=
            mul_le_mul_of_nonneg_left hz (abs_nonneg _)
          _ = (t*A)*(|((C i).multiplicity z : ℝ)| * Real.sqrt (P i z).det) := by ring
      _ = _ := by rw [integral_const_mul]; ring
end CAT0Fillings
end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_WholeMass
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open MeasureTheory Set Filter Metric Matrix
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] {k : ℕ}
theorem uniform_chart_radialJacobian_majorant
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {B : ℝ} (hB : 1 ≤ B) (hK : (K:ℝ) ≤ B)
    (hgb : ∀ x, |g x| ≤ B) (hrb : ∀ x, dist o x ≤ B) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (C : IntegerChart X k) (p : Euc k → Seminorm ℝ (Euc k)),
      (∀ᵐ z ∂volume.restrict C.domain,
        (∀ hz : z ∈ C.domain, MetricDifferentiation.HasCenteredMetricDifferentialWithin
          C.domain C.param (p z) ⟨z,hz⟩) ∧
        (∀ u v, p z (u+v)^2+p z (u-v)^2 = 2*p z u^2+2*p z v^2) ∧
        (∀ v, p z v = 0 ↔ v = 0)) →
      ∀ t ∈ Icc (0:ℝ) 1, ∀ᵐ z ∂volume.restrict C.domain,
        C.radialJacobian
          (fun z => polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis)
          o g t z ≤ A*Real.sqrt (polarizationMatrix (p z)
            (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det := by
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  obtain ⟨A,hA,hbound⟩ := metricSpatialRadialForm_intrinsic_uniform_slope_bound (ι := Fin k) B hB0
  refine ⟨A+1,by linarith,?_⟩
  intro C p hp t ht
  filter_upwards [hp,ae_restrict_mem C.borel,
    C.ae_scalar_row_quadratic_bound p hp (LipschitzWith.dist_right o),
    C.ae_scalar_row_quadratic_bound p hp hg] with z hpz hzs hR hG
  let P := polarizationMatrix (p z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  have hP : P.PosDef := polarizationMatrix_posDef _ _ hpz.2.2 hpz.2.1
  have hPr (v : Fin k → ℝ) : 0 ≤ v ⬝ᵥ P.mulVec v := hP.posSemidef.dotProduct_mulVec_nonneg v
  have hα : ∀ v : Fin k → ℝ,
      (differentialRow (fderivWithin ℝ (C.scalar (dist o)) C.domain z) ⬝ᵥ v)^2 ≤
        B^2*(v ⬝ᵥ P.mulVec v) := by
    intro v
    have hh := hR v
    simp only [NNReal.coe_one,one_pow,one_mul] at hh
    exact hh.trans (le_mul_of_one_le_left (hPr v) (by nlinarith))
  have hγ : ∀ v : Fin k → ℝ,
      (differentialRow (fderivWithin ℝ (C.scalar g) C.domain z) ⬝ᵥ v)^2 ≤
        B^2*(v ⬝ᵥ P.mulVec v) := by
    intro v
    exact (hG v).trans (mul_le_mul_of_nonneg_right
      ((sq_le_sq₀ K.coe_nonneg hB0).2 hK) (hPr v))
  have hh := hbound P hP (C.scalar g z) (C.scalar (dist o) z)
    (by simpa only [C.scalar_eq hzs] using hgb (C.param ⟨z,hzs⟩))
    (by simpa only [C.scalar_eq hzs,abs_of_nonneg dist_nonneg] using hrb (C.param ⟨z,hzs⟩))
    _ _ hα hγ t ht
  have hpos : 0 < Real.sqrt P.det := Real.sqrt_pos.2 hP.det_pos
  apply (div_le_iff₀ hpos).1
  change C.radialJacobian _ o g t z / Real.sqrt P.det ≤ A+1
  have hAt : A*t ≤ A := (mul_le_mul_of_nonneg_left ht.2 hA).trans_eq (mul_one A)
  change |C.radialJacobian (fun z => polarizationMatrix (p z)
    (EuclideanSpace.basisFun (Fin k) ℝ).toBasis) o g t z / Real.sqrt P.det-1| ≤ A*t at hh
  have hs := (le_abs_self _).trans hh
  linarith

end CAT0Fillings

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Minimizers_SpatialVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
open CurrentOperations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}
namespace ChartGeometry
variable {T : Functional X k} {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma spatialMass_zero (o : X) (g : X → ℝ) : q.spatialMass o g 0 = mass T := by
  rw [q.density_mass]
  apply tsum_congr
  intro i
  simp only [density,IntegerChart.radialJacobian,metricSpatialRadialForm]
  simp

lemma spatialMass_first_variation (o : X) {g : X → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) :
    Summable (q.radialVariationChart o g) ∧
    HasDerivWithinAt (q.spatialMass o g) (-q.radialVariation o g) (Ici 0) 0 := by
  have hh := countable_chart_radial_first_variation q.chart q.field q.measurable q.differential
    q.integrable q.density_summable o hg
  dsimp only at hh
  simp_rw [mul_neg,integral_neg,tsum_neg] at hh
  refine ⟨?_,hh.2⟩
  have hs := hh.1.neg
  change Summable (fun i => -(-q.radialVariationChart o g i)) at hs
  simpa only [neg_neg] using hs

lemma spatial_push_mass_le
    (seg : X → X → ℝ → X)
    (hseg : ∀ o x a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o x b) = |a-b| *dist o x)
    (hcomp : ∀ o x y a b, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
      dist (seg o x a) (seg o y b)^2 ≤ (a*dist o x-b*dist o y)^2+
        a*b*(dist x y^2-(dist o x-dist o y)^2))
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (htg : ∀ y, 1-t*g y ∈ Icc (0:ℝ) 1) :
    mass (pushCurrent (fun y => seg o y (1-t*g y)) T) ≤ q.spatialMass o g t := by
  obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuous.continuousOn
  let B : ℝ := max 1 (max (K:ℝ) (max M (Metric.diam (univ : Set X))))
  have hB : 1 ≤ B := le_max_left ..
  have hK : (K:ℝ) ≤ B := (le_max_left ..).trans (le_max_right ..)
  have hgb : ∀ x, |g x| ≤ B := by
    intro x
    have hm : |g x| ≤ M := by simpa only [Real.norm_eq_abs] using hM x (mem_univ x)
    exact hm.trans ((le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..)))
  have hrb : ∀ x, dist o x ≤ B := by
    intro x
    exact (Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ o) (mem_univ x)).trans
      ((le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..)))
  obtain ⟨A,hA,hbound⟩ := uniform_chart_radialJacobian_majorant (k := k) o hg hB hK hgb hrb
  let I (i : ℕ) : ℝ := ∫ z, |((q.chart i).multiplicity z : ℝ)| *
    (q.chart i).radialJacobian (q.gram i) o g t z ∂volume.restrict (q.chart i).domain
  have hrad (i : ℕ) : Integrable (fun z => |((q.chart i).multiplicity z : ℝ)| *
      (q.chart i).radialJacobian (q.gram i) o g t z) (volume.restrict (q.chart i).domain) :=
    (q.chart i).integrable_radialJacobian (q.field i) (q.measurable i) (q.differential i)
      (q.integrable i) o hg hB hK hgb hrb ht
  have hI0 (i : ℕ) : 0 ≤ I i := integral_nonneg fun z =>
    mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hIle (i : ℕ) : I i ≤ A*mass (q.chart i).action := by
    rw [q.chart_mass,←integral_const_mul]
    apply integral_mono_ae (hrad i) ((q.integrable i).const_mul A)
    filter_upwards [hbound (q.chart i) (q.field i) (q.differential i) t ht] with z hz
    calc
      _ ≤ |((q.chart i).multiplicity z : ℝ)| *(A*Real.sqrt (q.gram i z).det) :=
        mul_le_mul_of_nonneg_left hz (abs_nonneg _)
      _ = _ := by dsimp only [gram]; ring
  have hIsum : Summable I := (q.summable.mul_left A).of_nonneg_of_le hI0 hIle
  obtain ⟨L,hf⟩ := radial_lipschitzWith seg hseg hcomp o hg t htg
  let f : X → X := fun y => seg o y (1-t*g y)
  have hpush (i : ℕ) : IsMetricCurrent (pushCurrent f (q.chart i).action) :=
    pushCurrent_isMetricCurrent (q.chart i).action_isMetricCurrent hf
  have hpushle (i : ℕ) : mass (pushCurrent f (q.chart i).action) ≤ I i :=
    (q.chart i).radial_push_mass_le seg hcomp o g hg t htg hf (q.field i) (q.differential i) (hrad i)
  have hpushsum : Summable (fun i => mass (pushCurrent f (q.chart i).action)) :=
    hIsum.of_nonneg_of_le (fun i => mass_nonneg _) hpushle
  have hpusheq : pushCurrent f T = fun b π => ∑' i, pushCurrent f (q.chart i).action b π := by
    funext b π
    by_cases hab : Admissible b π
    · simp only [pushCurrent_apply _ _ hab]
      exact q.action _ _
    · simp only [pushCurrent,ite_eq_right hab,tsum_zero]
  change mass (pushCurrent f T) ≤ ∑' i, I i
  rw [hpusheq]
  exact (mass_tsum_le hpush hpushsum).trans (hpushsum.tsum_le_tsum hpushle hIsum)

end ChartGeometry
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_ClosedInequality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings
open CurrentOperations Foundations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem radial_inequality_of_extremal_oai (hX : IsCAT0 X) {k : ℕ}
    {T : Functional X (k+1)} (hT : IsIntegral (k+1) T) (hz : boundarySucc T = 0)
    (q : ChartGeometry hT.1) {c p : ℝ} (hc : 0 ≤ c) (hp : 0 ≤ p)
    (hm : 0 < mass T)
    (hext : ∀ B : Functional X (k+1), IsIntegral (k+1) B → boundarySucc B = 0 →
      c*((mass T)^p-(mass B)^p) ≤ fillingVolume (T-B))
    (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1) :
    c*p*(mass T)^(p-1)*q.radialVariation o g ≤ q.sweptMass o g := by
  obtain ⟨seg,hends,hseg,hcomp⟩ := hX
  have hbound (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      c*((mass T)^p-(q.spatialMass o g t)^p) ≤ t*q.sweptMass o g := by
    have htg (y : X) : 1-t*g y ∈ Icc (0:ℝ) 1 := by
      have hy := hg0 y
      have hy' := hg1 y
      constructor
      · have hh := mul_le_mul_of_nonneg_left hy' ht.1
        nlinarith [ht.2]
      · exact sub_le_self _ (mul_nonneg ht.1 hy)
    obtain ⟨L,hf⟩ := radial_lipschitzWith seg hseg hcomp o hg t htg
    let B := pushCurrent (fun y => seg o y (1-t*g y)) T
    have hBi : IsIntegral (k+1) B := integral_push hT hf
    have hBz : boundarySucc B = 0 := pushCurrent_cycle hz hf
    have hg' : LipschitzWith (Real.nnabs t*K) (fun y => t*g y) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [Real.dist_eq,←mul_sub,abs_mul,NNReal.coe_mul,Real.coe_nnabs]
      exact (mul_le_mul_of_nonneg_left (hg.dist_le_mul x y) (abs_nonneg t)).trans_eq (mul_assoc _ _ _).symm
    have hg'0 : ∀ y, 0 ≤ t*g y := fun y => mul_nonneg ht.1 (hg0 y)
    have hg'1 : ∀ y, t*g y ≤ 1 := fun y => by
      exact (mul_le_mul_of_nonneg_left (hg1 y) ht.1).trans (by simpa using ht.2)
    obtain ⟨S,hS,hSb,hSm⟩ := exists_swept_current hT hz q seg hseg hcomp
      (fun o y => (hends o y).2) o hg' hg'0 hg'1
    have hNS : IsIntegral (k+2) (0-S) := (isIntegral_zero (X := X) (k+2)).sub hS
    have hbNS : boundarySucc (0-S) = T-B := by
      have hzero : boundarySucc (0 : Functional X (k+2)) = 0 := by
        funext b π; simp [boundarySucc]
      rw [boundarySucc_sub,hzero,hSb]
      dsimp only [B]
      abel
    calc
      c*((mass T)^p-(q.spatialMass o g t)^p) ≤ c*((mass T)^p-(mass B)^p) := by
        apply mul_le_mul_of_nonneg_left _ hc
        apply sub_le_sub_left
        exact Real.rpow_le_rpow (mass_nonneg B) (q.spatial_push_mass_le seg hseg hcomp o hg ht htg) hp
      _ ≤ fillingVolume (T-B) := hext B hBi hBz
      _ ≤ mass (0-S) := fillingVolume_le hNS hbNS
      _ = mass S := by simp only [zero_sub,mass_neg]
      _ ≤ q.sweptMass o (fun y => t*g y) := hSm
      _ = t*q.sweptMass o g := q.sweptMass_const_mul o g t
  let F : ℝ → ℝ := fun t => c*((mass T)^p-(q.spatialMass o g t)^p)-t*q.sweptMass o g
  have hF0 : F 0 = 0 := by simp only [F,q.spatialMass_zero,sub_self,mul_zero,zero_mul]
  have hFder : HasDerivWithinAt F
      (c*p*(mass T)^(p-1)*q.radialVariation o g-q.sweptMass o g) (Ici 0) 0 := by
    have hh := (q.spatialMass_first_variation o hg).2.rpow_const (p := p)
      (Or.inl (by rw [q.spatialMass_zero]; exact hm.ne'))
    have hd := (((hasDerivWithinAt_const (0:ℝ) (Ici 0) ((mass T)^p)).sub hh).const_mul c).sub
      ((hasDerivWithinAt_id (0:ℝ) (Ici 0)).mul_const (q.sweptMass o g))
    convert! hd using 1
    all_goals try with_reducible_and_instances rfl
    rw [q.spatialMass_zero]; ring
  have hlim : Tendsto (slope F 0) (𝓝[>] (0:ℝ))
      (𝓝 (c*p*(mass T)^(p-1)*q.radialVariation o g-q.sweptMass o g)) :=
    (hasDerivWithinAt_iff_tendsto_slope' (show (0:ℝ) ∉ Ioi 0 by simp)).mp hFder.Ioi_of_Ici
  have hnonpos : ∀ᶠ t in 𝓝[>] (0:ℝ), slope F 0 t ≤ 0 := by
    filter_upwards [self_mem_nhdsWithin,
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (show (0:ℝ)<1 by norm_num))] with t ht ht1
    rw [slope_def_field,hF0,sub_zero,sub_zero]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hbound t ⟨ht.le,ht1.le⟩)) ht.le
  have hh := le_of_tendsto hlim hnonpos
  exact sub_nonpos.mp hh

end CAT0Fillings
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CAT0Fillings.radial_inequality_of_extremal_oai.{u_1} := @OAI.CAT0Fillings.radial_inequality_of_extremal_oai.{u_1}
