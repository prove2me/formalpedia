-- Prove2me | solution 1 for OAI.CAT0Fillings.fillingVolume_le_two
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T03:10:43.703996+00:00
-- url     : https://prove2.me/submissions/c2574599-8abd-4c39-ae3c-06c3917c86c2

import Mathlib
import Definitions.Def_SharpCAT0Filling
import Definitions.Def_OAIQ29C0002
import Theorems.Thm_OAI_CAT0Fillings_Slicing_exists_integral_weak_subsequence
import Theorems.Thm_OAI_CAT0Fillings_exists_filling_mass_eq
import Theorems.Thm_OAI_CAT0Fillings_radial_inequality_of_extremal

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
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_ComponentMass
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
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
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

lemma tendsto_integral_abs_of_l1 {X : Type*} [MeasurableSpace X]
    {μ ν : Measure X} (hν : ν ≤ μ) {f : ℕ → X → ℝ} {b : X → ℝ}
    (hf : ∀ j, Integrable (f j) μ) (hb : Integrable b μ)
    (hlim : Tendsto (fun j => ∫ x, |f j x-b x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, |f j x| ∂ν) atTop (𝓝 (∫ x, |b x| ∂ν)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun j => dist_nonneg) (fun j => ?_) hlim
  rw [Real.dist_eq,←integral_sub ((hf j).mono_measure hν).abs (hb.mono_measure hν).abs]
  calc |∫ x, |f j x|-|b x| ∂ν| ≤ ∫ x, abs (|f j x|-|b x|) ∂ν := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun x => |f j x|-|b x|)
    _ ≤ ∫ x, |f j x-b x| ∂ν :=
        integral_mono_ae (((hf j).mono_measure hν).abs.sub (hb.mono_measure hν).abs).abs
          (((hf j).mono_measure hν).sub (hb.mono_measure hν)).abs
          (Eventually.of_forall fun x => abs_abs_sub_abs_le _ _)
    _ ≤ ∫ x, |f j x-b x| ∂μ :=
        integral_mono_measure hν (Eventually.of_forall fun _ => abs_nonneg _)
          ((hf j).sub hb).abs
end CAT0Fillings

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

section ComponentControls
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  {k : ℕ} {T : Functional X k} {S : ℕ → Functional X k}
  {μ : ℕ → Measure X} [IsFiniteMeasure (Measure.sum μ)]
  {Z : ℕ → Set X}

lemma component_approximation_bound (hS : ∀ i, IsMetricCurrent (S i))
    (hμ : ∀ i, Controls (S i) (μ i))
    (hT : ∀ b π, T b π = ∑' i, S i b π)
    (hZ : ∀ i, MeasurableSet (Z i)) (hd : Pairwise (fun i j => Disjoint (Z i) (Z j)))
    (hc : ∀ i, ∀ᵐ x ∂μ i, x ∈ Z i) (i : ℕ)
    {f b : X → ℝ} (hf : BoundedLip f) (hb : BoundedLip b)
    {π : Fin k → X → ℝ} (hπ : ∀ j, LipschitzWith 1 (π j)) :
    |T f π - S i b π| ≤ ∫ x, |f x - (Z i).indicator b x| ∂Measure.sum μ := by
  classical
  have hfi := BorelCoefficients.integrable_boundedLip (Measure.sum μ) hf
  have hbi := (BorelCoefficients.integrable_boundedLip (Measure.sum μ) hb).indicator (hZ i)
  let d : ℕ → ℝ := fun j => S j f π - if j = i then S i b π else 0
  have hbd (j : ℕ) : |d j| ≤ ∫ x, |f x-(Z i).indicator b x| ∂μ j := by
    by_cases hji : j = i
    · subst j
      have heq : S i (fun x => f x - b x) π = S i f π - S i b π := by
        simpa only [one_mul, neg_one_mul, sub_eq_add_neg] using
          (hS i).linearFirst f b π 1 (-1) hf hb (fun l => ⟨1,hπ l⟩)
      have hbound := hμ i (fun x => f x-b x) π (by simpa only [neg_one_mul, sub_eq_add_neg] using hf.add (hb.const_mul (-1))) hπ
      rw [heq] at hbound
      change |S i f π - if i = i then S i b π else 0| ≤ _
      rw [ite_eq_left rfl]
      apply hbound.trans_eq
      apply integral_congr_ae
      filter_upwards [hc i] with x hx
      rw [indicator_of_mem hx]
    · have hbound := hμ j f π hf hπ
      change |S j f π - if j = i then S i b π else 0| ≤ _
      rw [ite_eq_right hji,sub_zero]
      apply hbound.trans_eq
      apply integral_congr_ae
      filter_upwards [hc j] with x hx
      have hxi : x ∉ Z i := fun hxi => Set.disjoint_left.mp (hd hji) hx hxi
      rw [indicator_of_notMem hxi,sub_zero]
  have heint : Integrable (fun x => |f x-(Z i).indicator b x|) (Measure.sum μ) :=
    (hfi.sub hbi).abs
  have he : Summable (fun j => ∫ x, |f x-(Z i).indicator b x| ∂μ j) := by
    simpa only [Real.norm_eq_abs,abs_abs] using heint.summable_integral
  have hdS : Summable d := he.of_norm_bounded (fun j => by simpa only [Real.norm_eq_abs] using hbd j)
  have hfS : Summable (fun j => S j f π) := by
    have hfs : Summable (fun j => ∫ x, |f x| ∂μ j) := by
      simpa only [Real.norm_eq_abs,abs_abs] using hfi.abs.summable_integral
    exact hfs.of_norm_bounded (fun j => by simpa only [Real.norm_eq_abs] using hμ j f π hf hπ)
  have hsum : ∑' j, d j = T f π - S i b π := by
    rw [hT f π]
    dsimp only [d]
    rw [hfS.tsum_sub (hasSum_ite_eq i (S i b π)).summable,tsum_ite_eq]
  rw [←hsum,integral_sum_measure heint]
  calc |∑' j, d j| ≤ ∑' j, |d j| := by
        simpa only [Real.norm_eq_abs] using (norm_tsum_le_tsum_norm (f := d) hdS.norm)
    _ ≤ ∑' j, ∫ x, |f x-(Z i).indicator b x| ∂μ j := hdS.abs.tsum_le_tsum hbd he

lemma controls_component_restrict (hS : ∀ i, IsMetricCurrent (S i))
    (hμ : ∀ i, Controls (S i) (μ i))
    (hT : ∀ b π, T b π = ∑' i, S i b π)
    (hZ : ∀ i, MeasurableSet (Z i)) (hd : Pairwise (fun i j => Disjoint (Z i) (Z j)))
    (hc : ∀ i, ∀ᵐ x ∂μ i, x ∈ Z i)
    {ν : Measure X} [IsFiniteMeasure ν] (hν : Controls T ν) (i : ℕ) :
    Controls (S i) (ν.restrict (Z i)) := by
  intro b π hb hπ
  let η := ν + Measure.sum μ
  have hbη : Integrable ((Z i).indicator b) η :=
    (BorelCoefficients.integrable_boundedLip η hb).indicator (hZ i)
  obtain ⟨f,hf⟩ := BorelCoefficients.exists_lipschitz_approximation η hbη
  have hfi (j : ℕ) : Integrable (f j).val η :=
    BorelCoefficients.integrable_boundedLip η (f j).property
  have hleμ : Measure.sum μ ≤ η := Measure.le_add_left le_rfl
  have hleν : ν ≤ η := Measure.le_add_right le_rfl
  have hlim : Tendsto (fun j => T (f j).val π) atTop (𝓝 (S i b π)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun j => dist_nonneg) (fun j => ?_) hf
    rw [Real.dist_eq]
    apply (component_approximation_bound hS hμ hT hZ hd hc i (f j).property hb hπ).trans
    exact integral_mono_measure hleμ (Eventually.of_forall fun _ => abs_nonneg _)
      ((hfi j).sub hbη).abs
  have hlimν := tendsto_integral_abs_of_l1 hleν hfi hbη hf
  have hle := le_of_tendsto_of_tendsto hlim.abs hlimν
    (Eventually.of_forall fun j => hν _ π (f j).property hπ)
  apply hle.trans_eq
  rw [←integral_indicator (hZ i)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ Z i <;> simp [hx]

end ComponentControls
end CAT0Fillings

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

lemma sum_measure_le_of_component_minimal
    {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {k : ℕ} {T : Functional X k} {S : ℕ → Functional X k}
    {μ : ℕ → Measure X} [IsFiniteMeasure (Measure.sum μ)]
    {Z : ℕ → Set X}
    (hS : ∀ i, IsMetricCurrent (S i)) (hμ : ∀ i, Controls (S i) (μ i))
    (hmin : ∀ i (ν : Measure X), IsFiniteMeasure ν → Controls (S i) ν → μ i ≤ ν)
    (hT : ∀ b π, T b π = ∑' i, S i b π)
    (hZ : ∀ i, MeasurableSet (Z i)) (hd : Pairwise (fun i j => Disjoint (Z i) (Z j)))
    (hc : ∀ i, ∀ᵐ x ∂μ i, x ∈ Z i)
    {ν : Measure X} [IsFiniteMeasure ν] (hν : Controls T ν) : Measure.sum μ ≤ ν := by
  have hle (i) : μ i ≤ ν.restrict (Z i) :=
    hmin i _ inferInstance (controls_component_restrict hS hμ hT hZ hd hc hν i)
  have hsum : Measure.sum μ ≤ Measure.sum (fun i => ν.restrict (Z i)) := by
    apply Measure.le_iff.mpr
    intro B hB
    simp only [Measure.sum_apply _ hB]
    exact ENNReal.tsum_le_tsum (fun i => hle i B)
  rw [←Measure.restrict_iUnion hd hZ] at hsum
  exact hsum.trans Measure.restrict_le_self

end CAT0Fillings

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
-- module Solutions.OAIQ29_C0.CAT0Fillings_Charts_RectifiableMass
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
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace IntegerChart
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)

lemma majorantMeasure_ae_image (J : Euc k → ℝ) :
    ∀ᵐ x ∂C.majorantMeasure J, x ∈ C.image := by
  rw [majorantMeasure,densityPush]
  apply (ae_map_iff C.measurable_paramExtended.aemeasurable C.measurableSet_image).mpr
  have hmem := (withDensity_absolutelyContinuous (volume.restrict C.domain)
    (fun z => ENNReal.ofReal (|(C.multiplicity z : ℝ)| * J z))).ae_le (ae_restrict_mem C.borel)
  filter_upwards [hmem] with z hz
  exact ⟨⟨z,hz⟩,by simp only [paramExtended,dite_eq_left hz]⟩

end IntegerChart

end CAT0Fillings

end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Constants
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings

lemma sphereArea_two : sphereArea 2 = 4*Real.pi := by
  change (2+1:ℝ) * (volume (Metric.ball (0 : Euc 3) 1)).toReal = _
  rw [EuclideanSpace.volume_ball_fin_three]
  rw [ENNReal.ofReal_one,one_pow,one_mul,ENNReal.toReal_ofReal (by positivity)]
  ring
lemma fillingCoefficient_two : fillingCoefficient 2 = 1/(6*Real.sqrt Real.pi) := by
  rw [fillingCoefficient,sphereArea_two]
  norm_num only [Nat.cast_ofNat,Nat.reduceAdd]
  rw [←Real.sqrt_eq_rpow,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
  norm_num
  ring
lemma fillingCoefficient_two_pos : 0 < fillingCoefficient 2 := by
  rw [fillingCoefficient_two]
  positivity
lemma fillingCoefficient_two_sq : 36*Real.pi*(fillingCoefficient 2)^2 = 1 := by
  rw [fillingCoefficient_two,div_pow,one_pow,mul_pow,Real.sq_sqrt Real.pi_pos.le]
  field_simp [Real.pi_ne_zero]
  ring
lemma fillingPower_two : fillingPower 2 = (3:ℝ)/2 := by norm_num [fillingPower]
end CAT0Fillings
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
-- module Solutions.OAIQ29_C0.CAT0Fillings_Prism_MixedMass
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
open Set MeasureTheory Filter
open scoped Topology NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X] in
lemma ae_prism_jacobian_bound_mixed (π : Fin (k+1) → ℝ × X → ℝ)
    (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) (R : ℝ≥0)
    (ht : ∀ i x, LipschitzWith R (fun t : ℝ => π i (t,x))) :
    ∀ᵐ p ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain),
      |C.prism.jacobian π ((Prism.split k).symm p)| ≤
        (R:ℝ) * ∑ i : Fin (k+1), |C.jacobian (fun j x => π (i.succAbove j) (p.1,x)) p.2| := by
  have hpz := Measure.quasiMeasurePreserving_snd (μ := volume.restrict (Icc (0:ℝ) 1)) |>.ae
    (ae_restrict_mem (μ := volume) C.borel)
  filter_upwards [C.ae_prism_jacobian_decompose π hπ,hpz] with p hd hz
  rw [hd,Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  have hl : LipschitzWith R (fun t => C.scalar (fun x => π i (t,x)) p.2) := by
    have heq : (fun t => C.scalar (fun x => π i (t,x)) p.2) =
        (fun t => π i (t,C.param ⟨p.2,hz⟩)) := funext fun _ => C.scalar_eq hz
    rw [heq]
    exact ht i _
  have hD : |deriv (fun t => C.scalar (fun x => π i (t,x)) p.2) p.1| ≤ R := by
    simpa only [Real.norm_eq_abs] using norm_deriv_le_of_lipschitz hl
  simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
  exact mul_le_mul_of_nonneg_right hD (abs_nonneg _)

lemma prism_action_bound_mixed {ν : Measure X} [IsFiniteMeasure ν] (hν : Controls C.action ν)
    (b : ℝ × X → ℝ) (π : Fin (k+1) → ℝ × X → ℝ) (hab : Admissible b π)
    (R : ℝ≥0) (ht : ∀ i x, LipschitzWith R (fun t : ℝ => π i (t,x)))
    (hs : ∀ i t, LipschitzWith 1 (fun x : X => π i (t,x))) :
    |C.prism.action b π| ≤ ((k+1:ℝ)*(R:ℝ)) *
      ∫ p : ℝ × X, |b p| ∂(volume.restrict (Icc (0:ℝ) 1)).prod ν := by
  let F (i : Fin (k+1)) (p : ℝ × Euc k) :=
    |(C.multiplicity p.2 : ℝ) * C.scalar (fun x => b (p.1,x)) p.2 *
      C.jacobian (fun j x => π (i.succAbove j) (p.1,x)) p.2|
  have hF (i : Fin (k+1)) : Integrable (F i)
      ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain)) :=
    (C.integrable_prism_slice b (fun j => π (i.succAbove j))
      ⟨hab.1,fun j => hab.2 _⟩).abs
  have hib : Integrable (fun p : ℝ × X => |b p|)
      ((volume.restrict (Icc (0:ℝ) 1)).prod ν) := by
    obtain ⟨M,hM⟩ := hab.1.2
    exact Integrable.of_bound hab.1.continuous.abs.aestronglyMeasurable M
      (Eventually.of_forall fun p => by simpa using hM p)
  have hinner (i : Fin (k+1)) :
      (∫ p, F i p ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain)) ≤
      ∫ p : ℝ × X, |b p| ∂(volume.restrict (Icc (0:ℝ) 1)).prod ν := by
    rw [integral_prod _ (hF i),integral_prod _ hib]
    apply integral_mono_ae (hF i).integral_prod_left hib.integral_prod_left
    exact Eventually.of_forall fun t => C.chart_abs_integrand_le hν
      (boundedLip_slice hab.1 t) (fun j => hs (i.succAbove j) t)
  rw [C.prism_action_eq b π hab]
  calc
    _ ≤ ∫ p, |(C.multiplicity p.2 : ℝ)*C.scalar (fun x => b (p.1,x)) p.2*
        C.prism.jacobian π ((Prism.split k).symm p)|
        ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain) := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := ((volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain)))
        (fun p => (C.multiplicity p.2 : ℝ)*C.scalar (fun x => b (p.1,x)) p.2*
          C.prism.jacobian π ((Prism.split k).symm p))
    _ ≤ ∫ p, (R:ℝ)*∑ i, F i p
        ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain) := by
      apply integral_mono_ae (C.integrable_prism_formula b π hab).abs
        ((integrable_finsetSum _ fun i _ => hF i).const_mul _)
      filter_upwards [C.ae_prism_jacobian_bound_mixed π hab.2 R ht] with p hp
      have hh := mul_le_mul_of_nonneg_left hp (mul_nonneg
        (abs_nonneg ((C.multiplicity p.2 : ℝ))) (abs_nonneg (C.scalar (fun x => b (p.1,x)) p.2)))
      simpa only [F,abs_mul,←Finset.mul_sum,mul_assoc,mul_comm,mul_left_comm] using hh
    _ = (R:ℝ)*∑ i, ∫ p, F i p
        ∂(volume.restrict (Icc (0:ℝ) 1)).prod (volume.restrict C.domain) := by
      rw [integral_const_mul,integral_finsetSum _ fun i _ => hF i]
    _ ≤ (R:ℝ)*∑ _i : Fin (k+1), ∫ p : ℝ × X, |b p|
        ∂(volume.restrict (Icc (0:ℝ) 1)).prod ν :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hinner i) R.coe_nonneg
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin, nsmul_eq_mul]; push_cast; ring

end CAT0Fillings.IntegerChart
end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Prism_ConeMass
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
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
open Set MeasureTheory CurrentOperations MassMeasure
open scoped NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}
lemma IntegerChart.cone_controls (C : IntegerChart X k)
    {f : ℝ × X → X} {L R : ℝ≥0} (hf : LipschitzWith L f)
    (ht : ∀ x, LipschitzWith R (fun t : ℝ => f (t,x)))
    (hs : ∀ t, LipschitzWith 1 (fun x : X => f (t,x))) :
    Controls (pushCurrent f C.prism.action)
      (((k+1:ℝ≥0)*R) • ((volume.restrict (Icc (0:ℝ) 1)).prod (currentMassMeasure C.action_isMetricCurrent)).map f) := by
  intro b π hb hπ
  have hab : Admissible b π := ⟨hb,fun i => ⟨1,hπ i⟩⟩
  rw [pushCurrent_apply _ _ hab,integral_smul_nnreal_measure,
    integral_map hf.continuous.aemeasurable hb.continuous.abs.aestronglyMeasurable]
  have h := C.prism_action_bound_mixed (currentMassMeasure_controls C.action_isMetricCurrent)
    (b ∘ f) (fun i => π i ∘ f) (admissible_comp hab hf) R
    (fun i x => by simpa only [one_mul,Function.comp_def] using (hπ i).comp (ht x))
    (fun i t => by simpa only [one_mul,Function.comp_def] using (hπ i).comp (hs t))
  simpa only [NNReal.smul_def,smul_eq_mul,NNReal.coe_mul,NNReal.coe_add,
    NNReal.coe_natCast,NNReal.coe_one,Function.comp_apply] using h

lemma IntegerChart.mass_cone_le (C : IntegerChart X k)
    {f : ℝ × X → X} {L R : ℝ≥0} (hf : LipschitzWith L f)
    (ht : ∀ x, LipschitzWith R (fun t : ℝ => f (t,x)))
    (hs : ∀ t, LipschitzWith 1 (fun x : X => f (t,x))) :
    mass (pushCurrent f C.prism.action) ≤ (k+1:ℝ)*(R:ℝ)*mass C.action := by
  have hh := mass_le_measure inferInstance (C.cone_controls hf ht hs)
  have he : ((((k+1:ℝ≥0)*R) •
      ((volume.restrict (Icc (0:ℝ) 1)).prod (currentMassMeasure C.action_isMetricCurrent)).map f).real univ) =
      (k+1:ℝ)*(R:ℝ)*mass C.action := by
    rw [measureReal_nnreal_smul_apply]
    simp only [Measure.real,Measure.map_apply hf.continuous.measurable MeasurableSet.univ,preimage_univ]
    rw [←Set.univ_prod_univ,Measure.prod_prod,ENNReal.toReal_mul]
    have hv : (volume.restrict (Icc (0:ℝ) 1)) univ = 1 := by simp
    rw [hv,ENNReal.toReal_one,one_mul]
    change (↑((k+1:ℝ≥0)*R):ℝ) * (currentMassMeasure C.action_isMetricCurrent).real univ = _
    rw [currentMassMeasure_total]
    push_cast
    rfl
  exact hh.trans_eq he

lemma mass_prismFamily_cone_le {T : Functional X k} (hT : IsMetricCurrent T)
    (C : ℕ → IntegerChart X k) (hd : Pairwise (fun i j => Disjoint (C i).image (C j).image))
    (hC : ∀ i, IsMetricCurrent (C i).action) (hCS : Summable (fun i => mass (C i).action))
    (heq : ∀ b π, T b π = ∑' i, (C i).action b π)
    {f : ℝ × X → X} {L R : ℝ≥0} (hf : LipschitzWith L f)
    (ht : ∀ x, LipschitzWith R (fun t : ℝ => f (t,x)))
    (hs : ∀ t, LipschitzWith 1 (fun x : X => f (t,x))) :
    mass (pushCurrent f (prismFamily C)) ≤ (k+1:ℝ)*(R:ℝ)*mass T := by
  let S (i : ℕ) := pushCurrent f (C i).prism.action
  have hS (i) : IsMetricCurrent (S i) := pushCurrent_isMetricCurrent (C i).prism.action_isMetricCurrent hf
  have hM (i) : mass (S i) ≤ ((k+1:ℝ)*(R:ℝ))*mass (C i).action := (C i).mass_cone_le hf ht hs
  have hsum : Summable (fun i => mass (S i)) :=
    (hCS.mul_left ((k+1:ℝ)*(R:ℝ))).of_nonneg_of_le (fun i => mass_nonneg _) hM
  have hp : pushCurrent f (prismFamily C) = (fun b π => ∑' i, S i b π) := by
    funext b π
    by_cases hab : Admissible b π
    · simp only [pushCurrent_apply _ _ hab,prismFamily,S]
    · simp only [pushCurrent,ite_eq_right hab,tsum_zero,S]
  rw [hp]
  calc
    _ ≤ ∑' i, mass (S i) := mass_tsum_le hS hsum
    _ ≤ ∑' i, ((k+1:ℝ)*(R:ℝ))*mass (C i).action := hsum.tsum_le_tsum hM (hCS.mul_left _)
    _ = ((k+1:ℝ)*(R:ℝ))*(∑' i, mass (C i).action) := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (chartFamily_mass_sum_le hT C hd hC hCS heq) (by positivity)

end CAT0Fillings

end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Fillings_ConeBound
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
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
open Set
open scoped NNReal

lemma IsCAT0.exists_mixed_contraction {X : Type*} [MetricSpace X]
    (hX : IsCAT0 X) (o : X) (R : ℝ≥0) (hR : ∀ x, dist o x ≤ R) :
    ∃ f : ℝ × X → X, LipschitzWith (1+R) f ∧
      (∀ x, LipschitzWith R (fun t : ℝ => f (t,x))) ∧
      (∀ t, LipschitzWith 1 (fun x : X => f (t,x))) ∧
      (∀ x, f (0,x) = o) ∧ (∀ x, f (1,x) = x) := by
  obtain ⟨s,hs,hseg,hcomp⟩ := hX
  let a : ℝ → Icc (0:ℝ) 1 := projIcc 0 1 (by norm_num)
  have ha : LipschitzWith 1 a := LipschitzWith.projIcc (by norm_num : (0:ℝ) ≤ 1)
  let f : ℝ × X → X := fun p => s o p.2 (a p.1)
  have hspace (t : ℝ) : LipschitzWith 1 (fun x : X => f (t,x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one,one_mul]
    have hh : dist (f (t,x)) (f (t,y)) ≤ (a t).val*dist x y := by
      apply (sq_le_sq₀ dist_nonneg (mul_nonneg (a t).2.1 dist_nonneg)).mp
      calc
        _ ≤ ((a t).val*dist o x-(a t).val*dist o y)^2 +
            (a t).val*(a t).val*(dist x y^2-(dist o x-dist o y)^2) :=
          hcomp o x y (a t) (a t) (a t).2 (a t).2
        _ = _ := by ring
    exact hh.trans (mul_le_of_le_one_left dist_nonneg (a t).2.2)
  have htime (x : X) : LipschitzWith R (fun t : ℝ => f (t,x)) := by
    apply LipschitzWith.of_dist_le_mul
    intro t r
    change dist (s o x (a t)) (s o x (a r)) ≤ _
    rw [hseg o x (a t) (a r) (a t).2 (a r).2]
    have hh : |(a t).val-(a r).val| ≤ dist t r := by
      simpa only [NNReal.coe_one,one_mul,Subtype.dist_eq,Real.dist_eq] using ha.dist_le_mul t r
    calc
      _ ≤ dist t r * (R:ℝ) := mul_le_mul hh (hR x) dist_nonneg dist_nonneg
      _ = _ := mul_comm _ _
  refine ⟨f,?_,htime,hspace,?_,?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro p q
    have h1 : dist (f p) (f (p.1,q.2)) ≤ dist p.2 q.2 := by simpa using (hspace p.1).dist_le_mul p.2 q.2
    have h2 : dist (f (p.1,q.2)) (f q) ≤ (R:ℝ)*dist p.1 q.1 := (htime q.2).dist_le_mul _ _
    calc
      _ ≤ dist p.2 q.2 + (R:ℝ)*dist p.1 q.1 := (dist_triangle _ _ _).trans (add_le_add h1 h2)
      _ ≤ dist p q + (R:ℝ)*dist p q := add_le_add (le_max_right _ _)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) R.coe_nonneg)
      _ = _ := by push_cast; ring
  · intro x
    dsimp [f,a]
    rw [projIcc_of_mem (by norm_num : (0:ℝ) ≤ 1) (show (0:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)]
    exact (hs o x).1
  · intro x
    dsimp [f,a]
    rw [projIcc_of_mem (by norm_num : (0:ℝ) ≤ 1) (show (1:ℝ) ∈ Icc (0:ℝ) 1 by constructor <;> norm_num)]
    exact (hs o x).2
end CAT0Fillings
namespace CAT0Fillings
open Set MeasureTheory CurrentOperations
open scoped NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem IsCAT0.exists_integral_filling_mass_le (hX : IsCAT0 X) {k : ℕ}
    {T : Functional X (k+1)} (hT : IsIntegral (k+1) T) (hz : boundarySucc T = 0)
    (o : X) (R : ℝ≥0) (hR : ∀ x, dist o x ≤ R) :
    ∃ S : Functional X (k+2), IsIntegral (k+2) S ∧ boundarySucc S = T ∧
      mass S ≤ (k+2:ℝ)*(R:ℝ)*mass T := by
  classical
  obtain ⟨f,hf,ht,hs,hf0,hf1⟩ := hX.exists_mixed_contraction o R hR
  let g : ClosedCylinder X → X := f ∘ cylinderEmbed
  have hg : LipschitzWith (1+R) g := by
    simpa only [mul_one] using hf.comp cylinderEmbed_isometry.lipschitz
  let F : ℝ × X → X := g ∘ cylinderClamp
  have hF : LipschitzWith (1+R) F := by simpa only [mul_one] using hg.comp cylinderClamp_lipschitz
  have hFt (x : X) : LipschitzWith R (fun t : ℝ => F (t,x)) := by
    have ha := (LipschitzWith.subtype_val (Icc (0:ℝ) 1)).comp
      (LipschitzWith.projIcc (by norm_num : (0:ℝ) ≤ 1))
    simpa only [mul_one,Function.comp_def,F,g,cylinderEmbed,cylinderClamp] using (ht x).comp ha
  have hFs (t : ℝ) : LipschitzWith 1 (fun x : X => F (t,x)) := by
    dsimp only [F,g,cylinderEmbed,cylinderClamp,Function.comp_def]
    exact hs _
  let : Nonempty (ClosedCylinder X) := ⟨(⟨0,by constructor <;> norm_num⟩,o)⟩
  obtain ⟨C,hd,hC,hCS,heq⟩ := hT.2.1
  let S := pushCurrent g (closedPrismFamily C)
  have hb : boundarySucc S = T := by
    funext b π
    by_cases hab : Admissible b π
    · dsimp [S]
      rw [pushCurrent_boundarySucc _ hg,pushCurrent_apply _ _ hab,
        closedPrismFamily_boundary_cycle hT.1 hT.2.1 hz C hCS heq _ _
          (admissible_comp hab hg)]
      simp only [Function.comp_apply,g,cylinderEmbed,hf0,hf1]
      have hz' : T (fun _ => b o) (fun j _ => π j o) = 0 :=
        hT.1.eq_zero_of_const_coord
          ⟨BoundedLip.const _,fun j => ⟨0,LipschitzWith.const _⟩⟩ 0 (π 0 o) (fun _ => rfl)
      rw [hz',sub_zero]
    · simp only [boundarySucc,ite_eq_right hab,hT.1.offDomain b π hab]
  refine ⟨S,⟨pushCurrent_isMetricCurrent (closedPrismFamily_current C hCS) hg,
    integerRectifiable_push (closedPrismFamily_rectifiable C hd hCS) hg,
    hb ▸ hT.1,hb ▸ hT.2.1⟩,hb,?_⟩
  have hseq : S = pushCurrent F (prismFamily C) := (pushCurrent_comp hg).symm
  rw [hseq]
  convert mass_prismFamily_cone_le hT.1 C hd hC hCS heq hF hFt hFs using 1
  all_goals try with_reducible_and_instances rfl
  push_cast
  ring

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
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
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
open Set MeasureTheory CurrentOperations
open scoped NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]
theorem IsCAT0.exists_integral_filling_diam (hX : IsCAT0 X) {k : ℕ}
    {T : Functional X (k+1)} (hT : IsIntegral (k+1) T) (hz : boundarySucc T = 0) :
    ∃ S : Functional X (k+2), IsIntegral (k+2) S ∧ boundarySucc S = T ∧
      mass S ≤ (k+2:ℝ)*Metric.diam (univ : Set X)*mass T := by
  let o : X := Classical.choice inferInstance
  let R : ℝ≥0 := ⟨Metric.diam (univ : Set X),Metric.diam_nonneg⟩
  exact hX.exists_integral_filling_mass_le hT hz o R (fun x =>
    Metric.dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ o) (mem_univ x))

end CAT0Fillings

end

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
end
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Radial_MassComparison
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
variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [Nonempty X] {k : ℕ} (C : IntegerChart X k)
theorem mass_eq_integral_majorant (hC : IsMetricCurrent C.action) {J : Euc k → ℝ}
    (hρ : Integrable (fun z => |(C.multiplicity z : ℝ)| * J z)
      (volume.restrict C.domain))
    (hJ : 0 ≤ᵐ[volume.restrict C.domain] J)
    (hcontrol : Controls C.action (C.majorantMeasure J))
    (hmin : ∀ ν : Measure X, IsFiniteMeasure ν → Controls C.action ν →
      C.majorantMeasure J ≤ ν) :
    mass C.action = ∫ z, |(C.multiplicity z : ℝ)| * J z ∂volume.restrict C.domain := by
  have hfin : IsFiniteMeasure (C.majorantMeasure J) := densityPush_finite _ _ hρ
  have hνeq : (C.majorantMeasure J).real univ =
      ∫ z, |(C.multiplicity z : ℝ)| * J z ∂volume.restrict C.domain := by
    have hh := integral_densityPush (volume.restrict C.domain)
      C.measurable_paramExtended hρ
      (hJ.mono fun z hz => mul_nonneg (abs_nonneg _) hz) (continuous_const (y := (1:ℝ)))
    simpa only [majorantMeasure,integral_const,smul_eq_mul,mul_one] using hh
  rw [←hνeq]
  apply le_antisymm (mass_le_measure hfin hcontrol)
  obtain ⟨ν,hν,hνc,heq⟩ := hC.exists_controls_mass_eq
  rw [heq]
  exact ENNReal.toReal_mono (by let := hν; exact measure_ne_top ν univ)
    (hmin ν hν hνc univ)

end IntegerChart
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
-- module Solutions.OAIQ29_C0.CAT0Fillings_Swept_Measure
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
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

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
open CurrentOperations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}

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

theorem exists_chartGeometry {T : Functional X k}
    (hX : IsCAT0 X) (hT : IsMetricCurrent T) (hr : IntegerRectifiable T) :
    Nonempty (ChartGeometry hT) := by
  classical
  obtain ⟨C,hdis,hC,hsum,heq⟩ := hr
  choose P hPm hP hρ hfin hcontrol hmin hfield using
    fun i => (C i).exists_exact_quadratic_mass hX (hC i)
  choose p hPeq hpm hp using hfield
  simp only [hPeq] at hρ hfin hcontrol hmin
  let J (i : ℕ) (z : Euc k) := Real.sqrt
    (polarizationMatrix (p i z) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det
  have hmass (i : ℕ) : mass (C i).action =
      ∫ z, |((C i).multiplicity z : ℝ)| *J i z ∂volume.restrict (C i).domain :=
    (C i).mass_eq_integral_majorant (hC i) (hρ i)
      (Eventually.of_forall fun _ => Real.sqrt_nonneg _) (hcontrol i) (hmin i)
  let μ (i : ℕ) : Measure X := (C i).majorantMeasure (J i)
  have hμfin : ∀ i, IsFiniteMeasure (μ i) := hfin
  let := hμfin
  have htot (i : ℕ) : (μ i).real univ = mass (C i).action := by
    have heqm : MassMeasure.currentMassMeasure (hC i) = μ i := by
      apply le_antisymm (MassMeasure.currentMassMeasure_le (hC i) (hcontrol i))
      exact hmin i _ inferInstance (MassMeasure.currentMassMeasure_controls (hC i))
    rw [←heqm]
    exact MassMeasure.currentMassMeasure_total _
  have hμsum : Summable (fun i => (μ i).real univ) := by simpa only [htot] using hsum
  let := finite_sum_measure_of_summable_total μ hμsum
  have hmeasure : MassMeasure.currentMassMeasure hT = Measure.sum μ := by
    apply le_antisymm
    · exact MassMeasure.currentMassMeasure_le hT (controls_sum_general hcontrol heq)
    · exact sum_measure_le_of_component_minimal hC hcontrol hmin heq
        (fun i => (C i).measurableSet_image) hdis
        (fun i => (C i).majorantMeasure_ae_image _) (MassMeasure.currentMassMeasure_controls hT)
  have htotal : mass T = ∑' i, mass (C i).action := by
    rw [←MassMeasure.currentMassMeasure_total hT,hmeasure]
    rw [measureReal_def,Measure.sum_apply _ MeasurableSet.univ,
      ENNReal.tsum_toReal_eq (fun i => measure_ne_top (μ i) univ)]
    exact tsum_congr htot
  exact ⟨⟨C,p,hdis,hsum,heq,hpm,hp,hρ,hmass,hmeasure,htotal,hC,hcontrol⟩⟩

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

end ChartGeometry

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Density_InverseCutoff
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings

lemma inverseSquareCutoff_nonneg {ε : ℝ} (r : ℝ) : 0 ≤ inverseSquareCutoff ε r :=
  div_nonneg (sq_nonneg _) (sq_nonneg _)

lemma inverseSquareCutoff_le_one {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    inverseSquareCutoff ε r ≤ 1 := by
  apply (div_le_one (sq_pos_of_pos (hε.trans_le (le_max_left ..)))).mpr
  exact sq_le_sq₀ hε.le (hε.le.trans (le_max_left ..)) |>.mpr (le_max_left ..)

lemma inverseSquareCutoff_eq_one {ε r : ℝ} (hε : 0 < ε) (hr : r ≤ ε) :
    inverseSquareCutoff ε r = 1 := by
  simp only [inverseSquareCutoff,max_eq_left hr]
  exact div_self (pow_ne_zero _ hε.ne')

lemma hasDerivAt_inverse_square {ε r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun t : ℝ => ε^2/t^2) (-2*ε^2/r^3) r := by
  have h := (hasDerivAt_const r (ε^2)).div ((hasDerivAt_id r).pow 2) (pow_ne_zero _ hr)
  have hh : ((0:ℝ)*r^2-ε^2*(2*r^(2-1)*1))/(r^2)^2 = -2*ε^2/r^3 := by
    field_simp
    ring
  norm_num only [Pi.div_apply,Pi.pow_apply,id_eq,Nat.cast_ofNat] at h
  rw [hh] at h
  exact h

lemma inverseSquareCutoff_lipschitz {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith (Real.toNNReal (2/ε)) (inverseSquareCutoff ε) := by
  have hd : LipschitzOnWith (Real.toNNReal (2/ε)) (fun r : ℝ => ε^2/r^2) (Ici ε) := by
    apply (convex_Ici ε).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun r hr => (hasDerivAt_inverse_square (hε.trans_le hr).ne').hasDerivWithinAt)
    intro r hr
    have hr0 : 0 < r := hε.trans_le hr
    apply NNReal.coe_le_coe.mp
    simp only [coe_nnnorm,Real.norm_eq_abs,Real.toNNReal_of_nonneg (by positivity : 0 ≤ 2/ε),
      abs_div,abs_mul,abs_of_nonneg (sq_nonneg ε),abs_pow,abs_of_pos hr0]
    norm_num
    apply (div_le_div_iff₀ (pow_pos hr0 _) hε).mpr
    have hh : ε^3 ≤ r^3 := pow_le_pow_left₀ hε.le hr 3
    nlinarith
  have hm : LipschitzWith 1 (fun r : ℝ => max ε r) := by
    simpa using (LipschitzWith.const ε).max (LipschitzWith.id : LipschitzWith 1 (id : ℝ → ℝ))
  apply LipschitzWith.of_dist_le_mul
  intro r s
  exact (hd.dist_le_mul _ (show ε ≤ max ε r from le_max_left _ _) _ (show ε ≤ max ε s from le_max_left _ _)).trans
    (by simpa only [NNReal.coe_one,one_mul] using
      mul_le_mul_of_nonneg_left (hm.dist_le_mul r s) (NNReal.coe_nonneg _))

lemma hasDerivAt_inverseSquareCutoff_lt {ε r : ℝ} (hε : 0 < ε) (hr : r < ε) :
    HasDerivAt (inverseSquareCutoff ε) 0 r := by
  apply (hasDerivAt_const r (1:ℝ)).congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds hr] with s hs
  exact inverseSquareCutoff_eq_one hε hs.le

lemma hasDerivAt_inverseSquareCutoff_gt {ε r : ℝ} (hε : 0 < ε) (hr : ε < r) :
    HasDerivAt (inverseSquareCutoff ε) (-2*ε^2/r^3) r := by
  apply (hasDerivAt_inverse_square (hε.trans hr).ne').congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hr] with s hs
  simp only [inverseSquareCutoff,max_eq_right hs.le]

namespace IntegerChart
variable {X : Type*} [MetricSpace X] {k : ℕ} (C : IntegerChart X k)
lemma fderivWithin_scalar_comp {f : X → ℝ} {ψ : ℝ → ℝ} {a : ℝ}
    {z : Euc k} (hz : z ∈ C.domain) (hu : UniqueDiffWithinAt ℝ C.domain z)
    (hf : DifferentiableWithinAt ℝ (C.scalar f) C.domain z)
    (hψ : HasDerivAt ψ a (C.scalar f z)) :
    fderivWithin ℝ (C.scalar (ψ ∘ f)) C.domain z =
      a • fderivWithin ℝ (C.scalar f) C.domain z := by
  apply HasFDerivWithinAt.fderivWithin _ hu
  apply (hψ.comp_hasFDerivWithinAt z hf.hasFDerivWithinAt).congr
  · intro x hx
    simp only [C.scalar_eq hx,Function.comp_apply]
  · simp only [C.scalar_eq hz,Function.comp_apply]
end IntegerChart

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}
variable {T : Functional X k} {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma weighted_density_integrable_borel (i : ℕ) {w : X → ℝ} (hw : Measurable w)
    (hb : ∃ B : ℝ, ∀ x, |w x| ≤ B) :
    Integrable (fun z => q.density i z*w ((q.chart i).paramExtended z))
      (volume.restrict (q.chart i).domain) :=
  integrable_weighted_comp _ (q.chart i).measurable_paramExtended (q.density_integrable i) hw hb

lemma integral_massMeasure_borel {w : X → ℝ} (hw : Measurable w)
    (hb : ∃ B : ℝ, ∀ x, |w x| ≤ B) :
    (∫ x, w x ∂MassMeasure.currentMassMeasure hT) = ∑' i, ∫ z,
      q.density i z*w ((q.chart i).paramExtended z)
      ∂volume.restrict (q.chart i).domain := by
  have hi : Integrable w (MassMeasure.currentMassMeasure hT) := by
    obtain ⟨B,hB⟩ := hb
    exact Integrable.of_bound hw.aestronglyMeasurable B
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB x)
  rw [q.measure_eq] at hi ⊢
  rw [integral_sum_measure hi]
  apply tsum_congr
  intro i
  exact integral_densityPush_measurable _ (q.chart i).measurable_paramExtended
    (q.density_integrable i)
    (Eventually.of_forall fun _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) hw

lemma weighted_density_summable_borel {w : X → ℝ} (hw : Measurable w)
    (hb : ∃ B : ℝ, ∀ x, |w x| ≤ B) :
    Summable (fun i => ∫ z, q.density i z*w ((q.chart i).paramExtended z)
      ∂volume.restrict (q.chart i).domain) := by
  have hi : Integrable w (MassMeasure.currentMassMeasure hT) := by
    obtain ⟨B,hB⟩ := hb
    exact Integrable.of_bound hw.aestronglyMeasurable B
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB x)
  rw [q.measure_eq] at hi
  apply (hasSum_integral_measure hi).summable.congr
  intro i
  exact integral_densityPush_measurable _ (q.chart i).measurable_paramExtended
    (q.density_integrable i)
    (Eventually.of_forall fun _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) hw

lemma ae_radialNormSq_bounds (o : X) (i : ℕ) :
    ∀ᵐ z ∂volume.restrict (q.chart i).domain,
      0 ≤ q.radialNormSq o i z ∧ q.radialNormSq o i z ≤ 1 := by
  filter_upwards [q.differential i,
    (q.chart i).ae_scalar_row_quadratic_bound (q.field i) (q.differential i)
      (LipschitzWith.dist_right o)] with z hp hb
  let G := q.gram i z
  let α := differentialRow (fderivWithin ℝ ((q.chart i).scalar (dist o)) (q.chart i).domain z)
  have hG : G.PosDef := polarizationMatrix_posDef _ _ hp.2.2 hp.2.1
  have hn : 0 ≤ α ⬝ᵥ G⁻¹.mulVec α := hG.inv.posSemidef.dotProduct_mulVec_nonneg α
  refine ⟨hn,?_⟩
  have hh := hb (G⁻¹.mulVec α)
  have he : G.mulVec (G⁻¹.mulVec α) = α := by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hG.det_pos.ne'),
      Matrix.one_mulVec]
  change (α ⬝ᵥ G⁻¹.mulVec α)^2 ≤ (1:ℝ)^2*(G⁻¹.mulVec α ⬝ᵥ G.mulVec (G⁻¹.mulVec α)) at hh
  rw [he,dotProduct_comm (G⁻¹.mulVec α) α] at hh
  change α ⬝ᵥ G⁻¹.mulVec α ≤ 1
  nlinarith

lemma aestronglyMeasurable_radialNormSq (o : X) (i : ℕ) :
    AEStronglyMeasurable (q.radialNormSq o i) (volume.restrict (q.chart i).domain) := by
  let C := q.chart i
  let : MeasurableSpace (Matrix (Fin k) (Fin k) ℝ) := borel _
  let : BorelSpace (Matrix (Fin k) (Fin k) ℝ) := ⟨rfl⟩
  obtain ⟨L,U,hL,_⟩ := C.bilipschitz
  obtain ⟨R,hR,heR⟩ := (C.scalar_lipschitzOn hL (LipschitzWith.dist_right o)).extend_real
  have hPm : Measurable (q.gram i) := by
    have hh : Measurable (fun z a b => q.gram i z a b) :=
      measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun b =>
        measurable_polarizationMatrix (q.field i) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
          (q.measurable i) a b
    change @Measurable (Euc k) (Fin k → Fin k → ℝ) _ (borel _) _
    rw [show borel (Fin k → Fin k → ℝ) = MeasurableSpace.pi from BorelSpace.measurable_eq.symm]
    exact hh
  have hRd : Measurable (fun z => differentialRow (fderiv ℝ R z)) := by
    apply measurable_pi_iff.mpr
    intro a
    simp only [differentialRow]
    fun_prop
  have hc : Continuous (fun v : (Fin k → ℝ) × Matrix (Fin k) (Fin k) ℝ =>
      v.1 ⬝ᵥ v.2.mulVec v.1) := by fun_prop
  have hm := hc.measurable.comp (hRd.prodMk (measurable_matrix_inverse _ hPm))
  apply hm.aestronglyMeasurable.congr
  filter_upwards [ae_fderivWithin_eq_fderiv_extension volume C.borel hR heR] with z hz
  change fderivWithin ℝ ((q.chart i).scalar (dist o)) (q.chart i).domain z = _ at hz
  simp only [radialNormSq,hz,Function.comp_apply]

end ChartGeometry
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Fillings_Attainment
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
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

theorem mass_le_of_mass_tendsto {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] {k : ℕ} {Ts : ℕ → Functional X k}
    {T : Functional X k} (hTs : ∀ j, IsMetricCurrent (Ts j)) {m : ℝ}
    (hm : Tendsto (fun j => mass (Ts j)) atTop (𝓝 m))
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π))) :
    mass T ≤ m := by
  have hm0 : 0 ≤ m := ge_of_tendsto hm (Eventually.of_forall fun j => mass_nonneg (Ts j))
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hm.eventually (gt_mem_nhds (lt_add_of_pos_right m hε)))
  exact mass_le_of_bounded_weak_limit (⟨m+ε,by positivity⟩ : ℝ≥0)
    (fun j => hTs (j+N)) (fun j => (hN (j+N) (Nat.le_add_left N j)).le)
    (fun b π _ => (hlim b π).comp (tendsto_add_atTop_nat N))

lemma fillingVolume_nonneg {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] {k : ℕ}
    (T : Functional X (k+1)) : 0 ≤ fillingVolume T := by
  apply Real.sInf_nonneg
  rintro r ⟨S,_,_,rfl⟩
  exact mass_nonneg S

lemma fillingVolume_le {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompactSpace X] [Nonempty X] {k : ℕ}
    {T : Functional X (k+1)} {S : Functional X (k+2)}
    (hS : IsIntegral (k+2) S) (hb : boundarySucc S = T) : fillingVolume T ≤ mass S := by
  apply csInf_le
  · exact ⟨0,by rintro r ⟨U,_,_,rfl⟩; exact mass_nonneg U⟩
  · exact ⟨S,hS,hb,rfl⟩

 theorem IsCAT0.exists_minimal_integral_filling (hX : IsCAT0 X) {k : ℕ}
    {T : Functional X (k+1)} (hT : IsIntegral (k+1) T) (hz : boundarySucc T = 0) :
    ∃ S : Functional X (k+2), IsIntegral (k+2) S ∧ boundarySucc S = T ∧
      mass S = fillingVolume T := by
  obtain ⟨S,hS,hb,_⟩ := hX.exists_integral_filling_diam hT hz
  exact exists_filling_mass_eq hX ⟨S,hS,hb⟩

lemma IsCAT0.fillingVolume_le_linear (hX : IsCAT0 X) {k : ℕ}
    {T : Functional X (k+1)} (hT : IsIntegral (k+1) T) (hz : boundarySucc T = 0) :
    fillingVolume T ≤ (k+2:ℝ)*Metric.diam (univ : Set X)*mass T := by
  obtain ⟨S,hS,hb,hm⟩ := hX.exists_integral_filling_diam hT hz
  exact (fillingVolume_le hS hb).trans hm

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Fillings_WeightedCone
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings
open Foundations CurrentOperations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X] in
lemma boundarySucc_neg {k : ℕ} (T : Functional X (k+1)) :
    boundarySucc (-T) = -boundarySucc T := by
  funext b π
  by_cases h : Admissible b π <;> simp [boundarySucc,h]

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X] in
lemma boundarySucc_add {k : ℕ} (T U : Functional X (k+1)) :
    boundarySucc (T+U) = boundarySucc T+boundarySucc U := by
  funext b π
  by_cases h : Admissible b π <;> simp [boundarySucc,h]

lemma IsIntegral.neg {k : ℕ} {T : Functional X k} (hT : IsIntegral k T) :
    IsIntegral k (-T) := by
  have h0 : IsIntegral k (0 : Functional X k) := isIntegral_zero k
  simpa only [zero_sub] using h0.sub hT

lemma IsIntegral.add {k : ℕ} {T U : Functional X k} (hT : IsIntegral k T)
    (hU : IsIntegral k U) : IsIntegral k (T+U) := by
  simpa only [sub_neg_eq_add] using hT.sub hU.neg

omit [Nonempty X] in
lemma mass_sub_le {k : ℕ} {T U : Functional X k} (hT : IsMetricCurrent T)
    (hU : IsMetricCurrent U) : mass (T-U) ≤ mass T+mass U := by
  simpa only [sub_eq_add_neg,mass_neg] using mass_add_le hT hU.neg

lemma fillingVolume_zero {k : ℕ} : fillingVolume (0 : Functional X (k+1)) = 0 := by
  apply le_antisymm _ (fillingVolume_nonneg _)
  have hb : boundarySucc (0 : Functional X (k+2)) = 0 := by
    funext b π; simp [boundarySucc]
  exact (fillingVolume_le (isIntegral_zero (k+2)) hb).trans_eq (mass_zero (k+2))

lemma fillingVolume_neg (hX : IsCAT0 X) {k : ℕ} {T : Functional X (k+1)}
    (hT : IsIntegral (k+1) T) (hz : boundarySucc T = 0) :
    fillingVolume (-T) = fillingVolume T := by
  obtain ⟨S,hS,hb,hm⟩ := hX.exists_minimal_integral_filling hT hz
  have hnz : boundarySucc (-T) = 0 := by rw [boundarySucc_neg,hz,neg_zero]
  obtain ⟨U,hU,hUb,hUm⟩ := hX.exists_minimal_integral_filling hT.neg hnz
  apply le_antisymm
  · exact (fillingVolume_le hS.neg (by rw [boundarySucc_neg,hb])).trans_eq (by rw [mass_neg,hm])
  · exact (fillingVolume_le hU.neg (by rw [boundarySucc_neg,hUb,neg_neg])).trans_eq (by rw [mass_neg,hUm])

lemma fillingVolume_add_le (hX : IsCAT0 X) {k : ℕ} {T U : Functional X (k+1)}
    (hT : IsIntegral (k+1) T) (hzT : boundarySucc T = 0)
    (hU : IsIntegral (k+1) U) (hzU : boundarySucc U = 0) :
    fillingVolume (T+U) ≤ fillingVolume T+fillingVolume U := by
  obtain ⟨S,hS,hbS,hmS⟩ := hX.exists_minimal_integral_filling hT hzT
  obtain ⟨R,hR,hbR,hmR⟩ := hX.exists_minimal_integral_filling hU hzU
  calc
    _ ≤ mass (S+R) := fillingVolume_le (hS.add hR) (by rw [boundarySucc_add,hbS,hbR])
    _ ≤ mass S+mass R := mass_add_le hS.1 hR.1
    _ = _ := by rw [hmS,hmR]

lemma fillingVolume_sub_symm (hX : IsCAT0 X) {k : ℕ} {T U : Functional X (k+1)}
    (hT : IsIntegral (k+1) T) (hzT : boundarySucc T = 0)
    (hU : IsIntegral (k+1) U) (hzU : boundarySucc U = 0) :
    fillingVolume (T-U) = fillingVolume (U-T) := by
  have hz : boundarySucc (U-T) = 0 := by rw [boundarySucc_sub,hzU,hzT,sub_self]
  simpa only [neg_sub] using fillingVolume_neg hX (hU.sub hT) hz

lemma fillingVolume_triangle (hX : IsCAT0 X) {k : ℕ} {T U V : Functional X (k+1)}
    (hT : IsIntegral (k+1) T) (hzT : boundarySucc T = 0)
    (hU : IsIntegral (k+1) U) (hzU : boundarySucc U = 0)
    (hV : IsIntegral (k+1) V) (hzV : boundarySucc V = 0) :
    fillingVolume (T-V) ≤ fillingVolume (T-U)+fillingVolume (U-V) := by
  have hh := fillingVolume_add_le hX (hT.sub hU)
    (by rw [boundarySucc_sub,hzT,hzU,sub_self]) (hU.sub hV)
    (by rw [boundarySucc_sub,hzU,hzV,sub_self])
  simpa only [sub_add_sub_cancel] using hh

lemma abs_fillingVolume_sub_le (hX : IsCAT0 X) {k : ℕ} {T U : Functional X (k+1)}
    (hT : IsIntegral (k+1) T) (hzT : boundarySucc T = 0)
    (hU : IsIntegral (k+1) U) (hzU : boundarySucc U = 0) :
    |fillingVolume T-fillingVolume U| ≤ fillingVolume (T-U) := by
  have hzero : boundarySucc (0 : Functional X (k+1)) = 0 := by
    funext b π; simp [boundarySucc]
  have hi0 : IsIntegral (k+1) (0 : Functional X (k+1)) := isIntegral_zero (k+1)
  have h1 := fillingVolume_triangle hX hT hzT hU hzU hi0 hzero
  have h2 := fillingVolume_triangle hX hU hzU hT hzT hi0 hzero
  simp only [sub_zero,fillingVolume_sub_symm hX hU hzU hT hzT] at h1 h2
  exact abs_le.mpr ⟨by linarith,by linarith⟩

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
local instance instBorelSpaceMatrixReal_solutions_2_r5c1164_1 : BorelSpace (Matrix ι ι ℝ) := ⟨rfl⟩
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
local instance instBorelSpaceMatrixFinReal_1_r5c1164_1 : BorelSpace (Matrix (Fin k) (Fin k) ℝ) := ⟨rfl⟩
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

end ChartGeometry
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Density_RadialEstimate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings

lemma cutoffVariationWeight_bounds {ε r a : ℝ} (hε : 0 < ε) (ha : a ∈ Icc (0:ℝ) 1) :
    0 ≤ cutoffVariationWeight ε r a ∧ cutoffVariationWeight ε r a ≤ 2 := by
  unfold cutoffVariationWeight
  split_ifs
  · norm_num
  · have hg := inverseSquareCutoff_nonneg (ε := ε) r
    have hgl := inverseSquareCutoff_le_one hε r
    have hh := mul_le_mul_of_nonneg_left (show 1-a ≤ 1 by linarith [ha.1])
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hg)
    constructor
    · exact mul_nonneg (mul_nonneg (by norm_num) hg) (sub_nonneg.mpr ha.2)
    · nlinarith [ha.2]

lemma cutoff_pointwise_estimate {ε ell r a : ℝ} (hε : 0 < ε) (hell : 0 < ell)
    (hr : 0 ≤ r) (ha : a ∈ Icc (0:ℝ) 1) :
    (if r < ε then 2*ell-ε else 0)-ε^2/(8*ell) ≤
      ell*cutoffVariationWeight ε r a-r*inverseSquareCutoff ε r*Real.sqrt (1-a) := by
  have hs0 := Real.sqrt_nonneg (1-a)
  have hs2 : (Real.sqrt (1-a))^2 = 1-a := Real.sq_sqrt (sub_nonneg.mpr ha.2)
  have hs1 : Real.sqrt (1-a) ≤ 1 := by nlinarith [ha.1]
  by_cases ht : r < ε
  · simp only [cutoffVariationWeight,ite_eq_left ht,inverseSquareCutoff_eq_one hε ht.le,mul_one]
    have hh := mul_le_mul_of_nonneg_left hs1 hr
    have hend : 0 ≤ ε^2/(8*ell) := by positivity
    nlinarith
  · have hr0 : 0 < r := hε.trans_le (le_of_not_gt ht)
    let b : ℝ := Real.sqrt (1-a)/r
    have hquad : 2*ell*b^2-b ≥ -1/(8*ell) := by
      have hh : b-2*ell*b^2 ≤ 1/(8*ell) := by
        apply (le_div_iff₀ (by positivity : 0 < 8*ell)).mpr
        nlinarith [sq_nonneg (4*ell*b-1)]
      simpa only [neg_sub,neg_div] using neg_le_neg hh
    have he : ell*cutoffVariationWeight ε r a-r*inverseSquareCutoff ε r*Real.sqrt (1-a) =
        ε^2*(2*ell*b^2-b) := by
      simp only [cutoffVariationWeight,ite_eq_right ht,inverseSquareCutoff,max_eq_right (le_of_not_gt ht),b]
      field_simp
      nlinarith [hs2]
    rw [he,ite_eq_right ht,zero_sub]
    have hh := mul_le_mul_of_nonneg_left hquad (sq_nonneg ε)
    calc
      -(ε^2/(8*ell)) = ε^2*(-1/(8*ell)) := by ring
      _ ≤ ε^2*(2*ell*b^2-b) := hh

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}
variable {T : Functional X k} {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma ae_density_zero_or_not_mem {s : Set X} (hs : MeasurableSet s)
    (hμ : MassMeasure.currentMassMeasure hT s = 0) (i : ℕ) :
    ∀ᵐ z ∂volume.restrict (q.chart i).domain,
      q.density i z = 0 ∨ (q.chart i).paramExtended z ∉ s := by
  classical
  let τ := densityPush (volume.restrict (q.chart i).domain) (q.chart i).paramExtended (q.density i)
  let : IsFiniteMeasure τ := densityPush_finite _ _ (q.density_integrable i)
  have ht : τ ≤ MassMeasure.currentMassMeasure hT := by
    rw [q.measure_eq]
    exact Measure.le_sum (fun index => densityPush (volume.restrict (q.chart index).domain)
      (q.chart index).paramExtended (q.density index)) i
  have ht0 : τ s = 0 := le_antisymm ((ht s).trans_eq hμ) bot_le
  have hi : ∫ z, q.density i z*s.indicator (fun _ => (1:ℝ)) ((q.chart i).paramExtended z)
      ∂volume.restrict (q.chart i).domain = 0 := by
    rw [←integral_densityPush_measurable _ (q.chart i).measurable_paramExtended
      (q.density_integrable i)
      (Eventually.of_forall fun _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
      (measurable_const.indicator hs),integral_indicator hs,integral_const]
    simp only [Measure.restrict_apply_univ,measureReal_def,smul_eq_mul]
    change (τ s).toReal*1 = 0
    rw [ht0]; simp
  have hB : ∃ B : ℝ, ∀ x, |s.indicator (fun _ => (1:ℝ)) x| ≤ B := by
    refine ⟨1,fun x => ?_⟩
    by_cases hx : x ∈ s <;> simp [hx]
  have ha := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun _ => mul_nonneg (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
      (indicator_nonneg (fun _ _ => zero_le_one) _))
    (q.weighted_density_integrable_borel i (measurable_const.indicator hs) hB)).mp hi
  filter_upwards [ha] with z hz
  by_cases hx : (q.chart i).paramExtended z ∈ s
  · left
    simpa only [density,indicator_of_mem hx,Pi.zero_apply,mul_one] using hz
  · exact Or.inr hx

lemma cutoff_weight_integrable (o : X) (i : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun z => q.density i z * cutoffVariationWeight ε
      (dist o ((q.chart i).paramExtended z)) (q.radialNormSq o i z))
      (volume.restrict (q.chart i).domain) := by
  classical
  have hr : Measurable (fun z => dist o ((q.chart i).paramExtended z)) :=
    (continuous_const.dist continuous_id).measurable.comp (q.chart i).measurable_paramExtended
  have hg : Measurable (fun z => inverseSquareCutoff ε (dist o ((q.chart i).paramExtended z))) :=
    (inverseSquareCutoff_lipschitz hε).continuous.measurable.comp hr
  have hm : AEStronglyMeasurable (fun z => cutoffVariationWeight ε
      (dist o ((q.chart i).paramExtended z)) (q.radialNormSq o i z))
      (volume.restrict (q.chart i).domain) := by
    exact AEStronglyMeasurable.piecewise (measurableSet_lt hr measurable_const)
      aestronglyMeasurable_const ((hg.aestronglyMeasurable.const_mul 2).mul
        (aestronglyMeasurable_const.sub (q.aestronglyMeasurable_radialNormSq o i).restrict))
  apply (q.density_integrable i).mul_bdd hm
  filter_upwards [q.ae_radialNormSq_bounds o i] with z hz
  have hh := cutoffVariationWeight_bounds (r := dist o ((q.chart i).paramExtended z)) hε hz
  simpa only [Real.norm_eq_abs,abs_of_nonneg hh.1] using hh.2

end ChartGeometry

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]
variable {T : Functional X 2} {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma radialVariationChart_cutoff (o : X) (i : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hμ : MassMeasure.currentMassMeasure hT {x | dist o x = ε} = 0) :
    q.radialVariationChart o (fun x => inverseSquareCutoff ε (dist o x)) i =
      ∫ z, q.density i z*cutoffVariationWeight ε
        (dist o ((q.chart i).paramExtended z)) (q.radialNormSq o i z)
        ∂volume.restrict (q.chart i).domain := by
  have hs : MeasurableSet {x : X | dist o x = ε} := isClosed_eq
    (continuous_const.dist continuous_id) continuous_const |>.measurableSet
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (q.chart i).borel,
    ae_uniqueDiffWithinAt volume (q.chart i).domain,
    (q.chart i).ae_differentiableWithinAt_scalar (LipschitzWith.dist_right o),
    q.ae_density_zero_or_not_mem hs hμ i] with z hz hu hr hn
  rcases hn with hn | hn
  · simp only [hn,zero_mul]
  let r := dist o ((q.chart i).paramExtended z)
  have hre : (q.chart i).scalar (dist o) z = r := by
    simp only [r,IntegerChart.scalar_eq _ hz,IntegerChart.paramExtended,dite_eq_left hz]
  have hge : (q.chart i).scalar (fun x => inverseSquareCutoff ε (dist o x)) z =
      inverseSquareCutoff ε r := by
    simp only [r,IntegerChart.scalar_eq _ hz,IntegerChart.paramExtended,dite_eq_left hz]
  have hne : r ≠ ε := hn
  change q.density i z * _ = q.density i z * cutoffVariationWeight ε r (q.radialNormSq o i z)
  rw [hge,hre]
  by_cases ht : r < ε
  · have hd := (q.chart i).fderivWithin_scalar_comp hz hu hr
      (show HasDerivAt (inverseSquareCutoff ε) 0 ((q.chart i).scalar (dist o) z) by
        rw [hre]; exact hasDerivAt_inverseSquareCutoff_lt hε ht)
    change fderivWithin ℝ ((q.chart i).scalar (fun x => inverseSquareCutoff ε (dist o x)))
      (q.chart i).domain z = _ at hd
    have hrow0 : differentialRow (0 : Euc 2 →L[ℝ] ℝ) = 0 := rfl
    simp only [hd,zero_smul,hrow0,Matrix.mulVec_zero,
      dotProduct_zero,mul_zero,add_zero,cutoffVariationWeight,ite_eq_left ht,
      inverseSquareCutoff_eq_one hε ht.le,mul_one,Nat.cast_ofNat]
  · have hgt : ε < r := lt_of_le_of_ne (le_of_not_gt ht) hne.symm
    have hd := (q.chart i).fderivWithin_scalar_comp hz hu hr
      (show HasDerivAt (inverseSquareCutoff ε) (-2*ε^2/r^3)
          ((q.chart i).scalar (dist o) z) by
        rw [hre]; exact hasDerivAt_inverseSquareCutoff_gt hε hgt)
    change fderivWithin ℝ ((q.chart i).scalar (fun x => inverseSquareCutoff ε (dist o x)))
      (q.chart i).domain z = _ at hd
    have hrow : differentialRow (fderivWithin ℝ ((q.chart i).scalar
        (fun x => inverseSquareCutoff ε (dist o x))) (q.chart i).domain z) =
        (-2*ε^2/r^3) • differentialRow (fderivWithin ℝ ((q.chart i).scalar (dist o))
          (q.chart i).domain z) := by
      rw [hd]
      ext j
      simp only [differentialRow,_root_.smul_apply,Pi.smul_apply,smul_eq_mul]
    rw [hrow,Matrix.mulVec_smul,dotProduct_smul]
    simp only [smul_eq_mul,radialNormSq,cutoffVariationWeight,ite_eq_right ht,Nat.cast_ofNat,
      inverseSquareCutoff,max_eq_right hgt.le]
    field_simp
    ring

end ChartGeometry
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Density_Chart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal BigOperators

namespace CAT0Fillings
namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]
variable {T : Functional X 2} {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma cutoff_mass_upper (o : X) {ε ell : ℝ} (hε : 0 < ε) (hell : 0 < ell)
    (hμ : MassMeasure.currentMassMeasure hT {x | dist o x = ε} = 0)
    (hrad : ell*q.radialVariation o (fun x => inverseSquareCutoff ε (dist o x)) ≤
      q.sweptMass o (fun x => inverseSquareCutoff ε (dist o x))) :
    (2*ell-ε)*(MassMeasure.currentMassMeasure hT).real (Metric.ball o ε) ≤
      ε^2/(8*ell)*mass T := by
  classical
  let g : X → ℝ := fun x => inverseSquareCutoff ε (dist o x)
  have hg : LipschitzWith ((2/ε).toNNReal*1) g :=
    (inverseSquareCutoff_lipschitz hε).comp (LipschitzWith.dist_right o)
  have hg0 : ∀ x, 0 ≤ g x := fun x => inverseSquareCutoff_nonneg _
  let w : X → ℝ := fun x => (if dist o x < ε then 2*ell-ε else 0)-ε^2/(8*ell)
  have hw : Measurable w :=
    ((measurable_const.piecewise (measurableSet_lt (continuous_const.dist continuous_id).measurable
      measurable_const) measurable_const).sub measurable_const)
  have hwb : ∃ B : ℝ, ∀ x, |w x| ≤ B := by
    refine ⟨|2*ell-ε|+|ε^2/(8*ell)|,fun x => ?_⟩
    dsimp only [w]
    split_ifs
    · exact abs_sub _ _
    · simpa only [zero_sub,abs_neg] using le_add_of_nonneg_left (abs_nonneg (2*ell-ε))
  let V (i : ℕ) := q.radialVariationChart o g i
  let W (i : ℕ) := ∫ z, |((q.chart i).multiplicity z : ℝ)| *
    (q.chart i).sweptWeight (q.field i) o g z ∂volume.restrict (q.chart i).domain
  have hW := q.swept_integrable_summable o hg hg0
  have hV := (q.spatialMass_first_variation o hg).1
  have hchart (i : ℕ) : (∫ z, q.density i z*w ((q.chart i).paramExtended z)
      ∂volume.restrict (q.chart i).domain) ≤ ell*V i-W i := by
    dsimp only [V,W]
    rw [q.radialVariationChart_cutoff o i hε hμ,←integral_const_mul,←integral_sub
      ((q.cutoff_weight_integrable o i hε).const_mul ell) (hW.1 i)]
    apply integral_mono_ae (q.weighted_density_integrable_borel i hw hwb)
      (((q.cutoff_weight_integrable o i hε).const_mul ell).sub (hW.1 i))
    filter_upwards [ae_restrict_mem (q.chart i).borel,q.ae_radialNormSq_bounds o i] with z hz ha
    have hin := cutoff_pointwise_estimate hε hell (dist_nonneg (x := o)
      (y := (q.chart i).paramExtended z)) ha
    have h := mul_le_mul_of_nonneg_left hin (q.density_nonneg i z)
    have hs (f : X → ℝ) : (q.chart i).scalar f z = f ((q.chart i).paramExtended z) := by
      rw [IntegerChart.scalar_eq _ hz]
      simp only [IntegerChart.paramExtended,dite_eq_left hz]
    dsimp only [w,g] at h ⊢
    simp only [Pi.sub_apply,IntegerChart.sweptWeight,hs,density,gram,radialNormSq] at h ⊢
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hint : (∫ x, w x ∂MassMeasure.currentMassMeasure hT) ≤ 0 := by
    rw [q.integral_massMeasure_borel hw hwb]
    calc
      _ ≤ ∑' i, (ell*V i-W i) := (q.weighted_density_summable_borel hw hwb).tsum_le_tsum
        hchart ((hV.mul_left ell).sub hW.2)
      _ = ell*q.radialVariation o g-q.sweptMass o g := by
        rw [(hV.mul_left ell).tsum_sub hW.2,tsum_mul_left]
        rfl
      _ ≤ 0 := sub_nonpos.mpr hrad
  have heq : w = fun x => (Metric.ball o ε).indicator (fun _ => 2*ell-ε) x-ε^2/(8*ell) := by
    funext x
    simp only [w,indicator,Metric.mem_ball,dist_comm]
  rw [heq,integral_sub ((integrable_const (2*ell-ε)).indicator measurableSet_ball)
    (integrable_const _),integral_indicator measurableSet_ball,integral_const,integral_const] at hint
  simp only [smul_eq_mul,measureReal_def,Measure.restrict_apply_univ] at hint
  change (MassMeasure.currentMassMeasure hT).real (Metric.ball o ε)*(2*ell-ε)-
    (MassMeasure.currentMassMeasure hT).real univ*(ε^2/(8*ell)) ≤ 0 at hint
  rw [MassMeasure.currentMassMeasure_total hT] at hint
  nlinarith

end ChartGeometry
end CAT0Fillings
end

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings

lemma exists_euclidean_density_point_two {s : Set (Euc 2)} (hs : MeasurableSet s)
    (hs0 : volume s ≠ 0) :
    ∃ u ∈ s, Tendsto (fun r : ℝ => volume.real (s ∩ closedBall u r)/r^2)
      (𝓝[>] 0) (𝓝 Real.pi) := by
  obtain ⟨u,hu,hd⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hs0
    (ae_restrict_of_ae (Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume hs))
  simp only [indicator_of_mem hu,Pi.one_apply] at hd
  refine ⟨u,hu,?_⟩
  have hreal := (ENNReal.continuousAt_toReal (by norm_num : (1:ℝ≥0∞) ≠ ∞)).tendsto.comp hd
  simp only [ENNReal.toReal_one] at hreal
  have hlim := hreal.mul_const Real.pi
  simp only [one_mul] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  simp only [Function.comp_apply,ENNReal.toReal_div,measureReal_def,EuclideanSpace.volume_closedBall_fin_two,ENNReal.toReal_mul,
    ENNReal.toReal_pow,ENNReal.toReal_ofReal hr.le,ENNReal.toReal_ofReal Real.pi_pos.le]
  field_simp [ne_of_gt (show (0:ℝ) < r from hr),Real.pi_ne_zero]

lemma exists_lipschitz_chart_density {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {s : Set (Euc 2)} (hs : MeasurableSet s) (hs0 : volume s ≠ 0)
    {f : Euc 2 → X} (hf : Measurable f) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (hLip : ∀ y ∈ s, ∀ z ∈ s, dist (f y) (f z) ≤ b*dist y z)
    (hdom : Measure.map f (volume.restrict s) ≤ ENNReal.ofReal a • μ) :
    ∃ o : X, ∀ v : ℝ, b < v → ∀ d : ℝ, d < Real.pi →
      ∀ᶠ r in 𝓝[>] (0:ℝ), d*(r/v)^2 ≤ a*μ.real (ball o r) := by
  obtain ⟨u,hu,hd⟩ := exists_euclidean_density_point_two hs hs0
  refine ⟨f u,fun v hv d hdπ => ?_⟩
  have hv0 : 0 < v := hb.trans_lt hv
  have ht : Tendsto (fun r : ℝ => r/v) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨by simpa using ((tendsto_id.div_const v : Tendsto (fun r : ℝ => r/v) (𝓝 0) (𝓝 (0/v))).mono_left nhdsWithin_le_nhds),?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr using div_pos hr hv0
  have hlimit := hd.comp ht
  have hevent := hlimit.eventually (eventually_gt_nhds hdπ)
  filter_upwards [self_mem_nhdsWithin,hevent] with r hr hrd
  have hr0 : 0 < r/v := div_pos hr hv0
  have hincl : s ∩ closedBall u (r/v) ⊆ f ⁻¹' ball (f u) r ∩ s := by
    intro z hz
    refine ⟨?_,hz.1⟩
    change dist (f z) (f u) < r
    have hh := (hLip z hz.1 u hu).trans (mul_le_mul_of_nonneg_left hz.2 hb)
    exact hh.trans_lt (by have := mul_lt_mul_of_pos_right hv hr0; nlinarith [div_mul_cancel₀ r hv0.ne'])
  have hbnd : volume (s ∩ closedBall u (r/v)) ≤ ENNReal.ofReal a*μ (ball (f u) r) := by
    calc
      _ ≤ (volume.restrict s) (f ⁻¹' ball (f u) r) := by
        rw [Measure.restrict_apply (hf measurableSet_ball)]
        exact measure_mono hincl
      _ = (Measure.map f (volume.restrict s)) (ball (f u) r) :=
        (Measure.map_apply hf measurableSet_ball).symm
      _ ≤ _ := hdom _
  have hfin : ENNReal.ofReal a*μ (ball (f u) r) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hrb := ENNReal.toReal_mono hfin hbnd
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofReal ha.le] at hrb
  change volume.real (s ∩ closedBall u (r/v)) ≤ a*μ.real (ball (f u) r) at hrb
  exact ((lt_div_iff₀ (sq_pos_of_pos hr0)).mp hrd).le.trans hrb

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Density_NearEuclidean
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal MatrixOrder

namespace CAT0Fillings
open CurrentOperations BorelCoefficients

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}
variable {T : Functional X k} {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma chart_controls_total (i : ℕ) : Controls (q.chart i).action
    (MassMeasure.currentMassMeasure hT) := by
  have hle : (q.chart i).majorantMeasure (fun z => Real.sqrt (q.gram i z).det) ≤
      MassMeasure.currentMassMeasure hT := by
    rw [q.measure_eq]
    exact Measure.le_sum (fun index => (q.chart index).majorantMeasure
      (fun point => Real.sqrt (q.gram index point).det)) i
  intro b π hab hπ
  apply (q.control i b π hab hπ).trans
  apply integral_mono_measure hle
  · exact Eventually.of_forall fun _ => abs_nonneg _
  · exact (integrable_boundedLip _ hab).abs

lemma exists_positive_integer_region (hM : 0 < mass T) :
    ∃ (i : ℕ) (s : Set (Euc k)), MeasurableSet s ∧ s ⊆ (q.chart i).domain ∧
      volume s ≠ 0 ∧ ∀ᵐ z ∂volume.restrict s, 1 ≤ |((q.chart i).multiplicity z : ℝ)| := by
  have hi : ∃ i, 0 < mass (q.chart i).action := by
    by_contra! hi
    have : (∑' i, mass (q.chart i).action) ≤ 0 := tsum_nonpos hi
    rw [←q.total_mass] at this
    exact (not_le_of_gt hM) this
  obtain ⟨i,hi⟩ := hi
  let C := q.chart i
  let hg := C.integrable.aestronglyMeasurable
  let g : Euc k → ℝ := hg.mk (fun z => (C.multiplicity z : ℝ))
  have hgm : Measurable g := hg.stronglyMeasurable_mk.measurable
  have hge : (fun z => (C.multiplicity z : ℝ)) =ᵐ[volume.restrict C.domain] g := hg.ae_eq_mk
  have hgn : MeasurableSet {z | g z ≠ 0} := (hgm (measurableSet_singleton 0)).compl
  let s := C.domain ∩ {z | g z ≠ 0}
  have hs : MeasurableSet s := C.borel.inter hgn
  have hss : s ⊆ C.domain := inter_subset_left
  have hs0 : volume s ≠ 0 := by
    intro hs0
    have hge0 : g =ᵐ[volume.restrict C.domain] 0 := by
      rw [EventuallyEq,ae_iff]
      change (volume.restrict C.domain) {z | g z ≠ 0} = 0
      rw [Measure.restrict_apply hgn,inter_comm]
      exact hs0
    have hm0 : (fun z => (C.multiplicity z : ℝ)) =ᵐ[volume.restrict C.domain] 0 := hge.trans hge0
    have hm : mass C.action = 0 := by
      rw [q.chart_mass i]
      apply integral_eq_zero_of_ae
      filter_upwards [hm0] with z hz
      change (C.multiplicity z : ℝ) = 0 at hz
      change |(C.multiplicity z : ℝ)| * _ = 0
      rw [hz,abs_zero,zero_mul]
    exact hi.ne' hm
  refine ⟨i,s,hs,hss,hs0,?_⟩
  have hget := hge.filter_mono (ae_mono (Measure.restrict_mono hss le_rfl))
  filter_upwards [hget,ae_restrict_mem hs] with z hz hzs
  have hn : C.multiplicity z ≠ 0 := by
    intro hh
    exact hzs.2 (by rw [←hz,hh,Int.cast_zero])
  exact_mod_cast Int.one_le_abs hn

lemma exists_positive_near_hilbert_piece (hX : IsCAT0 X) (hM : 0 < mass T)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (i : ℕ) (s : Set (Euc k)) (p : Seminorm ℝ (Euc k)),
      MeasurableSet s ∧ s ⊆ (q.chart i).domain ∧ volume s ≠ 0 ∧
      (∀ᵐ z ∂volume.restrict s, 1 ≤ |((q.chart i).multiplicity z : ℝ)|) ∧
      (∀ v, p v = 0 ↔ v = 0) ∧
      (∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2) ∧
      ∀ y ∈ s, ∀ z ∈ s,
        (1-ε)*p (y-z) ≤ dist ((q.chart i).paramExtended y) ((q.chart i).paramExtended z) ∧
        dist ((q.chart i).paramExtended y) ((q.chart i).paramExtended z) ≤ (1+ε)*p (y-z) := by
  obtain ⟨i,s,hs,hss,hs0,hθ⟩ := q.exists_positive_integer_region hM
  let C := q.chart i
  obtain ⟨A,B,hA,hB⟩ := C.bilipschitz
  obtain ⟨p,t,ht,hts,hdis,hnull,hLip,hp,hnear⟩ :=
    MetricDifferentiation.exists_hilbertian_nearIsometric_chart_partition volume
      C.borel C.bounded.measure_lt_top.ne hA hB
      (fun a b c d => hX.quadrilateral (C.param a) (C.param b) (C.param c) (C.param d)) hε
  have hj : ∃ j, volume (s ∩ t j) ≠ 0 := by
    by_contra! hj
    have hcov : s ⊆ (C.domain \ ⋃ j, t j) ∪ ⋃ j, s ∩ t j := by
      intro z hz
      by_cases hh : z ∈ ⋃ j, t j
      · right
        obtain ⟨j,hj⟩ := mem_iUnion.mp hh
        exact mem_iUnion.mpr ⟨j,hz,hj⟩
      · exact Or.inl ⟨hss hz,hh⟩
    exact hs0 (measure_mono_null hcov (measure_union_null hnull (measure_iUnion_null hj)))
  obtain ⟨j,hj⟩ := hj
  have hne : (t j).Nonempty := (nonempty_of_measure_ne_zero hj).mono inter_subset_right
  refine ⟨i,s ∩ t j,p j,hs.inter (ht j),inter_subset_left.trans hss,hj,
    hθ.filter_mono (ae_mono (Measure.restrict_mono inter_subset_left le_rfl)),?_,(hp j hne).1,?_⟩
  · intro v
    constructor
    · intro hv
      have hh := (hp j hne).2 v
      rw [hv,mul_zero] at hh
      exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg v))
    · rintro rfl
      exact map_zero _
  · intro y hy z hz
    simpa only [IntegerChart.paramExtended,dite_eq_left (hss hy.1),dite_eq_left (hss hz.1)] using
      hnear j ⟨y,hss hy.1⟩ hy.2 ⟨z,hss hz.1⟩ hz.2

end ChartGeometry
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Tangent_Quadratic
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint _root_.OAI.CAT0Fillings.EuclideanStraightening.replaceMap_apply _root_.OAI.CAT0Fillings.EuclideanStraightening.straightenMap_zero _root_.OAI.CAT0Fillings.EuclideanStraightening.switchZero_apply_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal MatrixOrder

namespace CAT0Fillings

lemma exists_hilbert_norm_equiv {k : ℕ} (p : Seminorm ℝ (Euc k))
    (hp : ∀ v, p v = 0 ↔ v = 0)
    (hpara : ∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2) :
    ∃ e : Euc k ≃L[ℝ] Euc k, (∀ v, ‖e v‖ = p v) ∧
      |LinearMap.det e.toLinearEquiv.toLinearMap| =
        Real.sqrt (polarizationMatrix p (EuclideanSpace.basisFun (Fin k) ℝ).toBasis).det := by
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let Q := polarizationMatrix p b
  have hQ : Q.PosDef := polarizationMatrix_posDef b p hp hpara
  let L : Euc k →ₗ[ℝ] Euc k := Matrix.toEuclideanLin (CFC.sqrt Q)
  have hdet : LinearMap.det L = Real.sqrt Q.det := by
    rw [show L = Matrix.toLin b b (CFC.sqrt Q) from rfl,LinearMap.det_toLin]
    simpa only [RCLike.sqrt_real] using hQ.posSemidef.det_sqrt
  have hdet0 : LinearMap.det L ≠ 0 := by rw [hdet]; exact (Real.sqrt_pos.mpr hQ.det_pos).ne'
  let e := (L.equivOfDetNeZero hdet0).toContinuousLinearEquiv
  refine ⟨e,?_,?_⟩
  · intro v
    have hnorm : ‖e v‖^2 = p v^2 := by
      rw [←real_inner_self_eq_norm_sq]
      change inner ℝ (L v) (L v) = _
      simp only [EuclideanSpace.inner_eq_star_dotProduct,star_trivial]
      change (CFC.sqrt Q).mulVec (WithLp.ofLp v) ⬝ᵥ
        (CFC.sqrt Q).mulVec (WithLp.ofLp v) = p v^2
      rw [←dot_mulVec_sqrt Q hQ.posSemidef]
      have hrepr : b.repr v = WithLp.ofLp v := by ext j; simp [b]
      rw [←hrepr]
      exact polarizationMatrix_quadratic b p hp hpara v
    nlinarith [norm_nonneg (e v),apply_nonneg p v]
  · change |LinearMap.det L| = _
    rw [hdet,abs_of_nonneg (Real.sqrt_nonneg _)]

lemma normalized_linear_image_push {E X : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace X]
    (ν : Measure E) [ν.IsAddHaarMeasure] (e : E ≃L[ℝ] E)
    {s : Set E} (hs : MeasurableSet s) {f : E → X} (hf : Measurable f) :
    Measure.map (f ∘ e.symm) (ν.restrict (e '' s)) =
      ENNReal.ofReal |LinearMap.det e.toLinearEquiv.toLinearMap| •
        Measure.map f (ν.restrict s) := by
  have hs' : MeasurableSet (e '' s) := e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hs
  let J := ENNReal.ofReal |LinearMap.det e.toLinearEquiv.toLinearMap|
  have hmap : Measure.map e.symm ν = J • ν := by
    have hh := Measure.map_linearMap_addHaar_eq_smul_addHaar ν
      (LinearEquiv.isUnit_det' e.symm.toLinearEquiv).ne_zero
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    change J • ν = ENNReal.ofReal |(LinearMap.det e.toLinearEquiv.symm.toLinearMap)⁻¹| • ν
    rw [LinearEquiv.det_coe_symm,inv_inv]
  have heq : Measure.map e.symm (ν.restrict (e '' s)) = J • ν.restrict s := by
    rw [show e '' s = e.symm ⁻¹' s by
      ext x; exact e.toEquiv.image_eq_preimage_symm s ▸ Iff.rfl,
      ←Measure.restrict_map e.symm.continuous.measurable hs,hmap,Measure.restrict_smul]
  rw [←Measure.map_map hf e.symm.continuous.measurable,heq,
    Measure.map_smul]

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Density_Normalized
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Matrix
open scoped Topology NNReal ENNReal MatrixOrder

namespace CAT0Fillings
namespace IntegerChart
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ}

lemma normalized_piece (C : IntegerChart X k) (hC : IsMetricCurrent C.action)
    {μ : Measure X} [IsFiniteMeasure μ] (hμ : Controls C.action μ)
    {s : Set (Euc k)} (hs : MeasurableSet s) (hss : s ⊆ C.domain) (hs0 : volume s ≠ 0)
    (hθ : ∀ᵐ z ∂volume.restrict s, 1 ≤ |(C.multiplicity z : ℝ)|)
    (p : Seminorm ℝ (Euc k)) (hp : ∀ v, p v = 0 ↔ v = 0)
    (hpara : ∀ u v, p (u+v)^2+p (u-v)^2 = 2*p u^2+2*p v^2)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hnear : ∀ y ∈ s, ∀ z ∈ s,
      (1-ε)*p (y-z) ≤ dist (C.paramExtended y) (C.paramExtended z) ∧
      dist (C.paramExtended y) (C.paramExtended z) ≤ (1+ε)*p (y-z)) :
    ∃ (t : Set (Euc k)) (f : Euc k → X), MeasurableSet t ∧ volume t ≠ 0 ∧ Measurable f ∧
      (∀ y ∈ t, ∀ z ∈ t, dist (f y) (f z) ≤ (1+ε)*dist y z) ∧
      Measure.map f (volume.restrict t) ≤ ENNReal.ofReal ((1-ε)⁻¹^k) • μ := by
  let b := (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
  let Q := polarizationMatrix p b
  let J := Real.sqrt Q.det
  have hQ : Q.PosDef := polarizationMatrix_posDef b p hp hpara
  have hJ : 0 < J := Real.sqrt_pos.mpr hQ.det_pos
  obtain ⟨e,he,hdet⟩ := exists_hilbert_norm_equiv p hp hpara
  let K : ℝ≥0 := ⟨(1-ε)⁻¹, inv_nonneg.mpr (sub_pos.mpr hε1).le⟩
  let ℓ : Fin k → Euc k →L[ℝ] ℝ := fun i => matrixRowFunctional (CFC.sqrt Q) i
  have hrow : ∀ i y (hy : y ∈ s) z (hz : z ∈ s),
      |ℓ i y-ℓ i z| ≤ (K : ℝ)*dist (C.param ⟨y,hss hy⟩) (C.param ⟨z,hss hz⟩) := by
    intro i y hy z hz
    rw [←map_sub]
    apply (abs_matrixRow_sqrt_le Q hQ.posSemidef i (y-z)).trans
    have hh := (hnear y hy z hz).1
    simp only [paramExtended,dite_eq_left (hss hy),dite_eq_left (hss hz)] at hh
    change Real.sqrt ((WithLp.ofLp (y-z)) ⬝ᵥ Q *ᵥ WithLp.ofLp (y-z)) ≤ _
    rw [show Q = polarizationMatrix p b from rfl,sqrt_polarization_quadratic p hp hpara,WithLp.toLp_ofLp]
    change p (y-z) ≤ (1-ε)⁻¹*_
    rw [←div_eq_inv_mul]
    apply (le_div_iff₀ (sub_pos.mpr hε1)).mpr
    simpa only [mul_comm] using hh
  have hm : (Matrix.of fun i j => ℓ i (EuclideanSpace.single j 1)) = CFC.sqrt Q := by
    ext i j
    simp only [ℓ,Matrix.of_apply,matrixRowFunctional_single]
  have hdetQ : |(CFC.sqrt Q).det| = J := by
    rw [show (CFC.sqrt Q).det = Real.sqrt Q.det by simpa only [RCLike.sqrt_real] using hQ.posSemidef.det_sqrt]
    exact abs_of_nonneg (Real.sqrt_nonneg _)
  have hpiece : densityPush (volume.restrict s) C.paramExtended
      (fun z => |(C.multiplicity z : ℝ)| * J) ≤ ((K^k) • μ).restrict (C.paramExtended '' s) := by
    simpa only [hm,hdetQ] using C.linear_piece_mass_le hC hμ hs hss ℓ K hrow
  have hconst : ENNReal.ofReal J • Measure.map C.paramExtended (volume.restrict s) ≤ (K^k) • μ := by
    calc
      _ = densityPush (volume.restrict s) C.paramExtended (fun _ => J) := by
        rw [densityPush,withDensity_const,Measure.map_smul]
      _ ≤ densityPush (volume.restrict s) C.paramExtended (fun z => |(C.multiplicity z : ℝ)| * J) := by
        apply densityPush_mono_ae C.measurable_paramExtended
        filter_upwards [hθ] with z hz
        exact (le_mul_of_one_le_left hJ.le hz)
      _ ≤ _ := hpiece.trans Measure.restrict_le_self
  refine ⟨e '' s,C.paramExtended ∘ e.symm,
    e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hs,?_,
    C.measurable_paramExtended.comp e.symm.continuous.measurable,?_,?_⟩
  · have hh := Measure.addHaar_image_linearMap volume e.toLinearEquiv.toLinearMap s
    change volume (e '' s) = _ at hh
    rw [hh,hdet]
    exact mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hJ) hs0
  · rintro _ ⟨y,hy,rfl⟩ _ ⟨z,hz,rfl⟩
    simp only [Function.comp_apply,e.symm_apply_apply]
    apply ((hnear y hy z hz).2).trans
    apply mul_le_mul_of_nonneg_left _ (by linarith only [hε])
    simp only [dist_eq_norm,←map_sub,he,le_refl]
  · rw [normalized_linear_image_push volume e hs C.measurable_paramExtended,hdet]
    convert hconst using 1
    all_goals try with_reducible_and_instances rfl
    change (ENNReal.ofReal ((K:ℝ)^k) • μ) = ((K^k) • μ)
    simp only [ENNReal.ofReal_pow K.coe_nonneg,ENNReal.ofReal_coe_nnreal]
    rfl
end IntegerChart

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]
variable {T : Functional X 2} {hT : IsMetricCurrent T} (q : ChartGeometry hT)

include q in
lemma exists_almost_euclidean_density (hX : IsCAT0 X) (hM : 0 < mass T)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ o : X, ∀ v : ℝ, 1+ε < v → ∀ d : ℝ, d < Real.pi →
      ∀ᶠ r in 𝓝[>] (0:ℝ), d*(r/v)^2 ≤ (1-ε)⁻¹^2 *
        (MassMeasure.currentMassMeasure hT).real (Metric.ball o r) := by
  obtain ⟨i,s,p,hs,hss,hs0,hθ,hp,hpara,hnear⟩ := q.exists_positive_near_hilbert_piece hX hM hε
  obtain ⟨t,f,ht,ht0,hf,hLip,hdom⟩ := (q.chart i).normalized_piece (q.current i)
    (q.chart_controls_total i) hs hss hs0 hθ p hp hpara hε hε1 hnear
  exact exists_lipschitz_chart_density ht ht0 hf (sq_pos_of_pos (inv_pos.mpr (sub_pos.mpr hε1)))
    (by linarith) hLip hdom
end ChartGeometry
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Density_RadialBound
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings

lemma exists_positive_shell_null_sequence {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] (o : X) :
    ∃ r : ℕ → ℝ, Tendsto r atTop (𝓝[>] 0) ∧
      ∀ j, 0 < r j ∧ μ {x | dist o x = r j} = 0 := by
  have hc := Measure.countable_meas_level_set_pos (μ := μ)
    (continuous_const.dist continuous_id : Continuous (fun x : X => dist o x)).measurable
  have ha : ∀ᵐ t : ℝ, μ {x | dist o x = t} = 0 := by
    filter_upwards [hc.ae_notMem volume] with t ht
    exact le_antisymm (le_of_not_gt ht) bot_le
  have hchoose (j : ℕ) : ∃ r : ℝ, 0 < r ∧ r < 1/((j:ℝ)+1) ∧ μ {x | dist o x = r} = 0 := by
    have hpos : (0:ℝ) < 1/((j:ℝ)+1) := by positivity
    obtain ⟨r,hr,hnull⟩ := (Measure.dense_of_ae ha).inter_open_nonempty _ isOpen_Ioo (nonempty_Ioo.mpr hpos)
    exact ⟨r,hr.1,hr.2,hnull⟩
  choose r hr hrb hrnull using hchoose
  refine ⟨r,?_,fun j => ⟨hr j,hrnull j⟩⟩
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨squeeze_zero (fun j => (hr j).le) (fun j => (hrb j).le)
    tendsto_one_div_add_atTop_nhds_zero_nat,Eventually.of_forall hr⟩

namespace ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]
variable {T : Functional X 2} {hT : IsMetricCurrent T} (q : ChartGeometry hT)

include q in
lemma radial_density_coefficient (hX : IsCAT0 X) (hM : 0 < mass T)
    {ell : ℝ} (hell : 0 < ell)
    (hrad : ∀ o : X, ∀ r : ℝ, 0 < r →
      ell*q.radialVariation o (fun x => inverseSquareCutoff r (dist o x)) ≤
        q.sweptMass o (fun x => inverseSquareCutoff r (dist o x)))
    {ε v d : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hv : 1+ε < v) (hd : d < Real.pi) :
    2*ell*d/v^2 ≤ (1-ε)⁻¹^2*mass T/(8*ell) := by
  obtain ⟨o,ho⟩ := q.exists_almost_euclidean_density hX hM hε hε1
  obtain ⟨r,hr,hrnull⟩ := exists_positive_shell_null_sequence (MassMeasure.currentMassMeasure hT) o
  have hlim : Tendsto r atTop (𝓝 0) := hr.mono_right nhdsWithin_le_nhds
  have hevent := hr.eventually (ho v hv d hd)
  have hsmall := hlim.eventually (eventually_lt_nhds (by linarith : (0:ℝ) < 2*ell))
  have hineq : ∀ᶠ j in atTop,
      (2*ell-r j)*d/v^2 ≤ (1-ε)⁻¹^2*mass T/(8*ell) := by
    filter_upwards [hevent,hsmall] with j hj hjs
    have hu := q.cutoff_mass_upper o (hrnull j).1 hell (hrnull j).2 (hrad o (r j) (hrnull j).1)
    apply (mul_le_mul_iff_left₀ (sq_pos_of_pos (hrnull j).1)).mp
    calc
      _ = (2*ell-r j)*(d*(r j/v)^2) := by ring
      _ ≤ (2*ell-r j)*((1-ε)⁻¹^2*(MassMeasure.currentMassMeasure hT).real (ball o (r j))) :=
        mul_le_mul_of_nonneg_left hj (sub_nonneg.mpr hjs.le)
      _ = (1-ε)⁻¹^2*((2*ell-r j)*(MassMeasure.currentMassMeasure hT).real (ball o (r j))) := by ring
      _ ≤ (1-ε)⁻¹^2*((r j)^2/(8*ell)*mass T) := mul_le_mul_of_nonneg_left hu (sq_nonneg _)
      _ = _ := by ring
  apply le_of_tendsto _ hineq
  simpa only [sub_zero] using ((tendsto_const_nhds.sub hlim).mul_const d).div_const (v^2)

include q in
lemma radial_coefficient_bound_two (hX : IsCAT0 X) (hM : 0 < mass T)
    {ell : ℝ} (hell : 0 < ell)
    (hrad : ∀ o : X, ∀ r : ℝ, 0 < r →
      ell*q.radialVariation o (fun x => inverseSquareCutoff r (dist o x)) ≤
        q.sweptMass o (fun x => inverseSquareCutoff r (dist o x))) :
    16*Real.pi*ell^2 ≤ mass T := by
  let ε (j : ℕ) : ℝ := 1/((j:ℝ)+2)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hε1 (j : ℕ) : ε j < 1 := by
    dsimp [ε]
    apply (div_lt_one (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) j]
  have hlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε,Function.comp_def,Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using
      ((tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 0)).comp (tendsto_add_atTop_nat 1))
  have hi (j : ℕ) := q.radial_density_coefficient hX hM hell hrad (hε j) (hε1 j)
    (show 1+ε j < 1+2*ε j by linarith [hε j]) (show Real.pi-ε j < Real.pi by linarith [hε j])
  have hleft : Tendsto (fun j => 2*ell*(Real.pi-ε j)/(1+2*ε j)^2) atTop (𝓝 (2*ell*Real.pi)) := by
    simpa only [Pi.div_def,Pi.pow_def,mul_zero,add_zero,sub_zero,one_pow,div_one] using ((hlim.const_sub Real.pi).const_mul (2*ell)).div
      (((hlim.const_mul 2).const_add 1).pow 2) (by norm_num : ((1:ℝ)+2*0)^2 ≠ 0)
  have hright : Tendsto (fun j => (1-ε j)⁻¹^2*mass T/(8*ell)) atTop (𝓝 (mass T/(8*ell))) := by
    simpa using ((((hlim.const_sub 1).inv₀ (by norm_num : (1:ℝ)-0 ≠ 0)).pow 2).mul_const (mass T)).div_const (8*ell)
  have hh := le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall hi)
  have hh' := (le_div_iff₀ (by positivity : (0:ℝ) < 8*ell)).mp hh
  nlinarith
end ChartGeometry
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Variational_Ekeland
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.Foundations.testClass_nonempty _root_.OAI.CAT0Fillings.Foundations.unitTestClass_nonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter
open scoped Topology

namespace CAT0Fillings

theorem exists_variational_point {A : Type*} (d : A → A → ℝ)
    (d0 : ∀ x, d x x = 0) (dn : ∀ x y, 0 ≤ d x y)
    (ds : ∀ x y, d x y = d y x) (dt : ∀ x y z, d x z ≤ d x y+d y z)
    (F : A → ℝ) (hF : BddAbove (range F))
    (hcluster : ∀ u : ℕ → A, ∀ L : ℝ,
      Tendsto (fun j => F (u j)) atTop (𝓝 L) →
      (∀ ε > 0, ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N, d (u i) (u j) < ε) →
      ∃ x : A, Tendsto (fun j => d (u j) x) atTop (𝓝 0) ∧ L ≤ F x)
    (x0 : A) {δ : ℝ} (hδ : 0 < δ) :
    ∃ x : A, F x0 ≤ F x ∧ ∀ y : A, F y ≤ F x+δ*d x y := by
  classical
  let R (x y : A) := F x+δ*d x y ≤ F y
  have hrefl x : R x x := by simp only [R,d0,mul_zero,add_zero,le_refl]
  have htrans {x y z : A} (hxy : R x y) (hyz : R y z) : R x z := by
    have hh := mul_le_mul_of_nonneg_left (dt x y z) hδ.le
    dsimp only [R] at *
    nlinarith
  have happ (x : A) (n : ℕ) : ∃ y, R x y ∧ ∀ z, R x z → F z ≤ F y+1/((n:ℝ)+1) := by
    let S : Set ℝ := {r | ∃ y, R x y ∧ r = F y}
    have hn : S.Nonempty := ⟨F x,x,hrefl x,rfl⟩
    have hb : BddAbove S := hF.mono (by rintro r ⟨y,_,rfl⟩; exact mem_range_self y)
    have he : 0 < 1/((n:ℝ)+1) := by positivity
    obtain ⟨r,⟨y,hy,rfl⟩,hr⟩ := exists_lt_of_lt_csSup hn (sub_lt_self (sSup S) he)
    refine ⟨y,hy,fun z hz => ?_⟩
    have hh : F z ≤ sSup S := le_csSup hb ⟨z,hz,rfl⟩
    linarith
  choose next hn hnmax using happ
  let u : ℕ → A := fun n => Nat.rec x0 (fun j x => next x j) n
  have hu0 : u 0 = x0 := rfl
  have hustep n : u (n+1) = next (u n) n := rfl
  have hstep n : R (u n) (u (n+1)) := by rw [hustep]; exact hn _ _
  have hchain {i j : ℕ} (hij : i ≤ j) : R (u i) (u j) := by
    induction j, hij using Nat.le_induction with
    | base => exact hrefl _
    | succ j hij ih => exact htrans ih (hstep j)
  have hmono : Monotone (fun j => F (u j)) := by
    intro i j hij
    have hh := hchain hij
    have hd := mul_nonneg hδ.le (dn (u i) (u j))
    dsimp only [R] at hh
    linarith
  have hb : BddAbove (range (fun j => F (u j))) := hF.mono (by
    rintro r ⟨j,rfl⟩; exact mem_range_self (u j))
  let L : ℝ := ⨆ j, F (u j)
  have hlim : Tendsto (fun j => F (u j)) atTop (𝓝 L) := tendsto_atTop_ciSup hmono hb
  have hle j : F (u j) ≤ L := le_ciSup hb j
  have hcauchy : ∀ ε > 0, ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N, d (u i) (u j) < ε := by
    intro ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hlim.eventually (lt_mem_nhds
      (sub_lt_self L (mul_pos hδ hε))))
    refine ⟨N,fun i hi j hj => ?_⟩
    have hh {i j : ℕ} (hi : N ≤ i) (hij : i ≤ j) : d (u i) (u j) < ε := by
      have hc := hchain hij
      have hn := hN i hi
      have hj := hle j
      dsimp only [R] at hc
      nlinarith
    rcases le_total i j with hij | hji
    · exact hh hi hij
    · rw [ds]; exact hh hj hji
  obtain ⟨x,hdlim,hx⟩ := hcluster u L hlim hcauchy
  have hdcont (i : ℕ) : Tendsto (fun j => d (u i) (u j)) atTop (𝓝 (d (u i) x)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ hdlim
    intro j
    rw [Real.norm_eq_abs]
    apply abs_sub_le_iff.mpr
    have h1 := dt (u i) (u j) x
    have h2 := dt (u i) x (u j)
    rw [←ds (u j) x] at h2
    constructor <;> linarith
  have hux (i : ℕ) : R (u i) x := by
    have hh : F (u i)+δ*d (u i) x ≤ L := by
      apply le_of_tendsto_of_tendsto (tendsto_const_nhds.add ((hdcont i).const_mul δ)) hlim
      filter_upwards [eventually_ge_atTop i] with j hj
      exact hchain hj
    exact hh.trans hx
  have hmax j {y : A} (hy : R (u j) y) : F y ≤ F (u (j+1))+1/((j:ℝ)+1) := by
    rw [hustep]
    exact hnmax _ _ _ hy
  have hlim' : Tendsto (fun j => F (u (j+1))+1/((j:ℝ)+1)) atTop (𝓝 L) := by
    simpa only [Function.comp_def,add_zero] using (hlim.comp (tendsto_add_atTop_nat 1)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun j : ℕ => (1:ℝ)/(j+1)) atTop (𝓝 0))
  have hxle : F x ≤ L := ge_of_tendsto hlim' (Eventually.of_forall fun j => hmax j (hux j))
  refine ⟨x,?_,?_⟩
  · have hh := hux 0
    have hnn := mul_nonneg hδ.le (dn x0 x)
    dsimp only [R] at hh
    rw [hu0] at hh
    linarith
  · intro y
    by_contra hnot
    have hlt : F x+δ*d x y < F y := lt_of_not_ge hnot
    have hy : R x y := hlt.le
    have hyle : F y ≤ L := ge_of_tendsto hlim'
      (Eventually.of_forall fun j => hmax j (htrans (hux j) hy))
    have hnn := mul_nonneg hδ.le (dn x y)
    linarith

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Variational_LowerContinuity
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings
open Foundations Slicing CurrentOperations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem fillingVolume_le_of_bounded_weak_limit (hX : IsCAT0 X) {k : ℕ}
    {Ts : ℕ → Functional X (k+1)} {T : Functional X (k+1)}
    (hTs : ∀ j, IsIntegral (k+1) (Ts j)) (hz : ∀ j, boundarySucc (Ts j) = 0)
    (M B : ℝ≥0) (hM : ∀ j, mass (Ts j) ≤ M) (hB : ∀ j, fillingVolume (Ts j) ≤ B)
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π))) :
    fillingVolume T ≤ B := by
  choose S hS hb hm using fun j => hX.exists_minimal_integral_filling (hTs j) (hz j)
  obtain ⟨ψ,hψ,U,hU,hUm,_,hweak⟩ := exists_integral_weak_subsequence hS B M
    (fun j => by rw [hm]; exact hB j) (fun j => by rw [hb]; exact hM j) hX
  have hboundary : boundarySucc U = T := by
    funext b π
    apply tendsto_nhds_unique (boundarySucc_weak_limit hweak b π)
    simpa only [hb,Function.comp_def] using (hlim b π).comp hψ.tendsto_atTop
  exact (fillingVolume_le hU hboundary).trans hUm

theorem fillingVolume_le_of_eventually_bounded_weak_limit (hX : IsCAT0 X) {k : ℕ}
    {Ts : ℕ → Functional X (k+1)} {T : Functional X (k+1)}
    (hTs : ∀ j, IsIntegral (k+1) (Ts j)) (hz : ∀ j, boundarySucc (Ts j) = 0)
    (M B : ℝ≥0) (hM : ∀ j, mass (Ts j) ≤ M)
    (hB : ∀ᶠ j in atTop, fillingVolume (Ts j) ≤ B)
    (hlim : ∀ b π, Tendsto (fun j => Ts j b π) atTop (𝓝 (T b π))) :
    fillingVolume T ≤ B := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hB
  exact fillingVolume_le_of_bounded_weak_limit hX (fun j => hTs (j+N))
    (fun j => hz (j+N)) M B (fun j => hM (j+N))
    (fun j => hN (j+N) (Nat.le_add_left N j))
    (fun b π => (hlim b π).comp (tendsto_add_atTop_nat N))

theorem fillingVolume_sub_tendsto_zero (hX : IsCAT0 X) {k : ℕ}
    {Ts : ℕ → Functional X (k+1)} {T : Functional X (k+1)}
    (hTs : ∀ j, IsIntegral (k+1) (Ts j)) (hz : ∀ j, boundarySucc (Ts j) = 0)
    (M : ℝ≥0) (hM : ∀ j, mass (Ts j) ≤ M)
    (hcauchy : ∀ ε > 0, ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N,
      fillingVolume (Ts i-Ts j) < ε)
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ)
    (hlim : ∀ b π, Tendsto (fun j => Ts (ψ j) b π) atTop (𝓝 (T b π))) :
    Tendsto (fun j => fillingVolume (Ts j-T)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun j => ha.trans_le (fillingVolume_nonneg _)
  · intro ε hε
    obtain ⟨N,hN⟩ := hcauchy (ε/2) (half_pos hε)
    apply eventually_atTop.mpr
    refine ⟨N,fun i hi => ?_⟩
    have hb : fillingVolume (Ts i-T) ≤ ε/2 := by
      apply fillingVolume_le_of_eventually_bounded_weak_limit hX
        (fun j => (hTs i).sub (hTs (ψ j)))
        (fun j => by rw [boundarySucc_sub,hz,hz,sub_self])
        (M+M) (⟨ε/2,(half_pos hε).le⟩ : ℝ≥0)
      · intro j
        exact (mass_sub_le (hTs i).1 (hTs (ψ j)).1).trans (add_le_add (hM i) (hM (ψ j)))
      · filter_upwards [hψ.tendsto_atTop.eventually (eventually_ge_atTop N)] with j hj
        exact (hN i hi (ψ j) hj).le
      · intro b π
        exact tendsto_const_nhds.sub (hlim b π)
    exact hb.trans_lt (half_lt_self hε)

lemma fillingVolume_tendsto_of_sub_tendsto_zero (hX : IsCAT0 X) {k : ℕ}
    {Ts : ℕ → Functional X (k+1)} {T : Functional X (k+1)}
    (hTs : ∀ j, IsIntegral (k+1) (Ts j)) (hzs : ∀ j, boundarySucc (Ts j) = 0)
    (hT : IsIntegral (k+1) T) (hz : boundarySucc T = 0)
    (hlim : Tendsto (fun j => fillingVolume (Ts j-T)) atTop (𝓝 0)) :
    Tendsto (fun j => fillingVolume (Ts j)) atTop (𝓝 (fillingVolume T)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) (fun j => by
    simpa only [Real.norm_eq_abs] using abs_fillingVolume_sub_le hX (hTs j) (hzs j) hT hz) hlim

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Variational_Extremizer
attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings
open Foundations Slicing CurrentOperations

lemma exists_mass_bound_of_positive_deficit {A c p : ℝ} (hc : 0 < c) (hp : 1 < p) :
    ∃ M : ℝ≥0, ∀ m : ℝ, 0 ≤ m → 0 ≤ A*m-c*m^p → m ≤ M := by
  obtain ⟨R,hR⟩ := eventually_atTop.mp ((tendsto_rpow_atTop (sub_pos.mpr hp)).eventually
    (eventually_ge_atTop ((A+1)/c)))
  refine ⟨⟨max R 1,le_trans zero_le_one (le_max_right _ _)⟩,fun m hm hpos => ?_⟩
  by_contra hnot
  have hlarge : max R 1 < m := lt_of_not_ge hnot
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one ((le_max_right R 1).trans hlarge.le)
  have hh := hR m ((le_max_left R 1).trans hlarge.le)
  have hpow : m^p = m^(p-1)*m := by
    conv_lhs => rw [show p = (p-1)+1 by ring]
    rw [Real.rpow_add hm0,Real.rpow_one]
  have hmul : A+1 ≤ c*m^(p-1) := by
    exact (div_le_iff₀ hc).mp hh |>.trans_eq (mul_comm _ _)
  rw [hpow] at hpos
  nlinarith

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem exists_filling_extremizer (hX : IsCAT0 X) {k : ℕ} {c p δ : ℝ}
    (hc : 0 < c) (hp : 1 < p) (hδ : 0 < δ)
    {T0 : Functional X (k+2)} (hT0 : IsIntegral (k+2) T0) (hz0 : boundarySucc T0 = 0)
    (hpositive : 0 < fillingDeficit c p T0) :
    ∃ T : Functional X (k+2), IsIntegral (k+2) T ∧ boundarySucc T = 0 ∧
      0 < mass T ∧ fillingDeficit c p T0 ≤ fillingDeficit c p T ∧
      ∀ B : Functional X (k+2), IsIntegral (k+2) B → boundarySucc B = 0 →
        c/(1+δ)*((mass T)^p-(mass B)^p) ≤ fillingVolume (T-B) := by
  classical
  have hpos : 0 < fillingVolume T0-c*(mass T0)^p := hpositive
  let A : ℝ := (k+3:ℝ)*diam (univ : Set X)
  have hA : 0 ≤ A := mul_nonneg (by positivity) diam_nonneg
  obtain ⟨M,hM⟩ := exists_mass_bound_of_positive_deficit (A := A) hc hp
  let C := {T : Functional X (k+2) // IsIntegral (k+2) T ∧ boundarySucc T = 0 ∧
    fillingDeficit c p T0 ≤ fillingDeficit c p T}
  let F : C → ℝ := fun T => fillingDeficit c p T.val
  let d : C → C → ℝ := fun T U => fillingVolume (T.val-U.val)
  have hlin (T : C) : fillingVolume T.val ≤ A*mass T.val := by
    simpa only [A,Nat.cast_add,Nat.cast_one,show (1:ℝ)+2 = 3 by norm_num,add_assoc] using
      hX.fillingVolume_le_linear T.property.1 T.property.2.1
  have hmass (T : C) : mass T.val ≤ M := by
    apply hM _ (mass_nonneg _)
    have hh := T.property.2.2
    have hl := hlin T
    dsimp only [fillingDeficit] at hh
    linarith
  have hbound : BddAbove (range F) := by
    refine ⟨A*M,?_⟩
    rintro v ⟨T,rfl⟩
    have hl := hlin T
    have hm := mul_le_mul_of_nonneg_left (hmass T) hA
    have hn := mul_nonneg hc.le (Real.rpow_nonneg (mass_nonneg T.val) p)
    dsimp only [F,fillingDeficit]
    linarith
  have hcluster : ∀ u : ℕ → C, ∀ L : ℝ,
      Tendsto (fun j => F (u j)) atTop (𝓝 L) →
      (∀ ε > 0, ∃ N : ℕ, ∀ i ≥ N, ∀ j ≥ N, d (u i) (u j) < ε) →
      ∃ x : C, Tendsto (fun j => d (u j) x) atTop (𝓝 0) ∧ L ≤ F x := by
    intro u L hL hdc
    obtain ⟨m,hmI,σ,hσ,hm⟩ := isCompact_Icc.isSeqCompact
      (fun j => (show mass (u j).val ∈ Icc (0:ℝ) M from ⟨mass_nonneg _,hmass _⟩))
    obtain ⟨ψ,hψ,T,hT,hTM,_,hweak⟩ := exists_integral_weak_subsequence
      (fun j => (u (σ j)).property.1) M 0 (fun j => hmass _)
      (fun j => by
        rw [(u (σ j)).property.2.1]
        change mass (fun _ _ => (0:ℝ)) ≤ (0:ℝ)
        rw [mass_zero]) hX
    let τ : ℕ → ℕ := σ ∘ ψ
    have hτ : StrictMono τ := hσ.comp hψ
    have hz : boundarySucc T = 0 := by
      funext b π
      apply tendsto_nhds_unique (boundarySucc_weak_limit hweak b π)
      simpa only [(u _).property.2.1,Pi.zero_apply] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
    have hdlim : Tendsto (fun j => fillingVolume ((u j).val-T)) atTop (𝓝 0) :=
      fillingVolume_sub_tendsto_zero hX (fun j => (u j).property.1)
        (fun j => (u j).property.2.1) M (fun j => hmass _) hdc hτ hweak
    have hV := fillingVolume_tendsto_of_sub_tendsto_zero hX
      (fun j => (u j).property.1) (fun j => (u j).property.2.1) hT hz hdlim
    have hmlim : Tendsto (fun j => mass (u (τ j)).val) atTop (𝓝 m) := hm.comp hψ.tendsto_atTop
    have hmle : mass T ≤ m := mass_le_of_mass_tendsto
      (fun j => (u (τ j)).property.1.1) hmlim hweak
    have hFlim : Tendsto (fun j => F (u (τ j))) atTop (𝓝 (fillingVolume T-c*m^p)) :=
      (hV.comp hτ.tendsto_atTop).sub ((hmlim.rpow_const (Or.inr (by linarith))).const_mul c)
    have heq : L = fillingVolume T-c*m^p := tendsto_nhds_unique
      (hL.comp hτ.tendsto_atTop) hFlim
    have hLle : L ≤ fillingDeficit c p T := by
      rw [heq]
      have hpow := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (mass_nonneg T) hmle (by linarith : 0 ≤ p)) hc.le
      dsimp only [fillingDeficit]
      linarith
    have hT0le : fillingDeficit c p T0 ≤ L := ge_of_tendsto hL
      (Eventually.of_forall fun j => (u j).property.2.2)
    exact ⟨⟨T,hT,hz,hT0le.trans hLle⟩,hdlim,hLle⟩
  let x0 : C := ⟨T0,hT0,hz0,le_refl _⟩
  obtain ⟨x,hx0,hx⟩ := exists_variational_point d
    (fun x => by dsimp only [d]; rw [sub_self,fillingVolume_zero])
    (fun x y => fillingVolume_nonneg _)
    (fun x y => fillingVolume_sub_symm hX x.property.1 x.property.2.1 y.property.1 y.property.2.1)
    (fun x y z => fillingVolume_triangle hX x.property.1 x.property.2.1
      y.property.1 y.property.2.1 z.property.1 z.property.2.1)
    F hbound hcluster x0 hδ
  have hx0' : fillingDeficit c p T0 ≤ fillingDeficit c p x.val := hx0
  refine ⟨x.val,x.property.1,x.property.2.1,?_,hx0',?_⟩
  · by_contra hnot
    have hm0 : mass x.val = 0 := le_antisymm (le_of_not_gt hnot) (mass_nonneg _)
    have hl := hlin x
    have hp0 : p ≠ 0 := by linarith
    simp only [hm0,Real.zero_rpow hp0,mul_zero,fillingDeficit] at hl hx0'
    linarith
  · intro B hB hzB
    have hF : fillingDeficit c p B ≤ fillingDeficit c p x.val+δ*fillingVolume (x.val-B) := by
      by_cases hb : fillingDeficit c p T0 ≤ fillingDeficit c p B
      · exact hx ⟨B,hB,hzB,hb⟩
      · have hn := mul_nonneg hδ.le (fillingVolume_nonneg (x.val-B))
        linarith [lt_of_not_ge hb]
    have hV := (le_abs_self (fillingVolume x.val-fillingVolume B)).trans
      (abs_fillingVolume_sub_le hX x.property.1 x.property.2.1 hB hzB)
    have hh : c*((mass x.val)^p-(mass B)^p) ≤ (1+δ)*fillingVolume (x.val-B) := by
      dsimp only [fillingDeficit] at hF
      nlinarith
    have hden : 0 < 1+δ := by linarith
    rw [div_mul_eq_mul_div,div_le_iff₀ hden]
    nlinarith

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Fillings_Compact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

lemma extremal_coefficient_two (hX : IsCAT0 X)
    {T : Functional X 2} (hT : IsIntegral 2 T) (hz : boundarySucc T = 0)
    {c : ℝ} (hc : 0 < c) (hm : 0 < mass T)
    (hext : ∀ B : Functional X 2, IsIntegral 2 B → boundarySucc B = 0 →
      c*((mass T)^((3:ℝ)/2)-(mass B)^((3:ℝ)/2)) ≤ fillingVolume (T-B)) :
    c ≤ fillingCoefficient 2 := by
  obtain ⟨q⟩ := exists_chartGeometry hX hT.1 hT.2.1
  let ell := c*((3:ℝ)/2)*(mass T)^((3:ℝ)/2-1)
  have hell : 0 < ell := by dsimp [ell]; positivity
  have hbound : 16*Real.pi*ell^2 ≤ mass T := by
    apply q.radial_coefficient_bound_two hX hm hell
    intro o r hr
    exact radial_inequality_of_extremal hX hT hz q hc.le (by norm_num) hm hext o
      ((inverseSquareCutoff_lipschitz hr).comp (LipschitzWith.dist_right o))
      (fun _ => inverseSquareCutoff_nonneg _)
      (fun _ => inverseSquareCutoff_le_one hr _)
  have hsq : ell^2 = ((9:ℝ)/4)*c^2*mass T := by
    dsimp [ell]
    rw [show (3:ℝ)/2-1 = 1/2 by norm_num,←Real.sqrt_eq_rpow]
    nlinarith [Real.sq_sqrt hm.le]
  rw [hsq] at hbound
  have hcoef : 36*Real.pi*c^2 ≤ 1 := by
    apply (mul_le_mul_iff_of_pos_right hm).mp
    nlinarith
  have hC := fillingCoefficient_two_pos
  have hCsq := fillingCoefficient_two_sq
  by_contra hn
  have hh : (fillingCoefficient 2)^2 < c^2 := sq_lt_sq₀ hC.le hc.le |>.mpr (lt_of_not_ge hn)
  have hp := mul_lt_mul_of_pos_left hh (show 0 < 36*Real.pi by positivity)
  linarith

lemma fillingVolume_le_two_supercritical (hX : IsCAT0 X)
    {T : Functional X 2} (hT : IsIntegral 2 T) (hz : boundarySucc T = 0)
    {c : ℝ} (hc : fillingCoefficient 2 < c) :
    fillingVolume T ≤ c*(mass T)^((3:ℝ)/2) := by
  by_contra hnot
  have hc0 : 0 < c := fillingCoefficient_two_pos.trans hc
  let δ := (c-fillingCoefficient 2)/(c+fillingCoefficient 2)
  have hsum : 0 < c+fillingCoefficient 2 := add_pos hc0 fillingCoefficient_two_pos
  have hδ : 0 < δ := div_pos (sub_pos.mpr hc) hsum
  obtain ⟨U,hU,hUz,hm,hdef,hext⟩ := exists_filling_extremizer hX hc0
    (by norm_num : (1:ℝ) < 3/2) hδ hT hz (show 0 < fillingDeficit c (3/2) T by
      dsimp [fillingDeficit]; linarith)
  have hden : 0 < 1+δ := by linarith
  have hcoeff : c/(1+δ) = (c+fillingCoefficient 2)/2 := by
    dsimp [δ]
    field_simp [hsum.ne',hc0.ne']
    ring
  have hb := extremal_coefficient_two hX hU hUz (div_pos hc0 hden) hm hext
  rw [hcoeff] at hb
  linarith

theorem fillingVolume_le_two_oai (hX : IsCAT0 X)
    {T : Functional X 2} (hT : IsIntegral 2 T) (hz : boundarySucc T = 0) :
    fillingVolume T ≤ fillingCoefficient 2*(mass T)^fillingPower 2 := by
  rw [fillingPower_two]
  have hlim : Tendsto (fun j : ℕ => (fillingCoefficient 2+1/((j:ℝ)+1))*(mass T)^((3:ℝ)/2))
      atTop (𝓝 (fillingCoefficient 2*(mass T)^((3:ℝ)/2))) := by
    simpa using ((tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun j : ℕ => 1/((j:ℝ)+1)) atTop (𝓝 0)).const_add (fillingCoefficient 2)).mul_const
        ((mass T)^((3:ℝ)/2))
  apply ge_of_tendsto hlim
  exact Eventually.of_forall fun j => fillingVolume_le_two_supercritical hX hT hz
    (lt_add_of_pos_right _ (by positivity))

end CAT0Fillings
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CAT0Fillings.fillingVolume_le_two_oai.{u_1} := @OAI.CAT0Fillings.fillingVolume_le_two_oai.{u_1}
