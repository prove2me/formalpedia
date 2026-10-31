-- Prove2me | solution 1 for OAI.CAT0Fillings.sharp_integral_filling
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T03:15:08.320806+00:00
-- url     : https://prove2.me/submissions/7fd29f51-d061-47e2-8586-28459c3de029

import Mathlib
import Definitions.Def_SharpCAT0Filling
import Definitions.Def_OAIQ29C0002
import Theorems.Thm_OAI_CAT0Fillings_Slicing_exists_integral_weak_subsequence
import Theorems.Thm_OAI_CAT0Fillings_exists_filling_mass_eq
import Theorems.Thm_OAI_CAT0Fillings_fillingVolume_le_two
import Theorems.Thm_OAI_CAT0Fillings_normalized_extremal_contradiction

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Bubble_Euclidean
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Real Set MeasureTheory

namespace CAT0Fillings.RadialSobolev

lemma omega_gamma {k : ℕ} (hk : 0 < k) :
    omega k = Real.sqrt Real.pi ^ k / Real.Gamma ((k:ℝ)/2+1) := by
  let : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  rw [omega, EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  apply ENNReal.toReal_ofReal
  exact div_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (Real.Gamma_pos_of_pos (by positivity)).le

end CAT0Fillings.RadialSobolev
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings

attribute [local instance] Classical.propDecidable

universe u

section Foundations
variable {X : Type u} [MetricSpace X] [MeasurableSpace X]

omit [MeasurableSpace X] in
lemma compactlySupported_zero (k : ℕ) :
    CompactlySupported (fun (_ : X → ℝ) (_ : Fin k → X → ℝ) => 0) :=
  ⟨∅, isCompact_empty, fun _ _ _ _ => rfl⟩

end Foundations
end CAT0Fillings
end

end OAI
end

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

omit [BorelSpace X] in
lemma pushCurrent_id {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T) :
    pushCurrent id T = T := by
  funext b π
  by_cases h : Admissible b π
  · rw [pushCurrent_apply id T h]
    rfl
  · simp only [pushCurrent, ite_eq_right h, hT.offDomain b π h]

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
-- module Solutions.OAIQ29_C0.CAT0Fillings_Currents_IntegralPush
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

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
  [CompactSpace X]
lemma integerRectifiable_push_of_bilipschitz {k : ℕ} {T : Functional X k}
    (hT : IntegerRectifiable T) {f : X → Y} {K J : ℝ≥0}
    (hf : LipschitzWith K f) (hfJ : AntilipschitzWith J f) :
    IntegerRectifiable (pushCurrent f T) := by
  classical
  obtain ⟨C,hdis,hC,hm,heq⟩ := hT
  choose L U hL hU using fun i => (C i).bilipschitz
  let D : ℕ → IntegerChart Y k := fun i => (C i).postcompose hf (hfJ.comp (hU i))
  have hDaction (i : ℕ) : (D i).action = pushCurrent f (C i).action :=
    (C i).postcompose_action hf (hfJ.comp (hU i))
  have hD (i : ℕ) : IsMetricCurrent (D i).action := by
    rw [hDaction]
    exact pushCurrent_isMetricCurrent (hC i) hf
  refine ⟨D,?_,hD,?_,?_⟩
  · intro i j hij
    change Disjoint ((C i).postcompose hf _).image ((C j).postcompose hf _).image
    rw [(C i).postcompose_image,(C j).postcompose_image]
    exact (Set.disjoint_image_iff hfJ.injective).mpr (hdis hij)
  · apply (hm.mul_left ((K : ℝ)^k)).of_nonneg_of_le
    · intro i
      exact mass_nonneg (D i).action
    · intro i
      rw [hDaction]
      exact mass_pushCurrent_le (hC i) hf
  · intro b π
    by_cases h : Admissible b π
    · rw [pushCurrent_apply f T h,heq]
      exact tsum_congr (fun i => by rw [hDaction,pushCurrent_apply f (C i).action h])
    · rw [show pushCurrent f T b π = 0 from ite_eq_right h]
      symm
      calc
        (∑' i, (D i).action b π) = ∑' (_i : ℕ), (0 : ℝ) :=
          tsum_congr (fun i => (hD i).offDomain b π h)
        _ = 0 := tsum_zero

lemma integral_push_of_bilipschitz {k : ℕ} {T : Functional X k}
    (hT : IsIntegral k T) {f : X → Y} {K J : ℝ≥0}
    (hf : LipschitzWith K f) (hfJ : AntilipschitzWith J f) :
    IsIntegral k (pushCurrent f T) := by
  cases k with
  | zero => exact ⟨pushCurrent_isMetricCurrent hT.1 hf,
      integerRectifiable_push_of_bilipschitz hT.2 hf hfJ⟩
  | succ k =>
    refine ⟨pushCurrent_isMetricCurrent hT.1 hf,
      integerRectifiable_push_of_bilipschitz hT.2.1 hf hfJ,?_,?_⟩
    · rw [pushCurrent_boundarySucc T hf]
      exact pushCurrent_isMetricCurrent hT.2.2.1 hf
    · rw [pushCurrent_boundarySucc T hf]
      exact integerRectifiable_push_of_bilipschitz hT.2.2.2 hf hfJ

end CAT0Fillings

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
-- module Solutions.OAIQ29_C0.CAT0Fillings_Transport_Sharp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace CAT0Fillings.RadialSobolev

lemma omega_pos {n : ℕ} (hn : 0 < n) : 0 < omega n := by
  rw [omega_gamma hn]
  have h : (0:ℝ) < n := by exact_mod_cast hn
  exact div_pos (pow_pos (Real.sqrt_pos.mpr Real.pi_pos) _) (Real.Gamma_pos_of_pos (by positivity))

end CAT0Fillings.RadialSobolev
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Rearrangement_Inverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace CAT0Fillings
open RadialSobolev

lemma fillingCoefficient_pos {m : ℕ} (hm : 0 < m) : 0 < fillingCoefficient m := by
  unfold fillingCoefficient sphereArea
  have hω := omega_pos (Nat.succ_pos m)
  positivity

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Scaling_Metric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings
open RadialSobolev

lemma power_mul_dimension {n : ℕ} (hn : 0 < n) : (n:ℝ)*fillingPower n = n+1 := by
  unfold fillingPower
  field [Nat.cast_ne_zero.mpr hn.ne']
lemma fillingPower_gt_one {n : ℕ} (hn : 0 < n) : 1 < fillingPower n := by
  unfold fillingPower
  exact (lt_div_iff₀ (Nat.cast_pos.mpr hn)).mpr (by linarith)
lemma normalized_scale {n : ℕ} (hn : 0 < n) {m c : ℝ} (hm : 0 < m)
    (hc : fillingCoefficient n < c) :
    ∃ l : ℝ, 0 < l ∧ 0 < l^n*m ∧ l^n*m < sphereArea n ∧
      c*fillingPower n*(l^n*m)^(fillingPower n-1) = 1/(n:ℝ) := by
  have hn0 : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hnp : 0 < (n+1:ℝ) := by positivity
  have hs : 0 < sphereArea n := mul_pos hnp (omega_pos (by omega))
  have hc0 := (fillingCoefficient_pos hn).trans hc
  let r := 1/((n+1:ℝ)*c)
  have hr : 0 < r := by dsimp [r]; positivity
  have hroot : r < (sphereArea n)^(1/(n:ℝ)) := by
    apply (div_lt_iff₀ (mul_pos hnp hc0)).mpr
    have h := (div_lt_iff₀ (mul_pos hnp (Real.rpow_pos_of_pos hs _))).mp hc
    nlinarith
  have hsr : ((sphereArea n)^(1/(n:ℝ)))^n = sphereArea n := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hs.le,one_div_mul_cancel hn0.ne',Real.rpow_one]
  have hM : r^n < sphereArea n := by
    rw [←hsr]
    exact pow_lt_pow_left₀ hroot hr.le (by omega)
  have hp : fillingPower n-1 = 1/(n:ℝ) := by
    unfold fillingPower
    field [hn0.ne']
  have hMr : (r^n)^(1/(n:ℝ)) = r := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hr.le,mul_one_div_cancel hn0.ne',Real.rpow_one]
  let l := (r^n/m)^(1/(n:ℝ))
  have hl : 0 < l := Real.rpow_pos_of_pos (div_pos (pow_pos hr _) hm) _
  have hmass : l^n*m = r^n := by
    dsimp [l]
    rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity : 0 ≤ r^n/m),
      one_div_mul_cancel hn0.ne',Real.rpow_one,div_mul_cancel₀ _ hm.ne']
  refine ⟨l,hl,by rw [hmass]; positivity,by rwa [hmass],?_⟩
  rw [hmass,hp,hMr]
  dsimp [r,fillingPower]
  field [hn0.ne',hc0.ne']
end CAT0Fillings
end

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings

namespace ScaledSpace
variable {X : Type*} [m : MetricSpace X] (c : ℝ≥0) [NeZero c]
omit m [NeZero c] in
lemma to_of (x : X) : toBase c (ofBase c x) = x := rfl
lemma dist_eq (x y : ScaledSpace X c) : dist x y = (c:ℝ)*dist (toBase c x) (toBase c y) := rfl
lemma up_lipschitz : LipschitzWith c (ofBase (X := X) c) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact le_rfl
lemma down_lipschitz : LipschitzWith c⁻¹ (toBase (X := X) c) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq,NNReal.coe_inv]
  have hc : (c:ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr (NeZero.ne c)
  rw [←mul_assoc,inv_mul_cancel₀ hc,one_mul]

lemma isCAT0 (hX : IsCAT0 X) : IsCAT0 (ScaledSpace X c) := by
  obtain ⟨s,he,hs,hc⟩ := hX
  refine ⟨fun x y t => ofBase c (s (toBase c x) (toBase c y) t),?_,?_,?_⟩
  · intro x y
    exact ⟨congrArg (ofBase c) (he (toBase c x) (toBase c y)).1,
      congrArg (ofBase c) (he (toBase c x) (toBase c y)).2⟩
  · intro x y u v hu hv
    simp only [dist_eq,to_of]
    rw [hs (toBase c x) (toBase c y) u v hu hv]
    ring
  · intro o x y u v hu hv
    have h := mul_le_mul_of_nonneg_left (hc (toBase c o) (toBase c x) (toBase c y) u v hu hv) (sq_nonneg (c:ℝ))
    simp only [dist_eq,to_of]
    convert h using 1 <;> first | rfl | ring
end ScaledSpace
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Scaling_Extremal
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

namespace CAT0Fillings.ScaledSpace
open CurrentOperations

lemma push_down_up {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [Nonempty X] (c : ℝ≥0) [NeZero c]
    {n : ℕ} {T : Functional X n} (hT : IsMetricCurrent T) :
    pushCurrent (toBase c) (pushCurrent (ofBase c) T) = T := by
  rw [←pushCurrent_comp (down_lipschitz c)]
  exact pushCurrent_id hT
lemma push_up_down {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [Nonempty X] (c : ℝ≥0) [NeZero c]
    {n : ℕ} {T : Functional (ScaledSpace X c) n} (hT : IsMetricCurrent T) :
    pushCurrent (ofBase c) (pushCurrent (toBase c) T) = T := by
  rw [←pushCurrent_comp (up_lipschitz c)]
  exact pushCurrent_id hT
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] (c : ℝ≥0) [NeZero c]
lemma mass_up {n : ℕ} {T : Functional X n} (hT : IsMetricCurrent T) :
    mass (pushCurrent (ofBase c) T) = (c:ℝ)^n*mass T := by
  have hc : 0 < (c:ℝ) := NNReal.coe_pos.mpr (pos_of_ne_zero (NeZero.ne c))
  apply le_antisymm (mass_pushCurrent_le hT (up_lipschitz c))
  have hl := mass_pushCurrent_le (pushCurrent_isMetricCurrent hT (up_lipschitz c)) (down_lipschitz c)
  rw [push_down_up c hT,NNReal.coe_inv,inv_pow] at hl
  have hh := mul_le_mul_of_nonneg_left hl (pow_nonneg hc.le n)
  simpa only [←mul_assoc,mul_inv_cancel₀ (pow_ne_zero n hc.ne'),one_mul] using hh
lemma mass_down {n : ℕ} {T : Functional (ScaledSpace X c) n} (hT : IsMetricCurrent T) :
    mass (pushCurrent (toBase c) T) = ((c:ℝ)^n)⁻¹*mass T := by
  have h := mass_up c (pushCurrent_isMetricCurrent hT (down_lipschitz c))
  rw [push_up_down c hT] at h
  rw [h,←mul_assoc,inv_mul_cancel₀ (pow_ne_zero n (NNReal.coe_ne_zero.mpr (NeZero.ne c))),one_mul]
lemma filling_up (hX : IsCAT0 X) {k : ℕ} {T : Functional X (k+1)}
    (hT : IsIntegral (k+1) T) (hz : boundarySucc T = 0) :
    fillingVolume (pushCurrent (ofBase c) T) = (c:ℝ)^(k+2)*fillingVolume T := by
  have hTi := integral_push hT (up_lipschitz c)
  have hTz := pushCurrent_cycle hz (up_lipschitz c)
  obtain ⟨S,hS,hSb,hSm⟩ := hX.exists_minimal_integral_filling hT hz
  obtain ⟨R,hR,hRb,hRm⟩ := (isCAT0 c hX).exists_minimal_integral_filling hTi hTz
  apply le_antisymm
  · have hh := fillingVolume_le (integral_push hS (up_lipschitz c))
      (by rw [pushCurrent_boundarySucc S (up_lipschitz c),hSb])
    simpa only [mass_up c hS.1,hSm] using hh
  · have hh := fillingVolume_le (integral_push hR (down_lipschitz c))
      (show boundarySucc (pushCurrent (toBase c) R) = T by
        rw [pushCurrent_boundarySucc R (down_lipschitz c),hRb,push_down_up c hT.1])
    rw [mass_down c hR.1,hRm] at hh
    have hm := mul_le_mul_of_nonneg_left hh (pow_nonneg c.coe_nonneg (k+2))
    simpa only [←mul_assoc,mul_inv_cancel₀
      (pow_ne_zero (k+2) (NNReal.coe_ne_zero.mpr (NeZero.ne c))),one_mul] using hm
end CAT0Fillings.ScaledSpace
end

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings.ScaledSpace
open CurrentOperations

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] (c : ℝ≥0) [NeZero c]
lemma mass_up_rpow {n : ℕ} {T : Functional X n} (hT : IsMetricCurrent T) (p : ℝ) :
    (mass (pushCurrent (ofBase c) T))^p = (c:ℝ)^((n:ℝ)*p)*(mass T)^p := by
  rw [mass_up c hT,Real.mul_rpow (pow_nonneg c.coe_nonneg n) (mass_nonneg T),
    ←Real.rpow_natCast (c:ℝ) n,←Real.rpow_mul c.coe_nonneg]
lemma extremal_up (hX : IsCAT0 X) {k : ℕ} {T : Functional X (k+1)}
    (hT : IsIntegral (k+1) T) (hz : boundarySucc T = 0) {d p : ℝ}
    (hp : (k+1:ℝ)*p = (k+2:ℝ))
    (hext : ∀ B : Functional X (k+1), IsIntegral (k+1) B → boundarySucc B = 0 →
      d*((mass T)^p-(mass B)^p) ≤ fillingVolume (T-B)) :
    ∀ B : Functional (ScaledSpace X c) (k+1), IsIntegral (k+1) B → boundarySucc B = 0 →
      d*((mass (pushCurrent (ofBase c) T))^p-(mass B)^p) ≤
        fillingVolume (pushCurrent (ofBase c) T-B) := by
  intro B hB hBz
  let D := pushCurrent (toBase c) B
  have hD : IsIntegral (k+1) D := integral_push hB (down_lipschitz c)
  have hDz : boundarySucc D = 0 := pushCurrent_cycle hBz (down_lipschitz c)
  have hDB : pushCurrent (ofBase c) D = B := push_up_down c hB.1
  have hsub : pushCurrent (ofBase c) (T-D) = pushCurrent (ofBase c) T-B := by
    rw [←hDB]
    funext b π
    simp only [pushCurrent,Pi.sub_apply]
    split <;> simp
  have hp' : ((k+1:ℕ):ℝ)*p = ((k+2:ℕ):ℝ) := by simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] using hp
  have h := mul_le_mul_of_nonneg_left (hext D hD hDz) (pow_nonneg c.coe_nonneg (k+2))
  rw [←filling_up c hX (hT.sub hD) (by rw [boundarySucc_sub,hz,hDz,sub_self]),hsub] at h
  have hmp := mass_up_rpow c hT.1 p
  have hmd := mass_up_rpow c hD.1 p
  rw [hp',Real.rpow_natCast] at hmp hmd
  rw [hDB] at hmd
  rw [hmp,hmd]
  convert h using 1 <;> first | rfl | ring
end CAT0Fillings.ScaledSpace
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Scaling_HighCoefficient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings
open CurrentOperations

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]
theorem extremal_coefficient_high {k : ℕ} (hk : 0 < k) (hX : IsCAT0 X)
    {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hz : boundarySucc T = 0)
    {c : ℝ} (hc : 0 < c) (hm : 0 < mass T)
    (hfill : ∀ (Y : Type u) [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
        [CompactSpace Y] [Nonempty Y], IsCAT0 Y →
      ∀ P : Functional Y (k+1), IsIntegral (k+1) P → boundarySucc P = 0 →
      fillingVolume P ≤ fillingCoefficient (k+1)*(mass P)^(fillingPower (k+1)))
    (hext : ∀ B : Functional X (k+2), IsIntegral (k+2) B → boundarySucc B = 0 →
      c*((mass T)^(fillingPower (k+2))-(mass B)^(fillingPower (k+2))) ≤ fillingVolume (T-B)) :
    c ≤ fillingCoefficient (k+2) := by
  by_contra hn
  obtain ⟨l,hl,hlm,hls,hln⟩ := normalized_scale (by omega : 0 < k+2) hm (lt_of_not_ge hn)
  let a : ℝ≥0 := ⟨l,hl.le⟩
  have : NeZero a := ⟨by exact NNReal.coe_ne_zero.mp hl.ne'⟩
  let Y := ScaledSpace X a
  have hY : IsCAT0 Y := ScaledSpace.isCAT0 a hX
  let U := pushCurrent (ScaledSpace.ofBase a) T
  have hU : IsIntegral (k+2) U := integral_push hT (ScaledSpace.up_lipschitz a)
  have hUz : boundarySucc U = 0 := pushCurrent_cycle hz (ScaledSpace.up_lipschitz a)
  have hUm : mass U = l^(k+2)*mass T := ScaledSpace.mass_up a hT.1
  have hUe := ScaledSpace.extremal_up a hX hT hz
    (by convert power_mul_dimension (by omega : 0 < k+2) using 1 <;> push_cast <;> ring) hext
  apply normalized_extremal_contradiction hk hY hU hUz (by rwa [hUm]) (by rwa [hUm]) hc
    (fillingPower_gt_one (by omega)) (by simpa only [Nat.cast_add,Nat.cast_ofNat,hUm] using hln) ?_ hUe
  intro P hP hPz
  obtain ⟨R,hR,hRb,hRm⟩ := hY.exists_minimal_integral_filling hP hPz
  exact ⟨R,hR,hRb,by rw [hRm]; exact hfill Y hY P hP hPz⟩
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
universe u
lemma fillingVolume_le_of_coefficient {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] [Nonempty X] (hX : IsCAT0 X) {k : ℕ}
    (hcoef : ∀ U : Functional X (k+2), IsIntegral (k+2) U → IsCycle U →
      ∀ c : ℝ, 0 < c → 0 < mass U →
      (∀ B : Functional X (k+2), IsIntegral (k+2) B → IsCycle B →
        c*((mass U)^(fillingPower (k+2))-(mass B)^(fillingPower (k+2))) ≤ fillingVolume (U-B)) →
      c ≤ fillingCoefficient (k+2))
    {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hz : IsCycle T) :
    fillingVolume T ≤ fillingCoefficient (k+2)*(mass T)^(fillingPower (k+2)) := by
  have hsuper (c : ℝ) (hc : fillingCoefficient (k+2) < c) :
      fillingVolume T ≤ c*(mass T)^(fillingPower (k+2)) := by
    by_contra hnot
    have hc0 := (fillingCoefficient_pos (by omega : 0 < k+2)).trans hc
    let δ := (c-fillingCoefficient (k+2))/(c+fillingCoefficient (k+2))
    have hsum : 0 < c+fillingCoefficient (k+2) := add_pos hc0 (fillingCoefficient_pos (by omega))
    have hδ : 0 < δ := div_pos (sub_pos.mpr hc) hsum
    obtain ⟨U,hU,hUz,hm,hdef,hext⟩ := exists_filling_extremizer hX hc0
      (fillingPower_gt_one (by omega : 0 < k+2)) hδ hT hz
      (show 0 < fillingDeficit c (fillingPower (k+2)) T by dsimp [fillingDeficit]; linarith)
    have hden : 0 < 1+δ := by linarith
    have hcoeff : c/(1+δ) = (c+fillingCoefficient (k+2))/2 := by
      dsimp [δ]
      field_simp [hsum.ne',hc0.ne']
      ring
    have hb := hcoef U hU hUz (c/(1+δ)) (div_pos hc0 hden) hm hext
    rw [hcoeff] at hb
    linarith
  have hlim : Tendsto (fun j : ℕ => (fillingCoefficient (k+2)+1/((j:ℝ)+1))*(mass T)^(fillingPower (k+2)))
      atTop (𝓝 (fillingCoefficient (k+2)*(mass T)^(fillingPower (k+2)))) := by
    simpa using ((tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun j : ℕ => 1/((j:ℝ)+1)) atTop (𝓝 0)).const_add (fillingCoefficient (k+2))).mul_const
        ((mass T)^(fillingPower (k+2)))
  apply ge_of_tendsto hlim
  exact Eventually.of_forall fun j => hsuper _ (lt_add_of_pos_right _ (by positivity))

theorem compact_filling_bound : ∀ k : ℕ,
    ∀ (X : Type u) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [Nonempty X],
      IsCAT0 X → ∀ T : Functional X (k+2), IsIntegral (k+2) T → boundarySucc T = 0 →
        fillingVolume T ≤ fillingCoefficient (k+2)*(mass T)^(fillingPower (k+2)) := by
  intro k
  induction k with
  | zero =>
    intro X _ _ _ _ _ hX T hT hz
    exact fillingVolume_le_two hX hT hz
  | succ k ih =>
    intro X _ _ _ _ _ hX T hT hz
    apply fillingVolume_le_of_coefficient hX ?_ hT hz
    intro U hU hUz c hc hm hext
    exact extremal_coefficient_high (by omega) hX hU hUz hc hm ih hext
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Geometry_Ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings
universe u

private lemma cutoffRatio_mem {R r : ℝ} (hR : 0 ≤ R) (hr : 0 ≤ r) :
    cutoffRatio R r ∈ Icc (0 : ℝ) 1 := by
  unfold cutoffRatio
  split_ifs with h
  · norm_num
  · have hr' : 0 < r := lt_of_le_of_lt hR (lt_of_not_ge h)
    exact ⟨div_nonneg hR hr, (div_le_one hr').mpr (le_of_lt (lt_of_not_ge h))⟩

private lemma cutoffRatio_mul {R r : ℝ} (hR : 0 ≤ R) :
    cutoffRatio R r * r = min r R := by
  unfold cutoffRatio
  split_ifs with h
  · simp [min_eq_left h]
  · have hr' : 0 < r := lt_of_le_of_lt hR (lt_of_not_ge h)
    simp [div_mul_cancel₀ _ hr'.ne', min_eq_right (le_of_lt (lt_of_not_ge h))]

theorem IsCAT0.exists_ball_retraction {X : Type u} [MetricSpace X] (hX : IsCAT0 X)
    (o : X) {R : ℝ} (hR : 0 ≤ R) :
    ∃ P : X → X, LipschitzWith 1 P ∧
      (∀ x, dist o (P x) ≤ R) ∧ (∀ x, dist o x ≤ R → P x = x) := by
  obtain ⟨s, hs, hd, hc⟩ := hX
  let q : X → ℝ := fun x => cutoffRatio R (dist o x)
  have hq (x : X) : q x ∈ Icc (0 : ℝ) 1 := cutoffRatio_mem hR dist_nonneg
  have hm (x : X) : q x * dist o x = min (dist o x) R :=
    cutoffRatio_mul hR
  let P : X → X := fun x => s o x (q x)
  refine ⟨P, ?_, ?_, ?_⟩
  · apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    have hh := hc o x y (q x) (q y) (hq x) (hq y)
    rw [hm x, hm y] at hh
    have hc₀ : 0 ≤ dist x y ^ 2 - (dist o x - dist o y) ^ 2 := by
      have hh' := abs_dist_sub_le x y o
      rw [dist_comm x o, dist_comm y o] at hh'
      have hh'' := (sq_le_sq₀ (abs_nonneg _) dist_nonneg).mpr hh'
      rw [sq_abs] at hh''
      linarith
    have hqq : q x * q y ≤ 1 := by
      nlinarith [(hq x).1, (hq y).1, (hq x).2, (hq y).2,
        mul_nonneg (sub_nonneg.mpr (hq x).2) (sub_nonneg.mpr (hq y).2)]
    have hmin := (LipschitzWith.id.min_const R).dist_le_mul (dist o x) (dist o y)
    simp only [id_eq, Real.dist_eq, NNReal.coe_one, one_mul] at hmin
    have hmin' := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr hmin
    simp only [sq_abs] at hmin'
    have hmul := mul_le_mul_of_nonneg_right hqq hc₀
    have hsq : dist (P x) (P y) ^ 2 ≤ dist x y ^ 2 := by
      change dist (s o x (q x)) (s o y (q y)) ^ 2 ≤ _
      nlinarith
    simpa using (sq_le_sq₀ dist_nonneg dist_nonneg).mp hsq
  · intro x
    have hh := hd o x 0 (q x) (by simp) (hq x)
    rw [(hs o x).1] at hh
    simp only [zero_sub, abs_neg, abs_of_nonneg (hq x).1] at hh
    change dist o (s o x (q x)) ≤ R
    rw [hh, hm x]
    exact min_le_right _ _
  · intro x hx
    change s o x (cutoffRatio R (dist o x)) = x
    simp only [cutoffRatio, ite_eq_left hx]
    exact (hs o x).2

theorem IsCAT0.closedBall {X : Type u} [MetricSpace X] (hX : IsCAT0 X)
    (o : X) {R : ℝ} (hR : 0 ≤ R) : IsCAT0 (Metric.closedBall o R) := by
  obtain ⟨s, hs, hd, hc⟩ := hX
  have hconv (x y : Metric.closedBall o R) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      s x.val y.val t ∈ Metric.closedBall o R := by
    have hh := hc x.val y.val o t 1 ht (by simp)
    rw [(hs x.val o).2] at hh
    have he : (t * dist x.val y.val - 1 * dist x.val o) ^ 2 +
          t * 1 * (dist y.val o ^ 2 - (dist x.val y.val - dist x.val o) ^ 2) =
        (1 - t) * dist x.val o ^ 2 + t * dist y.val o ^ 2 -
          t * (1 - t) * dist x.val y.val ^ 2 := by ring
    rw [he] at hh
    have hx := (sq_le_sq₀ dist_nonneg hR).mpr x.property
    have hy := (sq_le_sq₀ dist_nonneg hR).mpr y.property
    have hx' := mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr ht.2)
    have hy' := mul_le_mul_of_nonneg_left hy ht.1
    have hh' : dist (s x.val y.val t) o ^ 2 ≤ R ^ 2 := by
      nlinarith [mul_nonneg (mul_nonneg ht.1 (sub_nonneg.mpr ht.2))
        (sq_nonneg (dist x.val y.val))]
    exact (sq_le_sq₀ dist_nonneg hR).mp hh'
  let clamp : ℝ → ℝ := fun t => max 0 (min 1 t)
  have hclamp (t : ℝ) : clamp t ∈ Icc (0 : ℝ) 1 := by
    exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  have hclamp_eq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : clamp t = t := by
    simp only [clamp, min_eq_right ht.2, max_eq_right ht.1]
  let sB : Metric.closedBall o R → Metric.closedBall o R → ℝ →
      Metric.closedBall o R := fun x y t => ⟨s x.val y.val (clamp t), hconv x y _ (hclamp t)⟩
  refine ⟨sB, ?_, ?_, ?_⟩
  · intro x y
    constructor <;> apply Subtype.ext
    · change s x.val y.val (clamp 0) = x.val
      rw [hclamp_eq _ (by simp), (hs x.val y.val).1]
    · change s x.val y.val (clamp 1) = y.val
      rw [hclamp_eq _ (by simp), (hs x.val y.val).2]
  · intro x y u v hu hv
    change dist (s x.val y.val (clamp u)) (s x.val y.val (clamp v)) = _
    rw [hclamp_eq _ hu, hclamp_eq _ hv]
    exact hd x.val y.val u v hu hv
  · intro p x y u v hu hv
    change dist (s p.val x.val (clamp u)) (s p.val y.val (clamp v)) ^ 2 ≤ _
    rw [hclamp_eq _ hu, hclamp_eq _ hv]
    exact hc p.val x.val y.val u v hu hv

end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Transport_Proper
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
attribute [-simp] _root_.OAI.CAT0Fillings.ChartGeometry.closedGradient_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.gradientProjection_graphPoint _root_.OAI.CAT0Fillings.ChartGeometry.inclusion_lipSobolev _root_.OAI.CAT0Fillings.ChartGeometry.valueProjection_graphPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
open Foundations CurrentOperations

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
lemma mass_push_one_general {k : ℕ} {T : Functional X k} (hT : IsMetricCurrent T)
    {f : X → Y} (hf : LipschitzWith 1 f) : mass (pushCurrent f T) ≤ mass T := by
  apply le_csInf
  · obtain ⟨μ,hμ,hc⟩ := hT.finiteMass
    exact ⟨μ.real univ,μ,hμ,hc,rfl⟩
  · rintro r ⟨μ,hμ,hc,rfl⟩
    let := hμ
    have hh := pushCurrent_controls hT hc hf
    simp only [one_pow,ENNReal.coe_one,one_smul] at hh
    have hl := mass_le_measure (T := pushCurrent f T) (μ := μ.map f) inferInstance hh
    simpa only [Measure.real,Measure.map_apply hf.continuous.measurable MeasurableSet.univ,
      preimage_univ] using hl

omit [MeasurableSpace X] [BorelSpace X] in
lemma IntegerChart.image_bounded {k : ℕ} (C : IntegerChart X k) : Bornology.IsBounded C.image := by
  obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
  obtain ⟨R,hR⟩ := Metric.isBounded_iff.mp C.bounded
  apply Metric.isBounded_iff.mpr
  refine ⟨(L:ℝ)*R,?_⟩
  rintro x ⟨a,rfl⟩ y ⟨b,rfl⟩
  exact (hL.dist_le_mul a b).trans (mul_le_mul_of_nonneg_left
    (hR a.property b.property) L.coe_nonneg)

lemma IntegerChart.push_integerRectifiable_proper [ProperSpace X] [Nonempty X]
    [CompactSpace Y] [Nonempty Y] {k : ℕ} (C : IntegerChart X k)
    {f : X → Y} (hf : LipschitzWith 1 f) : IntegerRectifiable (pushCurrent f C.action) := by
  classical
  let o : X := Classical.choice inferInstance
  obtain ⟨R,hR,him⟩ := C.image_bounded.subset_closedBall_lt 0 o
  let B := closedBall o R
  have : Nonempty B := ⟨o,by simp [B,hR.le]⟩
  let D : IntegerChart B k := {
    domain := C.domain
    borel := C.borel
    bounded := C.bounded
    param := fun z => ⟨C.param z,him ⟨z,rfl⟩⟩
    bilipschitz := by
      obtain ⟨L,U,hL,hU⟩ := C.bilipschitz
      exact ⟨L,U,hL,hU⟩
    multiplicity := C.multiplicity
    integrable := C.integrable }
  have hinc : LipschitzWith 1 (Subtype.val : B → X) := LipschitzWith.subtype_val B
  have heq : C.action = pushCurrent (Subtype.val : B → X) D.action := by
    funext b π
    by_cases hab : Admissible b π
    · rw [pushCurrent_apply _ _ hab,IntegerChart.action,ite_eq_left hab,
        IntegerChart.action,ite_eq_left (admissible_comp hab hinc)]
      rfl
    · simp only [IntegerChart.action,pushCurrent,ite_eq_right hab]
  rw [heq,←pushCurrent_comp hf]
  exact D.push_integerRectifiable D.action_isMetricCurrent (hf.comp hinc)

lemma integerRectifiable_push_proper [ProperSpace X] [Nonempty X]
    [CompactSpace Y] [Nonempty Y] {k : ℕ} {T : Functional X k} (hT : IntegerRectifiable T)
    {f : X → Y} (hf : LipschitzWith 1 f) : IntegerRectifiable (pushCurrent f T) := by
  classical
  obtain ⟨C,hd,hC,hCS,heq⟩ := hT
  have hP i : IsMetricCurrent (pushCurrent f (C i).action) := pushCurrent_isMetricCurrent (hC i) hf
  have hPI i : IntegerRectifiable (pushCurrent f (C i).action) := (C i).push_integerRectifiable_proper hf
  have hPS : Summable (fun i => mass (pushCurrent f (C i).action)) :=
    hCS.of_nonneg_of_le (fun i => mass_nonneg _) (fun i => mass_push_one_general (hC i) hf)
  have hEq : pushCurrent f T = (fun b π => ∑' i, pushCurrent f (C i).action b π) := by
    funext b π
    by_cases hab : Admissible b π
    · simp_rw [pushCurrent_apply f _ hab]
      exact heq _ _
    · simp only [pushCurrent,ite_eq_right hab,tsum_zero]
  rw [hEq]
  exact integerRectifiable_tsum hP hPI hPS
lemma integral_push_proper [ProperSpace X] [Nonempty X]
    [CompactSpace Y] [Nonempty Y] {k : ℕ} {T : Functional X k} (hT : IsIntegral k T)
    {f : X → Y} (hf : LipschitzWith 1 f) : IsIntegral k (pushCurrent f T) := by
  cases k with
  | zero => exact ⟨pushCurrent_isMetricCurrent hT.1 hf,integerRectifiable_push_proper hT.2 hf⟩
  | succ k =>
    refine ⟨pushCurrent_isMetricCurrent hT.1 hf,integerRectifiable_push_proper hT.2.1 hf,?_,?_⟩
    · rw [pushCurrent_boundarySucc T hf]
      exact pushCurrent_isMetricCurrent hT.2.2.1 hf
    · rw [pushCurrent_boundarySucc T hf]
      exact integerRectifiable_push_proper hT.2.2.2 hf
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Transport_Support
attribute [-instance] _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable _root_.OAI.CAT0Fillings.MassMeasure.currentMassMeasure_finite _root_.OAI.CAT0Fillings.Slicing.fullSliceControl_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings
open CurrentOperations

variable {X : Type*} [MetricSpace X]
lemma IsMetricCurrent.coord_congr_on [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {T : Functional X n} (hT : IsMetricCurrent T)
    {b : X → ℝ} (hb : BoundedLip b) {π σ : Fin n → X → ℝ}
    (hπ : ∀ i, ∃ K, LipschitzWith K (π i)) (hσ : ∀ i, ∃ K, LipschitzWith K (σ i))
    {U : Set X} (hU : IsOpen U) (hbU : Function.support b ⊆ U)
    (heq : ∀ i, EqOn (π i) (σ i) U) : T b π = T b σ := by
  classical
  let a : Fin n → lipSubmodule (X := X) := fun i => ⟨π i,hπ i⟩
  let c : Fin n → lipSubmodule (X := X) := fun i => ⟨σ i,hσ i⟩
  let M := hT.multilinear b hb
  have hd := M.map_sub_map_piecewise a c Finset.univ
  simp only [Finset.piecewise_univ,Finset.mem_univ,true_implies] at hd
  have hz : ∀ i : Fin n, M (fun j => if j < i then a j else if i=j then a j-c j else c j) = 0 := by
    intro i
    apply hT.locality b _ ⟨hb,fun j => (if j < i then a j else if i=j then a j-c j else c j).property⟩
    refine ⟨i,U,0,hU,hbU,?_⟩
    intro x hx
    simp only [lt_self_iff_false,ite_false, if_false,ite_true, if_true,Submodule.coe_sub,Pi.sub_apply,a,c]
    exact sub_eq_zero.mpr (heq i hx)
  simp only [hz,Finset.sum_const_zero] at hd
  exact sub_eq_zero.mp hd
lemma IsMetricCurrent.first_congr_support [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {T : Functional X n} (hT : IsMetricCurrent T)
    {K : Set X} (hK : ∀ b π, Admissible b π → (∀ x ∈ K, b x = 0) → T b π = 0)
    {b c : X → ℝ} {π : Fin n → X → ℝ} (hb : BoundedLip b) (hc : BoundedLip c)
    (hπ : ∀ i, ∃ L, LipschitzWith L (π i)) (heq : EqOn b c K) : T b π = T c π := by
  have hz := hK (fun x => 1*b x+(-1)*c x) π
    ⟨(hb.const_mul 1).add (hc.const_mul (-1)),hπ⟩ (fun x hx => by rw [heq hx]; ring)
  rw [hT.linearFirst b c π 1 (-1) hb hc hπ] at hz
  linarith
lemma ballCutoff_boundedLip [MeasurableSpace X] [BorelSpace X]
    (o : X) (R : ℝ) : BoundedLip (ballCutoff o R) := by
  refine ⟨⟨1,?_⟩,1,?_⟩
  · change LipschitzWith 1 (fun x => min 1 (max 0 (R+1-dist x o)))
    simpa only [zero_add] using (((LipschitzWith.const (R+1)).sub (LipschitzWith.dist_left o)).const_max 0).const_min 1
  · intro x
    rw [abs_of_nonneg (le_min (by norm_num) (le_max_left _ _))]
    exact min_le_left _ _
lemma ballCutoff_one [MeasurableSpace X] [BorelSpace X]
    (o : X) (R : ℝ) {x : X} (hx : x ∈ closedBall o R) : ballCutoff o R x = 1 := by
  have hh : 1 ≤ R+1-dist x o := by have := hx; change dist x o ≤ R at this; linarith
  exact min_eq_left (hh.trans (le_max_right _ _))
lemma ballCutoff_support [MeasurableSpace X] [BorelSpace X]
    (o : X) (R : ℝ) : Function.support (ballCutoff o R) ⊆ ball o (R+1) := by
  intro x hx
  by_contra hn
  have hh : R+1-dist x o ≤ 0 := by change ¬dist x o < R+1 at hn; linarith
  exact hx (by simp [ballCutoff,max_eq_left hh])
lemma pushCurrent_eq_of_ball_support [MeasurableSpace X] [BorelSpace X]
    {n : ℕ} {T : Functional X n} (hT : IsMetricCurrent T)
    {K : Set X} (hK : ∀ b π, Admissible b π → (∀ x ∈ K, b x = 0) → T b π = 0)
    (o : X) (R : ℝ) (hKR : K ⊆ closedBall o R) {P : X → X}
    (hP : LipschitzWith 1 P) (hfix : ∀ x, dist x o ≤ R+2 → P x = x) : pushCurrent P T = T := by
  funext b π
  by_cases hab : Admissible b π
  · rw [pushCurrent_apply P T hab]
    let c := fun x => ballCutoff o R x*b x
    have hc : BoundedLip c := (ballCutoff_boundedLip o R).mul hab.1
    have hπP : ∀ i, ∃ L, LipschitzWith L (π i ∘ P) := (admissible_comp hab hP).2
    calc
      T (b ∘ P) (fun i => π i ∘ P) = T c (fun i => π i ∘ P) := by
        apply hT.first_congr_support hK (boundedLip_comp hab.1 hP) hc hπP
        intro x hx
        have hxR := hKR hx
        have hfixx := hfix x (by have := hxR; change dist x o ≤ R at this; linarith)
        simp only [Function.comp_apply,hfixx,c,ballCutoff_one o R hxR,one_mul]
      _ = T c π := by
        apply hT.coord_congr_on hc hπP hab.2 (U := ball o (R+1)) isOpen_ball ?_ ?_
        · intro x hx
          apply ballCutoff_support o R
          intro hz
          exact hx (by simp only [c,hz,zero_mul])
        · intro i x hx
          rw [Function.comp_apply,hfix x (by change dist x o < R+1 at hx; linarith)]
      _ = T b π := by
        apply hT.first_congr_support hK hc hab.1 hab.2
        intro x hx
        simp only [c,ballCutoff_one o R (hKR hx),one_mul]
  · simp only [pushCurrent,ite_eq_right hab,hT.offDomain b π hab]
end CAT0Fillings
end

end OAI
end

section
-- module Solutions.OAIQ29_C0.CAT0Fillings_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
open Foundations CurrentOperations

universe u
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
lemma proper_filling_bound [Nonempty X] (hX : IsCAT0 X) {k : ℕ}
    {T : Functional X (k+2)} (hT : IsIntegral (k+2) T) (hTc : CompactlySupported T)
    (hz : boundarySucc T = 0) :
    ∃ S : Functional X (k+3), IsIntegral (k+3) S ∧ CompactlySupported S ∧
      boundarySucc S = T ∧ mass S ≤ fillingCoefficient (k+2)*(mass T)^(fillingPower (k+2)) := by
  classical
  obtain ⟨K,hK,hTK⟩ := hTc
  let o : X := Classical.choice inferInstance
  obtain ⟨R,hR,hKR⟩ := hK.isBounded.subset_closedBall_lt 0 o
  obtain ⟨P,hP,hPr,hPf⟩ := hX.exists_ball_retraction o (R := R+2) (by linarith)
  let B := closedBall o (R+2)
  have : Nonempty B := ⟨o,by simp [B]; linarith⟩
  let p : X → B := fun x => ⟨P x,by simpa only [B,mem_closedBall,dist_comm] using hPr x⟩
  have hp : LipschitzWith 1 p := hP
  have hinc : LipschitzWith 1 (Subtype.val : B → X) := LipschitzWith.subtype_val B
  have hiA : AntilipschitzWith 1 (Subtype.val : B → X) := by
    intro x y
    change edist (x : X) (y : X) ≤ (1:ℝ≥0∞)*edist (x : X) (y : X)
    rw [one_mul]
  let U := pushCurrent p T
  have hU : IsIntegral (k+2) U := integral_push_proper hT hp
  have hUz : boundarySucc U = 0 := pushCurrent_cycle hz hp
  have hUm : mass U ≤ mass T := mass_push_one_general hT.1 hp
  have hB : IsCAT0 B := hX.closedBall o (by linarith)
  obtain ⟨V,hV,hVb,hVm⟩ := hB.exists_minimal_integral_filling hU hUz
  let S := pushCurrent (Subtype.val : B → X) V
  have hS : IsIntegral (k+3) S := integral_push_of_bilipschitz hV hinc hiA
  have hb : boundarySucc S = T := by
    rw [pushCurrent_boundarySucc V hinc,hVb,←pushCurrent_comp hinc]
    exact pushCurrent_eq_of_ball_support hT.1 hTK o R hKR hP
      (fun x hx => hPf x (by rwa [dist_comm]))
  refine ⟨S,hS,?_,hb,?_⟩
  · refine ⟨B,isCompact_closedBall o (R+2),?_⟩
    intro b π hab hbK
    change pushCurrent (Subtype.val : B → X) V b π = 0
    rw [pushCurrent_apply _ _ hab]
    have heq : b ∘ (Subtype.val : B → X) = fun _ => 0 := funext fun x => hbK x x.property
    rw [heq]
    have hπ := (admissible_comp hab hinc).2
    simpa using hV.1.linearFirst (fun _ => 0) (fun _ => 0) (fun i => π i ∘ Subtype.val)
      0 0 (BoundedLip.const 0) (BoundedLip.const 0) hπ
  · calc
      mass S ≤ mass V := mass_push_one_general hV.1 hinc
      _ = fillingVolume U := hVm
      _ ≤ fillingCoefficient (k+2)*(mass U)^(fillingPower (k+2)) := compact_filling_bound k B hB U hU hUz
      _ ≤ fillingCoefficient (k+2)*(mass T)^(fillingPower (k+2)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (mass_nonneg U) hUm
          (le_of_lt (lt_trans zero_lt_one (fillingPower_gt_one (by omega)))))
          (fillingCoefficient_pos (by omega)).le

theorem sharp_integral_filling_oai
    (X : Type u) [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
    (hX : IsCAT0 X) (n : ℕ) (hn : 2 ≤ n) (T : IntegralCurrent X n)
    (hTc : CompactlySupported T.val) (hTz : IsCycle T.val) :
    ∃ S : IntegralCurrent X (n + 1), CompactlySupported S.val ∧
      boundarySucc S.val = T.val ∧
      mass S.val ≤ fillingCoefficient n * (mass T.val) ^ fillingPower n := by
  classical
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hn
  have hnEq : n = k+2 := by omega
  clear hk
  subst n
  rcases isEmpty_or_nonempty X with hE | hN
  · have hT0 : T.val = 0 := by
      funext b π
      by_cases hab : Admissible b π
      · have heq : b = fun _ => 0 := funext fun x => isEmptyElim x
        rw [heq]
        simpa using T.property.1.linearFirst (fun _ => 0) (fun _ => 0) π 0 0
          (BoundedLip.const 0) (BoundedLip.const 0) hab.2
      · exact T.property.1.offDomain b π hab
    refine ⟨⟨0,isIntegral_zero _⟩,compactlySupported_zero _,?_,?_⟩
    · rw [hT0]; exact boundarySucc_zero _
    · rw [show mass (0 : Functional X (k+2+1)) = 0 from mass_zero _]
      exact mul_nonneg (fillingCoefficient_pos (by omega)).le (Real.rpow_nonneg (mass_nonneg _) _)
  · obtain ⟨S,hS,hSc,hSb,hSm⟩ := proper_filling_bound hX T.property hTc hTz
    exact ⟨⟨S,hS⟩,hSc,hSb,hSm⟩
end CAT0Fillings
end

end OAI
end

theorem solution.{u} : type_of% @OAI.CAT0Fillings.sharp_integral_filling_oai.{u} := @OAI.CAT0Fillings.sharp_integral_filling_oai.{u}
