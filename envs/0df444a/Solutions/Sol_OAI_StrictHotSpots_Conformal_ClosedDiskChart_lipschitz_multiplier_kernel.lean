-- Prove2me | solution 1 for OAI.StrictHotSpots.Conformal.ClosedDiskChart.lipschitz_multiplier_kernel
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T05:34:04.780577+00:00
-- url     : https://prove2.me/submissions/32cce06d-8f57-46ae-82a6-f7c0f84e10d4

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho004
import Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_multipliedGradient_coordinate_difference
import Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_multipliedGradient_identity
import Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_multipliedGradient_tendsto

section
-- module Solutions.OAIQ3_Hot.HotSpots_GreenOperator
attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section WeightedLayer
open Set MeasureTheory
open scoped ContDiff InnerProductSpace ENNReal NNReal
open Set Filter MeasureTheory InnerProductSpace NormedSpace
open scoped Topology ContDiff
open scoped Laplacian
open Set MeasureTheory Filter InnerProductSpace Bornology
open scoped Topology Laplacian ContDiff RealInnerProductSpace
open scoped Convolution
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology ContDiff Convolution Laplacian
open InnerProductSpace
open scoped Laplacian ContDiff

open Filter Set
open scoped Topology




open MeasureTheory Filter
open scoped Topology ENNReal





open MeasureTheory Filter Metric Set
open scoped Topology ENNReal


open MeasureTheory Filter Metric Set
open scoped Topology ENNReal


open MeasureTheory Filter Metric Set
open scoped Topology ENNReal



open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.MeasurableL2Kernel

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  (K : X × Y → ℝ) (hK : AEStronglyMeasurable K (μ.prod ν))
  (hrow : ∀ᵐ x ∂μ, MemLp (fun y => K (x,y)) 2 ν)
  {B : ℝ} (hB : 0 ≤ B)
  (hbound : ∀ᵐ x ∂μ, (eLpNorm (fun y => K (x,y)) 2 ν).toReal ≤ B)

lemma operator_apply_ae (f : Lp ℝ 2 ν) :
    operator K hK hrow hB hbound f =ᵐ[μ] fun x => ∫ y, K (x,y) * f y ∂ν :=
  (apply_memLp K hK hrow hbound f).coeFn_toLp

end StrictHotSpots.MeasurableL2Kernel



open MeasureTheory Filter InnerProductSpace
open scoped ENNReal Topology







open scoped InnerProductSpace


open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

lemma integralOperator_ae (f : Lp ℝ 2 (volume.restrict disk)) :
    integralOperator f =ᵐ[volume.restrict disk] fun x => ∫ y in disk, kernel x y * f y :=
  MeasurableL2Kernel.operator_apply_ae _ _ _ _ _ f

end StrictHotSpots.PlaneGreen


open MeasureTheory
open scoped InnerProductSpace ENNReal


open MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ (∞ : ℝ≥0∞))
  (hν : ν ≤ C • volume.restrict disk)

lemma inclusion_ae (f : Lp ℝ 2 (volume.restrict disk)) : inclusion hC hν f =ᵐ[ν] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul hC hν f

lemma inclusion_row (x : Plane) (hx : x ∈ disk) :
    inclusion hC hν ((kernel_memLp x hx).toLp (kernel x)) =
      (kernel_memLp_weighted hC hν x hx).toLp (kernel x) := by
  apply Lp.ext
  exact (inclusion_ae hC hν _).trans
    (((Measure.absolutelyContinuous_of_le_smul hν).ae_eq (kernel_memLp x hx).coeFn_toLp).trans
      (kernel_memLp_weighted hC hν x hx).coeFn_toLp.symm)

lemma integral_adjoint_row (f : Lp ℝ 2 ν) (x : Plane) (hx : x ∈ disk) :
    (∫ y in disk, kernel x y * (inclusion hC hν).adjoint f y) =
      ∫ y, kernel x y * f y ∂ν := by
  rw [MeasurableL2Kernel.integral_mul_eq_inner (kernel_memLp x hx)
    (Lp.memLp ((inclusion hC hν).adjoint f)), Lp.toLp_coeFn,
    ContinuousLinearMap.adjoint_inner_right, inclusion_row hC hν x hx]
  rw [MeasurableL2Kernel.integral_mul_eq_inner (kernel_memLp_weighted hC hν x hx)
    (Lp.memLp f), Lp.toLp_coeFn]



lemma weightedIntegralOperator_ae (f : Lp ℝ 2 ν) :
    weightedIntegralOperator hC hν f =ᵐ[ν] fun x => ∫ y, kernel x y * f y ∂ν := by
  have ha := (Measure.absolutelyContinuous_of_le_smul hν)
  filter_upwards [inclusion_ae hC hν (integralOperator ((inclusion hC hν).adjoint f)),
    ha.ae_eq (integralOperator_ae ((inclusion hC hν).adjoint f)),
    (ae_restrict_mem diskOpen.measurableSet).filter_mono ha.ae_le] with x hx hi hxd
  change inclusion hC hν (integralOperator ((inclusion hC hν).adjoint f)) x = _
  rw [hx,hi,integral_adjoint_row hC hν f x hxd]

end StrictHotSpots.PlaneGreen

end WeightedLayer


end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_KernelLimit
attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section L2CutoffLayer

open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.L2Cutoff
variable {X : Type*} [MeasurableSpace X] {ν : Measure X} (s : Set X) (hs : MeasurableSet s)

lemma extension_ae (f : Lp ℝ 2 (ν.restrict s)) :
    extension s hs f =ᵐ[ν] s.indicator f := (extension_memLp s hs f).coeFn_toLp

lemma extension_norm (f : Lp ℝ 2 (ν.restrict s)) : ‖extension s hs f‖ = ‖f‖ := by
  change ‖(extension_memLp s hs f).toLp _‖ = _
  rw [Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict hs]
  rfl

lemma restriction_ae (f : Lp ℝ 2 ν) : restriction s f =ᵐ[ν.restrict s] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ f

lemma restriction_norm (f : Lp ℝ 2 ν) : ‖restriction s f‖ ≤ ‖f‖ := by
  change (eLpNorm (restriction s f) 2 (ν.restrict s)).toReal ≤ (eLpNorm f 2 ν).toReal
  rw [eLpNorm_congr_ae (restriction_ae s f)]
  exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top (eLpNorm_restrict_le _ _ _ _)

lemma projection_ae (f : Lp ℝ 2 ν) : projection s hs f =ᵐ[ν] s.indicator f := by
  filter_upwards [extension_ae s hs (restriction s f),
    ae_imp_of_ae_restrict (restriction_ae s f)] with x hx hr
  change extension s hs (restriction s f) x = _
  rw [hx]
  by_cases hxs : x ∈ s
  · simp [hxs, hr hxs]
  · simp [hxs]

lemma projection_norm (f : Lp ℝ 2 ν) : ‖projection s hs f‖ ≤ ‖f‖ := by
  exact (extension_norm s hs _).le.trans (restriction_norm s f)

lemma projection_norm_le : ‖projection (ν := ν) s hs‖ ≤ 1 := by
  apply (projection (ν := ν) s hs).opNorm_le_bound (by norm_num)
  intro f
  simpa only [one_mul] using projection_norm s hs f

end StrictHotSpots.L2Cutoff

end L2CutoffLayer

section CutoffConvergenceLayer
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.L2Cutoff
variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

lemma projection_tendsto (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
    (hex : ∀ᵐ x ∂ν, ∀ᶠ n in atTop, x ∈ s n) (f : Lp ℝ 2 ν) :
    Tendsto (fun n => projection (s n) (hs n) f) atTop (𝓝 f) := by
  let hf : ∀ n, MemLp ((s n).indicator f) 2 ν :=
    fun n => (Lp.memLp f).indicator (hs n)
  have ht := L2Limits.tendsto_toLp_of_dominated hf (Lp.memLp f) (Lp.memLp f).norm
    (Eventually.of_forall fun n => Eventually.of_forall fun x => by
      by_cases hx : x ∈ s n <;> simp [hx])
    (by
      filter_upwards [hex] with x hx
      apply tendsto_const_nhds.congr'
      filter_upwards [hx] with n hn
      simp [hn])
  have he (n : ℕ) : projection (s n) (hs n) f = (hf n).toLp _ :=
    Lp.ext ((projection_ae (s n) (hs n) f).trans (hf n).coeFn_toLp.symm)
  simpa only [← he, Lp.toLp_coeFn] using ht

end StrictHotSpots.L2Cutoff
namespace StrictHotSpots.BanachResolvent
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma bounded_strong_tendsto_moving (Q : ℕ → E →L[ℝ] E) (A : E →L[ℝ] E)
    {d : ℝ} (hQ : ∀ᶠ n in atTop, ‖Q n‖ ≤ d)
    (hs : ∀ v, Tendsto (fun n => Q n v) atTop (𝓝 (A v)))
    {v : ℕ → E} {w : E} (hv : Tendsto v atTop (𝓝 w)) :
    Tendsto (fun n => Q n (v n)) atTop (𝓝 (A w)) := by
  have hz : Tendsto (fun n => Q n (v n-w)) atTop (𝓝 0) := by
    have hb : Tendsto (fun n => d * ‖v n-w‖) atTop (𝓝 0) := by
      simpa using (hv.sub_const w).norm.const_mul d
    apply squeeze_zero_norm' _ hb
    filter_upwards [hQ] with n hn
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right hn (norm_nonneg _))
  simpa only [map_sub, sub_add_cancel, zero_add] using hz.add (hs w)

end StrictHotSpots.BanachResolvent
end
end CutoffConvergenceLayer

section DiskCutoffLayer
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

lemma cutoffRadius_tendsto : Tendsto cutoffRadius atTop (𝓝 1) := by
  change Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 1)) atTop (𝓝 1)
  simpa only [sub_zero] using
    ((tendsto_const_nhds (x := (1:ℝ))).sub (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))

lemma eventually_mem_cutoffSet (x : Plane) (hx : x ∈ disk) :
    ∀ᶠ n in atTop, x ∈ cutoffSet n := by
  have ht := cutoffRadius_tendsto.eventually (eventually_gt_nhds (show ‖x‖ < 1 by simpa [disk] using hx))
  filter_upwards [ht] with n hn
  simpa [cutoffSet] using hn.le

variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ ∞)
  (hν : ν ≤ C • volume.restrict disk)

include hν in
lemma ae_eventually_mem_cutoffSet : ∀ᵐ x ∂ν, ∀ᶠ n in atTop, x ∈ cutoffSet n := by
  filter_upwards [ae_mem_disk hν] with x hx
  exact eventually_mem_cutoffSet x hx

include hν in
lemma cutoffProjection_tendsto (f : Lp ℝ 2 ν) :
    Tendsto (fun n => L2Cutoff.projection (cutoffSet n) (cutoffSet_measurable n) f)
      atTop (𝓝 f) :=
  L2Cutoff.projection_tendsto cutoffSet cutoffSet_measurable (ae_eventually_mem_cutoffSet hν) f

include hν in
lemma cutoff_integral_tendsto {f : Plane → ℝ} (hf : Integrable f ν) :
    Tendsto (fun n => ∫ x in cutoffSet n, f x ∂ν) atTop (𝓝 (∫ x, f x ∂ν)) := by
  have hm : ∀ n, AEStronglyMeasurable ((cutoffSet n).indicator f) ν :=
    fun n => hf.aestronglyMeasurable.indicator (cutoffSet_measurable n)
  have ht := tendsto_integral_filter_of_dominated_convergence (f := f) (fun x => ‖f x‖)
    (Eventually.of_forall hm)
    (Eventually.of_forall fun n => Eventually.of_forall fun x => by
      by_cases hx : x ∈ cutoffSet n <;> simp [hx]) hf.norm
    (by
      filter_upwards [ae_eventually_mem_cutoffSet hν] with x hx
      apply tendsto_const_nhds.congr'
      filter_upwards [hx] with n hn
      simp [hn])
  simpa only [integral_indicator (cutoffSet_measurable _)] using ht

include hC hν in
lemma smoothedPoisson_cutoff_tendsto (s : Boundary) {x : Plane} (hx : x ∈ disk) :
    Tendsto (fun n => smoothedPoisson (ν := ν.restrict (cutoffSet n)) s x)
      atTop (𝓝 (smoothedPoisson (ν := ν) s x)) :=
  cutoff_integral_tendsto hν (product_green_poisson_integrable hC hν x hx s)

lemma smoothedPoisson_cutoff_L2_tendsto [IsFiniteMeasure ν] (s : Boundary) :
    Tendsto (fun n => (smoothedPoisson_full_memLp hC hν s (cutoffSet n)).toLp
      (smoothedPoisson (ν := ν.restrict (cutoffSet n)) s)) atTop
      (𝓝 ((smoothedPoisson_memLp hC hν s).toLp (smoothedPoisson (ν := ν) s))) := by
  apply L2Limits.tendsto_toLp_of_dominated
    (fun n => smoothedPoisson_full_memLp hC hν s (cutoffSet n))
    (smoothedPoisson_memLp hC hν s) (smoothedPoisson_memLp hC hν s)
  · apply Eventually.of_forall
    intro n
    filter_upwards [ae_mem_disk hν] with x hx
    rw [Real.norm_of_nonneg (smoothedPoisson_nonneg (restrictDensity hν (cutoffSet n)) s hx)]
    exact smoothedPoisson_restrict_le hC hν s (cutoffSet n) hx
  · filter_upwards [ae_mem_disk hν] with x hx
    exact smoothedPoisson_cutoff_tendsto hC hν s hx

end StrictHotSpots.PlaneGreen
end
end DiskCutoffLayer

section FullBoundaryKernelLayer
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

lemma compactSmoothedRow_eq (n : ℕ) (s : Boundary) :
    weightedIntegralOperator hC (restrictDensity hν (cutoffSet n))
      (poissonRow (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s) =
    L2Cutoff.restriction (cutoffSet n) (cutoffSmoothedRow hC hν n s) := by
  apply Lp.ext
  filter_upwards [weightedIntegralOperator_ae hC (restrictDensity hν (cutoffSet n))
      (poissonRow (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s),
    L2Cutoff.restriction_ae (cutoffSet n) (cutoffSmoothedRow hC hν n s),
    ((smoothedPoisson_full_memLp hC hν s (cutoffSet n)).coeFn_toLp).restrict] with x hx hr hs
  rw [hx,hr,show cutoffSmoothedRow hC hν n s x =
    smoothedPoisson (ν := ν.restrict (cutoffSet n)) s x from hs]
  apply integral_congr_ae
  filter_upwards [(poisson_memLp (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s).coeFn_toLp]
    with y hy
  rw [show poissonRow (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s y = poisson s y from hy]

lemma extendedSmoothedRow_tendsto (s : Boundary) :
    Tendsto (fun n => L2Cutoff.projection (cutoffSet n) (cutoffSet_measurable n)
      (cutoffSmoothedRow hC hν n s)) atTop (𝓝 (smoothedRow hC hν s)) := by
  apply BanachResolvent.bounded_strong_tendsto_moving
    (fun n => L2Cutoff.projection (cutoffSet n) (cutoffSet_measurable n))
    (ContinuousLinearMap.id ℝ (Lp ℝ 2 ν))
    (Eventually.of_forall fun n => L2Cutoff.projection_norm_le _ _)
    (cutoffProjection_tendsto hν)
  exact smoothedPoisson_cutoff_L2_tendsto hC hν s



end StrictHotSpots.PlaneGreen
end
end FullBoundaryKernelLayer

section PoissonProductsLayer
noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

lemma poisson_measurable (s : Boundary) : Measurable (poisson s) := by
  unfold poisson DiskFormula.poisson
  fun_prop

end StrictHotSpots.PlaneGreen
end
end PoissonProductsLayer



end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section FullBoundaryEmbeddingLayer
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

lemma boundaryInteraction_eq_dist (s t : Boundary) :
    boundaryInteraction s t = 1 / (Real.pi * dist s t ^ 2) := by
  simp only [boundaryInteraction, DiskFormula.boundaryInteraction, ← map_sub,
    LinearIsometryEquiv.norm_map, Subtype.dist_eq, dist_eq_norm]

end StrictHotSpots.PlaneGreen
end
end FullBoundaryEmbeddingLayer
end FullBoundaryCombinedLayer


end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_BoundaryEnergy
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LipschitzBoundaryScalarSupport

noncomputable section

section BoundaryMeasurabilityScalarSupportLayer

section BoundaryMeasurabilityLayer
noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

variable {ν : Measure Plane} [IsFiniteMeasure ν] {R : ℝ}
  (hR : ∀ᵐ x ∂ν, ‖x‖ ≤ R) (hR1 : R < 1)

lemma poissonRow_continuous : Continuous (poissonRow hR hR1) := by
  rw [continuous_iff_continuousAt]
  intro s
  apply L2Limits.tendsto_toLp_of_dominated
    (hb := memLp_const (1 / (2 * Real.pi * (1-R)^2)))
  · apply Eventually.of_forall
    intro t
    filter_upwards [hR] with x hx
    change ‖DiskFormula.poisson (complexIso.symm (t : Plane)) (complexIso.symm x)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg
      (DiskFormula.poisson_nonneg _ _ (by simpa using hx.trans_lt hR1))]
    exact DiskFormula.poisson_bounded _ _ (by simpa using t.property) (by simpa using hx) hR1
  · filter_upwards [hR] with x hx
    exact (poisson_continuous_boundary ⟨x, by simpa [disk] using hx.trans_lt hR1⟩).continuousAt

variable {C : ℝ≥0∞} (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

lemma smoothedRow_stronglyMeasurable : StronglyMeasurable (smoothedRow hC hν) := by
  apply stronglyMeasurable_of_tendsto atTop
    (f := fun n s => L2Cutoff.projection (cutoffSet n) (cutoffSet_measurable n)
      (cutoffSmoothedRow hC hν n s))
  · intro n
    have he : (fun s => L2Cutoff.projection (cutoffSet n) (cutoffSet_measurable n)
        (cutoffSmoothedRow hC hν n s)) =
        fun s => L2Cutoff.extension (cutoffSet n) (cutoffSet_measurable n)
          (weightedIntegralOperator hC (restrictDensity hν (cutoffSet n))
            (poissonRow (cutoff_ae_norm (ν := ν) n) (cutoffRadius_lt_one n) s)) := by
      funext s
      rw [compactSmoothedRow_eq]
      rfl
    rw [he]
    apply Continuous.stronglyMeasurable
    exact (L2Cutoff.extension (cutoffSet n) (cutoffSet_measurable n)).continuous.comp
      ((weightedIntegralOperator hC (restrictDensity hν (cutoffSet n))).continuous.comp
        (poissonRow_continuous (cutoff_ae_norm n) (cutoffRadius_lt_one n)))
  · exact tendsto_pi_nhds.mpr (extendedSmoothedRow_tendsto hC hν)

lemma smoothedPoisson_joint_measurable :
    Measurable (fun z : Boundary × Plane => smoothedPoisson (ν := ν) z.1 z.2) := by
  have h1 : Measurable (fun z : (Boundary × Plane) × Plane => (z.1.2,z.2)) :=
    measurable_fst.snd.prodMk measurable_snd
  have h2 : Measurable (fun z : (Boundary × Plane) × Plane => (z.1.1,z.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have hk := measurable_kernel.comp h1
  have hp := poisson_joint_measurable.comp h2
  dsimp only [Function.comp_def] at hk hp
  have hm := hk.mul hp
  change Measurable (fun z : Boundary × Plane =>
    ∫ y, kernel z.2 y * poisson z.1 y ∂ν)
  have hh : StronglyMeasurable (fun z : Boundary × Plane =>
      ∫ y, kernel z.2 y * poisson z.1 y ∂ν) :=
    hm.stronglyMeasurable.integral_prod_right' (ν := ν)
  exact hh.measurable

lemma boundaryInteraction_measurable :
    Measurable (fun z : Boundary × Boundary => boundaryInteraction z.1 z.2) := by
  unfold boundaryInteraction DiskFormula.boundaryInteraction
  fun_prop

end StrictHotSpots.PlaneGreen
end
end BoundaryMeasurabilityLayer
end BoundaryMeasurabilityScalarSupportLayer

section BoundaryPoissonIntegralsScalarSupportLayer

section BoundaryPoissonIntegralsLayer
noncomputable section
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

include hC hν in
lemma poisson_integrable_weighted (s : Boundary) : Integrable (poisson s) ν :=
  (poisson_memLp_three_halves_weighted hC hν s).integrable (by
    apply (ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)).2
    norm_num)

include hC hν in
lemma poisson_product_boundary_integrable (s : Boundary) :
    Integrable (fun z : Boundary × Plane => poisson s z.2 * poisson z.1 z.2)
      (boundaryMeasure.prod ν) := by
  have hs : Measurable (fun z : Boundary × Plane => poisson s z.2) :=
    (poisson_measurable s).comp measurable_snd
  have hm := hs.mul poisson_joint_measurable
  apply (integrable_prod_iff' hm.aestronglyMeasurable).2
  constructor
  · filter_upwards [ae_mem_disk hν] with x hx
    exact (poisson_boundary_integrable ⟨x,hx⟩).const_mul (poisson s x)
  · apply (poisson_integrable_weighted hC hν s).congr
    filter_upwards [ae_mem_disk hν] with x hx
    change poisson s x = ∫ t, ‖poisson s x * poisson t x‖ ∂boundaryMeasure
    rw [integral_congr_ae (Eventually.of_forall (fun t : Boundary =>
      Real.norm_of_nonneg (mul_nonneg (poisson_nonneg s ⟨x,hx⟩) (poisson_nonneg t ⟨x,hx⟩))))]
    rw [integral_const_mul, integral_poisson ⟨x,hx⟩, mul_one]

include hC hν in
lemma firstInteraction_integrable (s : Boundary) :
    Integrable (fun t : Boundary => ∫ x, poisson s x * poisson t x ∂ν) boundaryMeasure :=
  (poisson_product_boundary_integrable hC hν s).integral_prod_left

include hC hν in
lemma integral_firstInteraction (s : Boundary) :
    (∫ t, ∫ x, poisson s x * poisson t x ∂ν ∂boundaryMeasure) = ∫ x, poisson s x ∂ν := by
  rw [integral_integral_swap (poisson_product_boundary_integrable hC hν s)]
  apply integral_congr_ae
  filter_upwards [ae_mem_disk hν] with x hx
  rw [integral_const_mul, integral_poisson ⟨x,hx⟩, mul_one]


end StrictHotSpots.PlaneGreen
end
end BoundaryPoissonIntegralsLayer
end BoundaryPoissonIntegralsScalarSupportLayer

section BoundaryExtensionScalarSupportLayer

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

lemma smoothedRow_uniform_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ s, ‖smoothedRow hC hν s‖ ≤ M := by
  obtain ⟨B,hB,h⟩ := green_poisson_uniform_bound hC hν
  refine ⟨(measureUnivNNReal ν : ℝ) ^ (2 : ℝ)⁻¹ * B, by positivity, fun s => ?_⟩
  apply Lp.norm_le_of_ae_bound hB
  filter_upwards [(smoothedPoisson_memLp hC hν s).coeFn_toLp, ae_mem_disk hν] with x hx hxd
  rw [show smoothedRow hC hν s x = smoothedPoisson (ν := ν) s x from hx]
  exact h x hxd s

end StrictHotSpots.PlaneGreen
end BoundaryExtensionScalarSupportLayer

section PoissonFubiniScalarSupportLayer
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hν : ν ≤ C • volume.restrict disk)

include hν in
lemma poisson_pair_integrable {g : Plane → ℝ} (hg : Integrable g ν) :
    Integrable (fun z : Boundary × Plane => poisson z.1 z.2 * g z.2) (boundaryMeasure.prod ν) := by
  have hm : AEStronglyMeasurable (fun z : Boundary × Plane => poisson z.1 z.2 * g z.2) (boundaryMeasure.prod ν) :=
    poisson_joint_measurable.aestronglyMeasurable.mul hg.aestronglyMeasurable.comp_snd
  apply (integrable_prod_iff' hm).2
  constructor
  · filter_upwards [ae_mem_disk hν] with x hx
    exact (poisson_boundary_integrable ⟨x,hx⟩).mul_const (g x)
  · apply hg.norm.congr
    filter_upwards [ae_mem_disk hν] with x hx
    change ‖g x‖ = ∫ s, ‖poisson s x * g x‖ ∂boundaryMeasure
    simp_rw [norm_mul,Real.norm_of_nonneg (poisson_nonneg _ ⟨x,hx⟩)]
    rw [integral_mul_const,integral_poisson ⟨x,hx⟩,one_mul]

end StrictHotSpots.PlaneGreen
end PoissonFubiniScalarSupportLayer

section BoundaryInteractionPartsScalarSupportLayer
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

lemma firstInteraction_measurable : Measurable (fun z : Boundary × Boundary => firstInteraction (ν := ν) z.1 z.2) := by
  have hm1 : Measurable (fun z : (Boundary × Boundary) × Plane => (z.1.1,z.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have hm2 : Measurable (fun z : (Boundary × Boundary) × Plane => (z.1.2,z.2)) :=
    measurable_fst.snd.prodMk measurable_snd
  exact ((poisson_joint_measurable.comp hm1).mul
    (poisson_joint_measurable.comp hm2)).stronglyMeasurable.integral_prod_right'.measurable

lemma secondInteraction_measurable : Measurable (fun z : Boundary × Boundary => secondInteraction (ν := ν) z.1 z.2) := by
  have hm1 : Measurable (fun z : (Boundary × Boundary) × Plane => (z.1.1,z.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have hm2 : Measurable (fun z : (Boundary × Boundary) × Plane => (z.1.2,z.2)) :=
    measurable_fst.snd.prodMk measurable_snd
  exact ((poisson_joint_measurable.comp hm1).mul
    (smoothedPoisson_joint_measurable.comp hm2)).stronglyMeasurable.integral_prod_right'.measurable

lemma tailInteraction_measurable : Measurable (fun z : Boundary × Boundary => tailInteraction hC hν z.1 z.2) := by
  have h1 := (smoothedRow_stronglyMeasurable hC hν).comp_measurable
    (measurable_fst : Measurable (Prod.fst : Boundary × Boundary → Boundary))
  have h2 := (smoothedRow_stronglyMeasurable hC hν).comp_measurable
    (measurable_snd : Measurable (Prod.snd : Boundary × Boundary → Boundary))
  exact (h1.inner ((BanachResolvent.resolvent (weightedIntegralOperator hC hν)).continuous.comp_stronglyMeasurable h2)).measurable

include hν in
omit [IsFiniteMeasure ν] in
lemma firstInteraction_nonneg (s t : Boundary) : 0 ≤ firstInteraction (ν := ν) s t := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_mem_disk hν] with x hx
  exact mul_nonneg (poisson_nonneg s ⟨x,hx⟩) (poisson_nonneg t ⟨x,hx⟩)

include hν in
lemma massPoisson_integrable : Integrable (fun s : Boundary => ∫ x, poisson s x ∂ν) boundaryMeasure := by
  have h := (poisson_pair_integrable hν (integrable_const (1 : ℝ))).integral_prod_left
  simpa only [mul_one] using h

include hC hν in
lemma firstInteraction_prod_integrable :
    Integrable (fun z : Boundary × Boundary => firstInteraction (ν := ν) z.1 z.2) (boundaryMeasure.prod boundaryMeasure) := by
  apply (integrable_prod_iff firstInteraction_measurable.aestronglyMeasurable).2
  constructor
  · exact Eventually.of_forall (firstInteraction_integrable hC hν)
  · apply (massPoisson_integrable hν).congr
    filter_upwards [] with s
    change (∫ x, poisson s x ∂ν) = ∫ t, ‖firstInteraction (ν := ν) s t‖ ∂boundaryMeasure
    simp_rw [Real.norm_of_nonneg (firstInteraction_nonneg hν s _)]
    exact (integral_firstInteraction hC hν s).symm

include hC hν in
lemma secondInteraction_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ s t : Boundary,
    ‖secondInteraction (ν := ν) s t‖ ≤ M * (∫ x, poisson s x ∂ν) := by
  obtain ⟨M,hM,h⟩ := green_poisson_uniform_bound hC hν
  refine ⟨M,hM,fun s t => ?_⟩
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ x, M * poisson s x ∂ν := by
      apply integral_mono_of_nonneg
      · exact Eventually.of_forall fun _ => norm_nonneg _
      · exact (poisson_integrable_weighted hC hν s).const_mul M
      · filter_upwards [ae_mem_disk hν] with x hx
        rw [norm_mul,Real.norm_of_nonneg (poisson_nonneg s ⟨x,hx⟩),mul_comm M]
        exact mul_le_mul_of_nonneg_left (h x hx t) (poisson_nonneg s ⟨x,hx⟩)
    _ = _ := integral_const_mul _ _

include hC hν in
lemma secondInteraction_prod_integrable :
    Integrable (fun z : Boundary × Boundary => secondInteraction (ν := ν) z.1 z.2) (boundaryMeasure.prod boundaryMeasure) := by
  obtain ⟨M,_,hM⟩ := secondInteraction_bound hC hν
  apply ((massPoisson_integrable hν).comp_fst boundaryMeasure |>.const_mul M).mono'
    secondInteraction_measurable.aestronglyMeasurable
  exact Eventually.of_forall fun z => hM z.1 z.2

lemma tailInteraction_prod_integrable :
    Integrable (fun z : Boundary × Boundary => tailInteraction hC hν z.1 z.2) (boundaryMeasure.prod boundaryMeasure) := by
  obtain ⟨M,hM,h⟩ := smoothedRow_uniform_bound hC hν
  apply Integrable.of_bound (tailInteraction_measurable hC hν).aestronglyMeasurable
    (M * (‖BanachResolvent.resolvent (weightedIntegralOperator hC hν)‖ * M))
  filter_upwards [] with z
  change ‖inner ℝ (smoothedRow hC hν z.1) (BanachResolvent.resolvent _ (smoothedRow hC hν z.2))‖ ≤ _
  apply (norm_inner_le_norm _ _).trans
  exact mul_le_mul (h z.1) ((ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_left (h z.2) (norm_nonneg _))) (norm_nonneg _) hM

lemma fullBoundaryR_integrable : Integrable (fun z : Boundary × Boundary => fullBoundaryR hC hν z.1 z.2)
    (boundaryMeasure.prod boundaryMeasure) :=
  ((firstInteraction_prod_integrable hC hν).add (secondInteraction_prod_integrable hC hν)).add
    (tailInteraction_prod_integrable hC hν)

end StrictHotSpots.PlaneGreen
end BoundaryInteractionPartsScalarSupportLayer

section BoundaryFormScalarSupportLayer



open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
lemma boundary_continuous_bound {f : Boundary → E} (hf : Continuous f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s, ‖f s‖ ≤ M := by
  obtain ⟨M,hM⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨max M 0,le_max_right _ _,fun s => (hM s (mem_univ s)).trans (le_max_left _ _)⟩

lemma harmonic_boundary_bound {h k : Boundary → E} {A B : ℝ≥0}
    (hh : LipschitzWith A h) (hk : LipschitzWith B k) (s t : Boundary) :
    ‖boundaryInteraction s t * inner ℝ (h s-h t) (k s-k t)‖ ≤ (A:ℝ)*B/Real.pi := by
  rw [norm_mul,Real.norm_eq_abs,boundaryInteraction_eq_dist,abs_of_nonneg (by positivity)]
  have h1 : ‖h s-h t‖ ≤ (A:ℝ)*dist s t := by simpa only [dist_eq_norm] using hh.dist_le_mul s t
  have h2 : ‖k s-k t‖ ≤ (B:ℝ)*dist s t := by simpa only [dist_eq_norm] using hk.dist_le_mul s t
  by_cases hd : dist s t = 0
  · simp [hd]; positivity
  · calc
      _ ≤ (1/(Real.pi*dist s t^2)) * (((A:ℝ)*dist s t)*((B:ℝ)*dist s t)) := by
        gcongr
        exact (norm_inner_le_norm _ _).trans (mul_le_mul h1 h2 (norm_nonneg _) (by positivity))
      _ = _ := by field_simp

lemma harmonic_boundary_integrable {h k : Boundary → E} {A B : ℝ≥0}
    (hh : LipschitzWith A h) (hk : LipschitzWith B k) :
    Integrable (fun z : Boundary × Boundary => boundaryInteraction z.1 z.2 *
      inner ℝ (h z.1-h z.2) (k z.1-k z.2)) (boundaryMeasure.prod boundaryMeasure) := by
  apply (integrable_const ((A:ℝ)*B/Real.pi)).mono'
  · exact (boundaryInteraction_measurable.aestronglyMeasurable).mul
      (((hh.continuous.comp continuous_fst).sub (hh.continuous.comp continuous_snd)).inner
        ((hk.continuous.comp continuous_fst).sub (hk.continuous.comp continuous_snd))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z => harmonic_boundary_bound hh hk z.1 z.2

lemma interaction_boundary_integrable {R : Boundary → Boundary → ℝ}
    (hR : Integrable (fun z : Boundary × Boundary => R z.1 z.2) (boundaryMeasure.prod boundaryMeasure))
    {h k : Boundary → E} (hh : Continuous h) (hk : Continuous k) :
    Integrable (fun z : Boundary × Boundary => R z.1 z.2 * inner ℝ (h z.1) (k z.2))
      (boundaryMeasure.prod boundaryMeasure) := by
  obtain ⟨A,hA,hAb⟩ := boundary_continuous_bound hh
  obtain ⟨B,hB,hBb⟩ := boundary_continuous_bound hk
  apply (hR.norm.const_mul (A*B)).mono'
  · exact hR.aestronglyMeasurable.mul
      ((hh.comp continuous_fst).inner (hk.comp continuous_snd)).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro z
    simp only [norm_mul]
    calc
      _ ≤ ‖R z.1 z.2‖ * (A*B) := by
        gcongr
        exact (norm_inner_le_norm _ _).trans (mul_le_mul (hAb z.1) (hBb z.2) (norm_nonneg _) hA)
      _ = _ := mul_comm _ _

lemma harmonic_multiplier_algebra (a b : ℝ) (x y : E) :
    inner ℝ (a•x-b•y) (a•x-b•y) - inner ℝ (x-y) (a^2•x-b^2•y) =
      (a-b)^2 * inner ℝ x y := by
  simp only [inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right]
  rw [real_inner_comm y x]
  ring

lemma boundary_smul_lipschitz {b : Boundary → ℝ} {g : Boundary → E} {A B : ℝ≥0}
    (hb : LipschitzWith A b) (hg : LipschitzWith B g) :
    ∃ L : ℝ≥0, LipschitzWith L (fun s => b s • g s) := by
  obtain ⟨M,hM,hMb⟩ := boundary_continuous_bound hb.continuous
  obtain ⟨N,hN,hNg⟩ := boundary_continuous_bound hg.continuous
  refine ⟨A * ⟨N,hN⟩ + ⟨M,hM⟩ * B,LipschitzWith.of_dist_le_mul fun s t => ?_⟩
  rw [dist_eq_norm]
  have he : b s • g s-b t • g t = (b s-b t) • g s + b t • (g s-g t) := by
    simp only [sub_smul,smul_sub]; abel
  rw [he]
  calc
    _ ≤ ‖(b s-b t) • g s‖ + ‖b t • (g s-g t)‖ := norm_add_le _ _
    _ = ‖b s-b t‖*‖g s‖ + ‖b t‖*‖g s-g t‖ := by simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ ((A:ℝ)*dist s t)*N + M*((B:ℝ)*dist s t) := by
      gcongr
      · simpa only [dist_eq_norm] using hb.dist_le_mul s t
      · exact hNg s
      · exact hMb t
      · simpa only [dist_eq_norm] using hg.dist_le_mul s t
    _ = _ := by
      change ((A:ℝ)*dist s t)*N + M*((B:ℝ)*dist s t) =
        ((A:ℝ)*N+M*(B:ℝ))*dist s t
      ring

end StrictHotSpots.PlaneGreen
end BoundaryFormScalarSupportLayer
end
end LipschitzBoundaryScalarSupport


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Potentials
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualVectorSupport

noncomputable section




section PlaneDifferentialInteriorSupportLayer

open Set MeasureTheory InnerProductSpace
open scoped ContDiff Laplacian
namespace StrictHotSpots.Hodge
lemma inner_two (x y : Plane) : inner ℝ x y = c 0 x*c 0 y+c 1 x*c 1 y := by
  simpa only [Fin.sum_univ_two,real_inner_comm (e 0) y,real_inner_comm (e 1) y] using
    (planeBasis.sum_inner_mul_inner x y).symm

end StrictHotSpots.Hodge


end PlaneDifferentialInteriorSupportLayer



end

end ActualVectorSupport

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_VectorEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualBoundaryMultiplier

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma multiplier_integrand_integrable {R : Boundary → Boundary → ℝ}
    (hR : Integrable (fun z : Boundary × Boundary => R z.1 z.2) (boundaryMeasure.prod boundaryMeasure))
    {g : Boundary → E} {b : Boundary → ℝ} {A B : ℝ≥0}
    (hg : LipschitzWith A g) (hb : LipschitzWith B b) :
    Integrable (fun z : Boundary × Boundary => (boundaryInteraction z.1 z.2+R z.1 z.2) *
      (b z.1-b z.2)^2 * inner ℝ (g z.1) (g z.2)) (boundaryMeasure.prod boundaryMeasure) := by
  obtain ⟨L,hL⟩ := boundary_smul_lipschitz hb hg
  obtain ⟨D,hD⟩ := boundary_smul_lipschitz hb hb
  have hD' : LipschitzWith D (fun s => b s^2) := by simpa only [smul_eq_mul,pow_two] using hD
  obtain ⟨F,hF⟩ := boundary_smul_lipschitz hD' hg
  have h0 := (harmonic_boundary_integrable hL hL).sub (harmonic_boundary_integrable hg hF)
  have h1 := interaction_boundary_integrable hR hF.continuous hg.continuous
  have h2 := interaction_boundary_integrable hR hg.continuous hF.continuous
  have h3 := interaction_boundary_integrable hR hL.continuous hL.continuous
  apply (h0.add ((h1.add h2).sub (h3.const_mul 2))).congr
  filter_upwards [] with z
  simp only [Pi.add_apply,Pi.sub_apply]
  rw [← mul_sub,harmonic_multiplier_algebra]
  simp only [real_inner_smul_left,real_inner_smul_right]
  ring


end StrictHotSpots.PlaneGreen
end
end ActualBoundaryMultiplier


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Multiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section PhysicalMultiplierLimit

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal Topology

namespace StrictHotSpots.Hodge
variable {Ω : Set Plane}
lemma vectorForm_tendsto {X : ℕ → Fin 2 → H1 Ω} {Y : Fin 2 → H1 Ω}
    (h : ∀ i, Tendsto (fun n => X n i) atTop (𝓝 (Y i))) (μ : ℝ) :
    Tendsto (fun n => vectorForm μ (X n) (X n)) atTop (𝓝 (vectorForm μ Y Y)) := by
  have hg (i : Fin 2) := H1.grad.continuous.continuousAt.tendsto.comp (h i)
  have hv (i : Fin 2) := H1.value.continuous.continuousAt.tendsto.comp (h i)
  have hp (i j : Fin 2) := (coordinateL Ω i).continuous.continuousAt.tendsto.comp (hg j)
  have ha (i : Fin 2) := (axisL Ω i).continuous.continuousAt.tendsto.comp (hv i)
  have hd := (hp 0 0).add (hp 1 1)
  have hc := (hp 0 1).sub (hp 1 0)
  have hb := (ha 0).add (ha 1)
  exact ((hd.inner hd).add (hc.inner hc)).sub ((hb.inner hb).const_mul μ)
end StrictHotSpots.Hodge
end
end PhysicalMultiplierLimit

section MultiplierKernelConvergence

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma harmonic_square_bound {b : Boundary → ℝ} {B : ℝ≥0}
    (hb : LipschitzWith B b) (s t : Boundary) :
    ‖boundaryInteraction s t*(b s-b t)^2‖ ≤ (B:ℝ)*B/Real.pi := by
  simpa only [Real.inner_apply,pow_two] using harmonic_boundary_bound hb hb s t

lemma multiplier_integrand_bound {R : Boundary → Boundary → ℝ}
    {g : Boundary → E} {b : Boundary → ℝ} {B : ℝ≥0}
    (hb : LipschitzWith B b) {M G : ℝ} (_hM : 0 ≤ M) (hG : 0 ≤ G)
    (hbM : ∀ s, ‖b s‖ ≤ M) (hgG : ∀ s, ‖g s‖ ≤ G) (s t : Boundary) :
    ‖(boundaryInteraction s t+R s t)*(b s-b t)^2*inner ℝ (g s) (g t)‖ ≤
      ((B:ℝ)*B/Real.pi+(M+M)^2*‖R s t‖)*(G*G) := by
  have hd : ‖b s-b t‖ ≤ M+M := (norm_sub_le _ _).trans (add_le_add (hbM s) (hbM t))
  have hi : ‖inner ℝ (g s) (g t)‖ ≤ G*G :=
    (norm_inner_le_norm _ _).trans (mul_le_mul (hgG s) (hgG t) (norm_nonneg _) hG)
  have hr : ‖R s t*(b s-b t)^2‖ ≤ (M+M)^2*‖R s t‖ := by
    rw [norm_mul,norm_pow,mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hd 2) (norm_nonneg _)
  have he : (boundaryInteraction s t+R s t)*(b s-b t)^2 =
      boundaryInteraction s t*(b s-b t)^2+R s t*(b s-b t)^2 := by ring
  rw [he,norm_mul]
  exact mul_le_mul ((norm_add_le _ _).trans (add_le_add (harmonic_square_bound hb s t) hr))
    hi (norm_nonneg _) (by positivity)




theorem multiplier_kernel_tendsto {R : Boundary → Boundary → ℝ}
    (hR : Integrable (fun z : Boundary × Boundary => R z.1 z.2) (boundaryMeasure.prod boundaryMeasure))
    {g : Boundary → E} (hg : Continuous g) {b : Boundary → ℝ} {bn : ℕ → Boundary → ℝ}
    {B : ℝ≥0} (hb : ∀ n, LipschitzWith B (bn n)) {M : ℝ} (hM : 0 ≤ M)
    (hMb : ∀ n s, ‖bn n s‖ ≤ M) (ht : ∀ s, Tendsto (fun n => bn n s) atTop (𝓝 (b s))) :
    Tendsto (fun n => ∫ z : Boundary × Boundary,
      (boundaryInteraction z.1 z.2+R z.1 z.2)*(bn n z.1-bn n z.2)^2*
        inner ℝ (g z.1) (g z.2) ∂boundaryMeasure.prod boundaryMeasure) atTop
      (𝓝 (∫ z : Boundary × Boundary,
        (boundaryInteraction z.1 z.2+R z.1 z.2)*(b z.1-b z.2)^2*
          inner ℝ (g z.1) (g z.2) ∂boundaryMeasure.prod boundaryMeasure)) := by
  obtain ⟨G,hG,hGb⟩ := boundary_continuous_bound hg
  apply tendsto_integral_of_dominated_convergence
    (fun z : Boundary × Boundary => ((B:ℝ)*B/Real.pi+(M+M)^2*‖R z.1 z.2‖)*(G*G))
  · intro n
    exact ((boundaryInteraction_measurable.aestronglyMeasurable.add hR.aestronglyMeasurable).mul
      ((((hb n).continuous.comp continuous_fst).sub ((hb n).continuous.comp continuous_snd)).pow 2).aestronglyMeasurable).mul
        ((hg.comp continuous_fst).inner (hg.comp continuous_snd)).aestronglyMeasurable
  · exact ((integrable_const _).add (hR.norm.const_mul ((M+M)^2))).mul_const (G*G)
  · intro n
    exact Eventually.of_forall fun z => multiplier_integrand_bound (hb n) hM hG (hMb n) hGb z.1 z.2
  · exact Eventually.of_forall fun z =>
      ((((ht z.1).sub (ht z.2)).pow 2).const_mul _).mul_const _

end StrictHotSpots.PlaneGreen
end
end MultiplierKernelConvergence

section ScalarBoundaryForm

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.Hodge
lemma cartesianForm_eq_sum {Ω : Set Plane} (μ : ℝ) (X Y : Fin 2 → H1 Ω) :
    cartesianForm μ X Y=H1.form μ (X 0) (Y 0)+H1.form μ (X 1) (Y 1) := by
  simp only [cartesianForm,cartesianEnergy,H1.form]
  ring
end StrictHotSpots.Hodge
end
end ScalarBoundaryForm

section SmoothMultiplierKernel

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω) (hΩ : AdmissibleDomain Ω)
variable {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u)
variable (hμ : 0 < firstPositiveNeumannValue Ω)

lemma datum_multiplier_integrable {w b : Plane → ℝ}
    (hw : ContDiffOn ℝ ∞ w (closure Ω)) (hb : ContDiff ℝ ∞ b) :
    let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
    Integrable (fun z : Boundary × Boundary =>
      (boundaryInteraction z.1 z.2+fullBoundaryR c.densityBound_ne_top (c.density_bound hμ.le) z.1 z.2)*
      (b (c.F z.1)-b (c.F z.2))^2 * inner ℝ (w (c.F z.1)) (w (c.F z.2)))
      (boundaryMeasure.prod boundaryMeasure) := by
  let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
  obtain ⟨A,hA⟩ := c.datumTrace_lipschitz hΩ.2.2.1 hΩ.2.2.2.2 hw
  obtain ⟨B,hB⟩ := c.datumTrace_lipschitz hΩ.2.2.1 hΩ.2.2.2.2 hb.contDiffOn
  change LipschitzWith A (fun s : Boundary => w (c.F s)) at hA
  change LipschitzWith B (fun s : Boundary => b (c.F s)) at hB
  have hR : Integrable (fun z : Boundary × Boundary =>
      fullBoundaryR c.densityBound_ne_top (c.density_bound hμ.le) z.1 z.2)
      (boundaryMeasure.prod boundaryMeasure) :=
    fullBoundaryR_integrable c.densityBound_ne_top (c.density_bound hμ.le)
  exact multiplier_integrand_integrable (E := ℝ) (g := fun s : Boundary => w (c.F s))
    (b := fun s : Boundary => b (c.F s)) hR hA hB



theorem smooth_multiplier_kernel {b : Plane → ℝ} (hb : ContDiff ℝ ∞ b)
    (hb0 : MemLp b ∞ (volume.restrict Ω)) (hb1 : MemLp (gradient b) ∞ (volume.restrict Ω)) :
    let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
    vectorForm (firstPositiveNeumannValue Ω) (c.multipliedGradient hΩ hu hμ hb)
      (c.multipliedGradient hΩ hu hμ hb) =
    (1/2:ℝ)*∫ z : Boundary × Boundary,
      (boundaryInteraction z.1 z.2+fullBoundaryR c.densityBound_ne_top (c.density_bound hμ.le) z.1 z.2)*
      (b (c.F z.1)-b (c.F z.2))^2*
      inner ℝ (closedGradient Ω u (c.F z.1)) (closedGradient Ω u (c.F z.2))
        ∂boundaryMeasure.prod boundaryMeasure := by
  let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
  let T (i : Fin 2) (z : Boundary × Boundary) :=
    (boundaryInteraction z.1 z.2+fullBoundaryR c.densityBound_ne_top (c.density_bound hμ.le) z.1 z.2)*
      (b (c.F z.1)-b (c.F z.2))^2*
      inner ℝ (fderivWithin ℝ u (closure Ω) (c.F z.1) (Hodge.e i))
        (fderivWithin ℝ u (closure Ω) (c.F z.2) (Hodge.e i))
  have hi (i : Fin 2) : Integrable (T i) (boundaryMeasure.prod boundaryMeasure) :=
    c.datum_multiplier_integrable hΩ hμ
      (closure_directional_smooth hΩ.2.1 hΩ.2.2.2.2 hu.1 (Hodge.e i)) hb
  rw [c.multipliedGradient_identity hΩ hu hμ hb hb0 hb1,
    cartesianForm_eq_sum,cartesianForm_eq_sum]
  have h0 := c.multipliedGradient_coordinate_difference hΩ hu hμ hb 0
  have h1 := c.multipliedGradient_coordinate_difference hΩ hu hμ hb 1
  change _ = (1/2:ℝ)* _ at h0 h1
  have ha : (∫ z, T 0 z ∂boundaryMeasure.prod boundaryMeasure)+
      (∫ z, T 1 z ∂boundaryMeasure.prod boundaryMeasure) =
      ∫ z : Boundary × Boundary,
        (boundaryInteraction z.1 z.2+fullBoundaryR c.densityBound_ne_top (c.density_bound hμ.le) z.1 z.2)*
        (b (c.F z.1)-b (c.F z.2))^2*
        inner ℝ (closedGradient Ω u (c.F z.1)) (closedGradient Ω u (c.F z.2))
          ∂boundaryMeasure.prod boundaryMeasure := by
    rw [← integral_add (hi 0) (hi 1)]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [Hodge.inner_two]
    simp only [T,Hodge.c,closedGradient,
      InnerProductSpace.toDual_symm_apply,Real.inner_apply]
    ring
  change (∫ z, T 0 z ∂boundaryMeasure.prod boundaryMeasure)+
    (∫ z, T 1 z ∂boundaryMeasure.prod boundaryMeasure) = _ at ha
  change _ = (1/2:ℝ)*(∫ z, T 0 z ∂boundaryMeasure.prod boundaryMeasure) at h0
  change _ = (1/2:ℝ)*(∫ z, T 1 z ∂boundaryMeasure.prod boundaryMeasure) at h1
  linarith

end StrictHotSpots.Conformal.ClosedDiskChart
end
end SmoothMultiplierKernel

section LipschitzMultiplierKernel

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal Topology
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω) (hΩ : AdmissibleDomain Ω)
variable {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u)
variable (hμ : 0 < firstPositiveNeumannValue Ω)
variable {L : ℝ} (hl : firstPositiveNeumannValue Ω < L)
  (hD : ∀ j : H10 hΩ.2.1, L*‖H10.value hΩ.2.1 j‖^2 ≤ ‖H10.grad hΩ.2.1 j‖^2)

include hΩ hu in
lemma closedGradient_trace_continuous :
    Continuous (fun s : Boundary => closedGradient Ω u (c.F s)) := by
  apply (closedGradient_continuous hΩ.2.1 hΩ.2.2.2.2 hu.1).comp_continuous
    (c.lipschitz.continuous.comp continuous_subtype_val)
  intro s
  exact c.maps_closed (boundary_mem_closed s)

include hΩ in
lemma smooth_physical_boundary_bound {b : Plane → ℝ} {B : ℝ≥0}
    (hb : LipschitzWith B b) : ∃ M : ℝ, 0 ≤ M ∧ ∀ n (s : Boundary),
      ‖ambientSmooth (planeApproxBump n) b (c.F s)‖ ≤ M := by
  have hc : Bornology.IsBounded (closure Ω) := hΩ.2.2.1.closure
  obtain ⟨M,hM,hMb⟩ := ambientSmooth_uniform_bound hc hb
  exact ⟨M,hM,fun n s => hMb n (c.F s) (c.maps_closed (boundary_mem_closed s))⟩

include hΩ in
lemma physical_multiplier_integral_tendsto
    {R : Boundary → Boundary → ℝ}
    (hR : Integrable (fun z : Boundary × Boundary => R z.1 z.2)
      (boundaryMeasure.prod boundaryMeasure))
    {g : Boundary → Plane} (hg : Continuous g)
    {b : Plane → ℝ} {B : ℝ≥0} (hb : LipschitzWith B b) :
    Tendsto (fun n => ∫ z : Boundary × Boundary,
      (boundaryInteraction z.1 z.2+R z.1 z.2)*
      (ambientSmooth (planeApproxBump n) b (c.F z.1)-ambientSmooth (planeApproxBump n) b (c.F z.2))^2*
      inner ℝ (g z.1) (g z.2) ∂boundaryMeasure.prod boundaryMeasure) atTop
      (𝓝 (∫ z : Boundary × Boundary,
      (boundaryInteraction z.1 z.2+R z.1 z.2)*(b (c.F z.1)-b (c.F z.2))^2*
      inner ℝ (g z.1) (g z.2) ∂boundaryMeasure.prod boundaryMeasure)) := by
  let bn : ℕ → Boundary → ℝ := fun n s => ambientSmooth (planeApproxBump n) b (c.F s)
  have hn (n : ℕ) : LipschitzWith ((B*c.Lip)*1) (bn n) :=
    c.physical_boundary_lipschitz (ambientSmooth_lipschitz (planeApproxBump n) hb)
  obtain ⟨M,hM,hMb⟩ := c.smooth_physical_boundary_bound hΩ hb
  have hm (n : ℕ) (s : Boundary) : ‖bn n s‖ ≤ M := hMb n s
  have ht (s : Boundary) : Tendsto (fun n => bn n s) atTop (𝓝 (b (c.F s))) :=
    ambientSmooth_tendsto planeApproxBump_rOut_tendsto hb (c.F s)
  exact multiplier_kernel_tendsto (bn:=bn) (B:=(B*c.Lip)*1) hR hg hn hM hm ht



theorem lipschitz_multiplier_kernel_oai {b : Plane → ℝ} {B : ℝ≥0}
    (hb : LipschitzWith B b) :
    let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
    vectorForm (firstPositiveNeumannValue Ω)
      (lipschitzMultipliedGradient hΩ hμ hl hD hu hb)
      (lipschitzMultipliedGradient hΩ hμ hl hD hu hb) =
    (1/2:ℝ)*∫ z : Boundary × Boundary,
      (boundaryInteraction z.1 z.2+fullBoundaryR c.densityBound_ne_top (c.density_bound hμ.le) z.1 z.2)*
      (b (c.F z.1)-b (c.F z.2))^2*
      inner ℝ (closedGradient Ω u (c.F z.1)) (closedGradient Ω u (c.F z.2))
        ∂boundaryMeasure.prod boundaryMeasure := by
  let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
  have hlhs := vectorForm_tendsto (c.multipliedGradient_tendsto hΩ hμ hl hD hu hb)
    (firstPositiveNeumannValue Ω)
  have hrhs := (c.physical_multiplier_integral_tendsto hΩ
    (fullBoundaryR_integrable c.densityBound_ne_top (c.density_bound hμ.le))
    (c.closedGradient_trace_continuous hΩ hu) hb).const_mul (1/2:ℝ)
  apply tendsto_nhds_unique hlhs
  apply hrhs.congr'
  exact Eventually.of_forall fun n => (c.smooth_multiplier_kernel hΩ hu hμ
    (ambientSmooth_smooth (planeApproxBump n) hb)
    (continuous_closure_memLp_top hΩ.2.1 hΩ.2.2.1
      (ambientSmooth_lipschitz (planeApproxBump n) hb).continuous.continuousOn)
    (lipschitz_gradient_memLp_top (ambientSmooth_lipschitz (planeApproxBump n) hb))).symm

end StrictHotSpots.Conformal.ClosedDiskChart
end
end LipschitzMultiplierKernel


end OAI
end

theorem solution : type_of% @OAI.StrictHotSpots.Conformal.ClosedDiskChart.lipschitz_multiplier_kernel_oai := @OAI.StrictHotSpots.Conformal.ClosedDiskChart.lipschitz_multiplier_kernel_oai
