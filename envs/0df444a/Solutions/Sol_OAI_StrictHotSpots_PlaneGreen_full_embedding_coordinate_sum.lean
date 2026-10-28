-- Prove2me | solution 1 for OAI.StrictHotSpots.PlaneGreen.full_embedding_coordinate_sum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T05:27:05.007081+00:00
-- url     : https://prove2.me/submissions/2babaa14-d838-404c-b156-00096cc28691

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho003

section
-- module Solutions.OAIQ3_Hot.HotSpots_Reciprocal
attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer

section SingularLayer






open Filter
open scoped Topology
namespace StrictHotSpots.BanachResolvent
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma resolvent_nonneg [PartialOrder E] [IsOrderedAddMonoid E] [OrderClosedTopology E]
    (A : E →L[ℝ] E) (hA : ‖A‖ < 1)
    (hpos : ∀ v, 0 ≤ v → 0 ≤ A v) {f : E} (hf : 0 ≤ f) :
    0 ≤ resolvent A f := by
  have ht : ∀ n : ℕ, 0 ≤ (A^n) f := by
    intro n
    induction n with
    | zero => simpa using hf
    | succ n ih => simpa only [pow_succ', mul_apply_eq_comp] using hpos _ ih
  have hs0 : HasSum (fun n : ℕ => A^n) (resolvent A) :=
    (summable_geometric_of_norm_lt_one hA).hasSum
  have hs := (ContinuousLinearMap.apply ℝ E f).hasSum hs0
  change HasSum (fun n : ℕ => (A^n) f) (resolvent A f) at hs
  rw [← hs.tsum_eq]
  exact tsum_nonneg ht

end StrictHotSpots.BanachResolvent







open MeasureTheory Filter Set TopologicalSpace
open scoped Topology ENNReal




open MeasureTheory Filter
open scoped Topology ENNReal

end SingularLayer


end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

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
-- module Solutions.OAIQ3_Hot.HotSpots_BoundaryKernel
attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer

section KernelPositivityLayer
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace

namespace StrictHotSpots.L2Limits
lemma inner_nonneg {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {f g : Lp ℝ 2 ν} (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ inner ℝ f g := by
  rw [L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [(Lp.coeFn_nonneg f).mpr hf, (Lp.coeFn_nonneg g).mpr hg] with x hx hy
  exact mul_nonneg hy hx
end StrictHotSpots.L2Limits

namespace StrictHotSpots.PlaneGreen
open DiskH10

variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ ∞)
  (hν : ν ≤ C • volume.restrict disk)

lemma row_nonneg (x : disk) : 0 ≤ row hC hν x := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [(column_memLp hC hν x).coeFn_toLp, ae_mem_disk hν] with z hz hzd
  rw [show row hC hν x z = kernel z x from hz]
  exact kernel_nonneg hzd x.property

lemma weightedIntegralOperator_order_nonneg (f : Lp ℝ 2 ν) (hf : 0 ≤ f) :
    0 ≤ weightedIntegralOperator hC hν f := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [weightedIntegralOperator_ae hC hν f, ae_mem_disk hν] with x hx hxd
  rw [hx]
  apply integral_nonneg_of_ae
  filter_upwards [(Lp.coeFn_nonneg f).mpr hf, ae_mem_disk hν] with y hy hyd
  exact mul_nonneg (kernel_nonneg hxd hyd) hy

end StrictHotSpots.PlaneGreen
end
end KernelPositivityLayer

section PlaneBoundaryLayer
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

lemma poisson_pos (s : Boundary) (x : disk) : 0 < poisson s x := by
  have hx : ‖(x : Plane)‖ < 1 := by simpa [disk] using x.property
  have hne : complexIso.symm (s : Plane) - complexIso.symm (x : Plane) ≠ 0 := by
    intro h
    have he := complexIso.symm.injective (sub_eq_zero.mp h)
    have hh := s.property
    rw [he] at hh
    linarith
  unfold poisson DiskFormula.poisson
  apply div_pos
  · simp only [LinearIsometryEquiv.norm_map]
    nlinarith [norm_nonneg (x : Plane)]
  · exact mul_pos (mul_pos (by norm_num) Real.pi_pos) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hne))

lemma boundaryInteraction_pos (s t : Boundary) (hst : s ≠ t) : 0 < boundaryInteraction s t := by
  unfold boundaryInteraction DiskFormula.boundaryInteraction
  apply one_div_pos.mpr
  apply mul_pos Real.pi_pos
  exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr
    (fun h => hst (Subtype.ext (complexIso.symm.injective h)))))

end StrictHotSpots.PlaneGreen
end
end PlaneBoundaryLayer


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



lemma smoothedRow_nonneg (s : Boundary) : 0 ≤ smoothedRow hC hν s := by
  apply (Lp.coeFn_nonneg _).mp
  filter_upwards [(smoothedPoisson_memLp hC hν s).coeFn_toLp, ae_mem_disk hν] with x hx hxd
  rw [show smoothedRow hC hν s x = smoothedPoisson (ν := ν) s x from hx]
  exact smoothedPoisson_nonneg hν s hxd

lemma fullBoundaryK_pos (hT : ‖weightedIntegralOperator hC hν‖ < 1) (p : disk) (s : Boundary) :
    0 < fullBoundaryK hC hν p s := by
  apply add_pos_of_pos_of_nonneg
  · exact add_pos_of_pos_of_nonneg (poisson_pos s p) (smoothedPoisson_nonneg hν s p.property)
  · apply L2Limits.inner_nonneg (row_nonneg hC hν p)
    exact BanachResolvent.resolvent_nonneg _ hT (weightedIntegralOperator_order_nonneg hC hν)
      (smoothedRow_nonneg hC hν s)

lemma fullBoundaryN_pos (hT : ‖weightedIntegralOperator hC hν‖ < 1) (s t : Boundary) (hst : s ≠ t) :
    0 < fullBoundaryN hC hν s t := by
  apply add_pos_of_pos_of_nonneg
  · apply add_pos_of_pos_of_nonneg
    · apply add_pos_of_pos_of_nonneg (boundaryInteraction_pos s t hst)
      apply integral_nonneg_of_ae
      filter_upwards [ae_mem_disk hν] with x hx
      exact mul_nonneg (poisson_nonneg s ⟨x,hx⟩) (poisson_nonneg t ⟨x,hx⟩)
    · apply integral_nonneg_of_ae
      filter_upwards [ae_mem_disk hν] with x hx
      exact mul_nonneg (poisson_nonneg s ⟨x,hx⟩) (smoothedPoisson_nonneg hν t hx)
  · apply L2Limits.inner_nonneg (smoothedRow_nonneg hC hν s)
    exact BanachResolvent.resolvent_nonneg _ hT (weightedIntegralOperator_order_nonneg hC hν)
      (smoothedRow_nonneg hC hν t)

end StrictHotSpots.PlaneGreen
end
end FullBoundaryKernelLayer



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

lemma fullBoundaryK_bounded (p : disk) : ∃ B : ℝ, 0 ≤ B ∧ ∀ s : Boundary,
    fullBoundaryK hC hν p s ≤ B := by
  obtain ⟨B,hB,h⟩ := green_poisson_uniform_bound hC hν
  let M : ℝ := (measureUnivNNReal ν : ℝ) ^ (2 : ℝ≥0∞).toReal⁻¹ * B
  have hM : 0 ≤ M := mul_nonneg (Real.rpow_nonneg (by positivity) _) hB
  have hs (s : Boundary) : ‖smoothedRow hC hν s‖ ≤ M := by
    apply Lp.norm_le_of_ae_bound hB
    filter_upwards [(smoothedPoisson_memLp hC hν s).coeFn_toLp, ae_mem_disk hν] with x hx hxd
    rw [show smoothedRow hC hν s x = smoothedPoisson (ν := ν) s x from hx]
    exact h x hxd s
  let A : ℝ := 1 / (2 * Real.pi * (1 - ‖(p : Plane)‖) ^ 2)
  refine ⟨A + B + ‖row hC hν p‖ * ‖BanachResolvent.resolvent (weightedIntegralOperator hC hν)‖ * M,
    by dsimp [A]; positivity, fun s => ?_⟩
  unfold fullBoundaryK
  apply add_le_add
  · apply add_le_add
    · exact DiskFormula.poisson_bounded _ _ (by simpa using s.property)
        (by simp) (by simpa [disk] using p.property)
    · exact (le_abs_self _).trans (h p p.property s)
  · calc
      _ ≤ ‖row hC hν p‖ * ‖BanachResolvent.resolvent (weightedIntegralOperator hC hν)
          (smoothedRow hC hν s)‖ := real_inner_le_norm _ _
      _ ≤ ‖row hC hν p‖ * (‖BanachResolvent.resolvent (weightedIntegralOperator hC hν)‖ * M) := by
        gcongr
        exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left (hs s) (norm_nonneg _))
      _ = _ := (mul_assoc _ _ _).symm

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

lemma fullBoundaryK_measurable (p : disk) : Measurable (fullBoundaryK hC hν p) := by
  unfold fullBoundaryK
  apply Measurable.add
  · have hm : Measurable (fun s : Boundary => (s,(p : Plane))) :=
      measurable_id.prodMk measurable_const
    have hf := (smoothedPoisson_joint_measurable (ν := ν)).comp hm
    dsimp only [Function.comp_def] at hf
    exact (poisson_continuous_boundary p).measurable.add hf
  · have hsm : StronglyMeasurable (fun s => BanachResolvent.resolvent
        (weightedIntegralOperator hC hν) (smoothedRow hC hν s)) :=
      (BanachResolvent.resolvent (weightedIntegralOperator hC hν)).continuous.comp_stronglyMeasurable
        (smoothedRow_stronglyMeasurable hC hν)
    exact (stronglyMeasurable_const.inner hsm).measurable

lemma boundaryInteraction_measurable :
    Measurable (fun z : Boundary × Boundary => boundaryInteraction z.1 z.2) := by
  unfold boundaryInteraction DiskFormula.boundaryInteraction
  fun_prop

lemma fullBoundaryN_measurable :
    Measurable (fun z : Boundary × Boundary => fullBoundaryN hC hν z.1 z.2) := by
  have hm1 : Measurable (fun z : (Boundary × Boundary) × Plane => (z.1.1,z.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have hm2 : Measurable (fun z : (Boundary × Boundary) × Plane => (z.1.2,z.2)) :=
    measurable_fst.snd.prodMk measurable_snd
  have hp1 := poisson_joint_measurable.comp hm1
  have hp2 := poisson_joint_measurable.comp hm2
  have hs2 := (smoothedPoisson_joint_measurable (ν := ν)).comp hm2
  dsimp only [Function.comp_def] at hp1 hp2 hs2
  have hp := hp1.mul hp2
  have hs := hp1.mul hs2
  have h1 := (smoothedRow_stronglyMeasurable hC hν).comp_measurable
    (measurable_fst : Measurable (Prod.fst : Boundary × Boundary → Boundary))
  have h2 := (smoothedRow_stronglyMeasurable hC hν).comp_measurable
    (measurable_snd : Measurable (Prod.snd : Boundary × Boundary → Boundary))
  have hi : StronglyMeasurable (fun z : Boundary × Boundary =>
      inner ℝ (smoothedRow hC hν z.1) (BanachResolvent.resolvent
        (weightedIntegralOperator hC hν) (smoothedRow hC hν z.2))) :=
    h1.inner ((BanachResolvent.resolvent (weightedIntegralOperator hC hν)).continuous.comp_stronglyMeasurable h2)
  exact ((boundaryInteraction_measurable.add (hp.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable).add
    (hs.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable).add hi.measurable

end StrictHotSpots.PlaneGreen
end
end BoundaryMeasurabilityLayer
end BoundaryMeasurabilityScalarSupportLayer

section BoundaryInteractionPartsScalarSupportLayer
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

include hν in
omit [IsFiniteMeasure ν] in
lemma firstInteraction_nonneg (s t : Boundary) : 0 ≤ firstInteraction (ν := ν) s t := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_mem_disk hν] with x hx
  exact mul_nonneg (poisson_nonneg s ⟨x,hx⟩) (poisson_nonneg t ⟨x,hx⟩)

include hν in
omit [IsFiniteMeasure ν] in
lemma secondInteraction_nonneg (s t : Boundary) : 0 ≤ secondInteraction (ν := ν) s t := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_mem_disk hν] with x hx
  exact mul_nonneg (poisson_nonneg s ⟨x,hx⟩) (smoothedPoisson_nonneg hν t hx)

lemma tailInteraction_nonneg (hT : ‖weightedIntegralOperator hC hν‖ < 1) (s t : Boundary) :
    0 ≤ tailInteraction hC hν s t := by
  exact L2Limits.inner_nonneg (smoothedRow_nonneg hC hν s)
    (BanachResolvent.resolvent_nonneg _ hT (weightedIntegralOperator_order_nonneg hC hν) (smoothedRow_nonneg hC hν t))

lemma fullBoundaryR_nonneg (hT : ‖weightedIntegralOperator hC hν‖ < 1) (s t : Boundary) :
    0 ≤ fullBoundaryR hC hν s t :=
  add_nonneg (add_nonneg (firstInteraction_nonneg hν s t) (secondInteraction_nonneg hν s t))
    (tailInteraction_nonneg hC hν hT s t)

end StrictHotSpots.PlaneGreen
end BoundaryInteractionPartsScalarSupportLayer

section BoundaryRRepresentationScalarSupportLayer
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

lemma fullBoundaryN_eq (s t : Boundary) : fullBoundaryN hC hν s t =
    boundaryInteraction s t + fullBoundaryR hC hν s t := by
  unfold fullBoundaryN fullBoundaryR firstInteraction secondInteraction tailInteraction
  ring

end StrictHotSpots.PlaneGreen
end BoundaryRRepresentationScalarSupportLayer

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

end StrictHotSpots.PlaneGreen
end BoundaryFormScalarSupportLayer
end
end LipschitzBoundaryScalarSupport


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Multiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section HilbertMultiplierSum

noncomputable section
open Set MeasureTheory Metric Function
open scoped InnerProductSpace Topology
namespace StrictHotSpots.HilbertMultipliers

lemma coordinate_hasSum {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (e : HilbertBasis ι ℝ H) (x : H) :
    HasSum (fun i => (inner ℝ (e i) x)^2) (‖x‖^2) := by
  have h := e.hasSum_inner_mul_inner x x
  simpa only [real_inner_comm x,← pow_two,real_inner_self_eq_norm_sq] using h



theorem coordinate_energy_sum {X H E ι : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [Countable ι] (μ : Measure X) [SFinite μ] (e : HilbertBasis ι ℝ H)
    (N : X → X → ℝ) (K : X → ℝ) (b : X → H) (g : X → E)
    (hN : ∀ s t, 0 ≤ N s t)
    (hidentity : ∀ᵐ z : X × X ∂μ.prod μ, N z.1 z.2 * ‖b z.1-b z.2‖^2 = K z.1*K z.2)
    (hKg : Integrable (fun s => K s • g s) μ)
    (hbound : Integrable (fun z : X × X =>
      N z.1 z.2 * ‖b z.1-b z.2‖^2 * (‖g z.1‖*‖g z.2‖)) (μ.prod μ))
    (hF : ∀ i, AEStronglyMeasurable (fun z : X × X => N z.1 z.2 *
      (inner ℝ (e i) (b z.1-b z.2))^2 * inner ℝ (g z.1) (g z.2)) (μ.prod μ)) :
    HasSum (fun i => (1/2:ℝ) * ∫ z : X × X, N z.1 z.2 *
      (inner ℝ (e i) (b z.1-b z.2))^2 * inner ℝ (g z.1) (g z.2) ∂μ.prod μ)
      ((1/2:ℝ)*‖∫ s, K s • g s ∂μ‖^2) := by
  let B : ι → X × X → ℝ := fun i z =>
    N z.1 z.2 * (inner ℝ (e i) (b z.1-b z.2))^2 * (‖g z.1‖*‖g z.2‖)
  have hB (z : X × X) : HasSum (fun i => B i z)
      (N z.1 z.2 * ‖b z.1-b z.2‖^2 * (‖g z.1‖*‖g z.2‖)) :=
    ((coordinate_hasSum e (b z.1-b z.2)).mul_left (N z.1 z.2)).mul_right _
  have hsum := hasSum_integral_of_dominated_convergence (μ := μ.prod μ) B hF
    (fun i => Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_of_nonneg (hN _ _),abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (mul_nonneg (hN _ _) (sq_nonneg _))))
    (Filter.Eventually.of_forall (fun z => (hB z).summable))
    (hbound.congr (Filter.Eventually.of_forall (fun z => (hB z).tsum_eq.symm)))
    (Filter.Eventually.of_forall (fun z =>
      ((coordinate_hasSum e (b z.1-b z.2)).mul_left (N z.1 z.2)).mul_right (inner ℝ (g z.1) (g z.2))))
  have hint : (∫ z : X × X, N z.1 z.2 * ‖b z.1-b z.2‖^2 *
      inner ℝ (g z.1) (g z.2) ∂μ.prod μ) = ‖∫ s, K s • g s ∂μ‖^2 := by
    calc
      _ = ∫ z : X × X, inner ℝ (K z.1 • g z.1) (K z.2 • g z.2) ∂μ.prod μ := by
        apply integral_congr_ae
        filter_upwards [hidentity] with z hz
        rw [hz,real_inner_smul_left,real_inner_smul_right]
        ring
      _ = ∫ s, ∫ t, inner ℝ (K s • g s) (K t • g t) ∂μ ∂μ := by
        exact integral_prod _ (Integrable.op_fst_snd (op := inner ℝ) (continuous_fst.inner continuous_snd)
          ⟨1, fun x y => by simpa only [one_mul] using norm_inner_le_norm x y⟩ hKg hKg)
      _ = ∫ s, inner ℝ (K s • g s) (∫ t, K t • g t ∂μ) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun s => integral_inner hKg _)
      _ = ∫ s, inner ℝ (∫ t, K t • g t ∂μ) (K s • g s) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun s => real_inner_comm _ _)
      _ = inner ℝ (∫ s, K s • g s ∂μ) (∫ s, K s • g s ∂μ) := integral_inner hKg _
      _ = _ := real_inner_self_eq_norm_sq _
  rw [hint] at hsum
  exact hsum.mul_left (1/2:ℝ)

end StrictHotSpots.HilbertMultipliers
end
end HilbertMultiplierSum

section HilbertKernelCoordinates

noncomputable section
open Set MeasureTheory Filter Metric Function
open scoped ENNReal NNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

lemma fullBoundaryN_nonneg (hT : ‖weightedIntegralOperator hC hν‖ < 1) (s t : Boundary) :
    0 ≤ fullBoundaryN hC hν s t := by
  rw [fullBoundaryN_eq]
  exact add_nonneg (by unfold boundaryInteraction DiskFormula.boundaryInteraction; positivity) (fullBoundaryR_nonneg hC hν hT s t)

lemma boundary_pair_ne : ∀ᵐ z : Boundary × Boundary ∂boundaryMeasure.prod boundaryMeasure, z.1 ≠ z.2 := by
  apply (Measure.ae_prod_iff_ae_ae (isClosed_eq continuous_fst continuous_snd).isOpen_compl.measurableSet).mpr
  exact Eventually.of_forall fun s => (boundaryMeasure.ae_ne s).mono fun _ h => h.symm


lemma full_embedding_identity {H : Type*} [NormedAddCommGroup H] (p : disk)
    (hT : ‖weightedIntegralOperator hC hν‖ < 1) {b : Boundary → H}
    (hb : ∀ s t, ‖b s-b t‖^2 = fullDistanceKernel hC hν p s t) :
    ∀ᵐ z : Boundary × Boundary ∂boundaryMeasure.prod boundaryMeasure,
      fullBoundaryN hC hν z.1 z.2 * ‖b z.1-b z.2‖^2 =
        fullBoundaryK hC hν p z.1 * fullBoundaryK hC hν p z.2 := by
  filter_upwards [boundary_pair_ne] with z hz
  rw [hb,fullDistanceKernel,ite_eq_right hz]
  exact mul_div_cancel₀ _ (fullBoundaryN_pos hC hν hT _ _ hz).ne'


theorem full_embedding_coordinate_sum_oai {H E ι : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [Countable ι] (e : HilbertBasis ι ℝ H)
    (p : disk) (hT : ‖weightedIntegralOperator hC hν‖ < 1) {b : Boundary → H}
    (hb : Continuous b) (hid : ∀ s t, ‖b s-b t‖^2 = fullDistanceKernel hC hν p s t)
    {g : Boundary → E} (hg : Continuous g) :
    HasSum (fun i => (1/2:ℝ)*∫ z : Boundary × Boundary,
      fullBoundaryN hC hν z.1 z.2 * (inner ℝ (e i) (b z.1-b z.2))^2 *
        inner ℝ (g z.1) (g z.2) ∂boundaryMeasure.prod boundaryMeasure)
      ((1/2:ℝ)*‖∫ s, fullBoundaryK hC hν p s • g s ∂boundaryMeasure‖^2) := by
  have hidentity := full_embedding_identity hC hν p hT hid
  obtain ⟨B,hB,hBK⟩ := fullBoundaryK_bounded hC hν p
  obtain ⟨M,hM,hMg⟩ := boundary_continuous_bound hg
  have hKg : Integrable (fun s => fullBoundaryK hC hν p s • g s) boundaryMeasure := by
    apply Integrable.of_bound ((fullBoundaryK_measurable hC hν p).aestronglyMeasurable.smul
      hg.aestronglyMeasurable) (B*M)
    exact Eventually.of_forall fun s => by
      change ‖fullBoundaryK hC hν p s • g s‖ ≤ B*M
      rw [norm_smul,Real.norm_of_nonneg (fullBoundaryK_pos hC hν hT p s).le]
      exact mul_le_mul (hBK s) (hMg s) (norm_nonneg _) hB
  have hKn : Integrable (fun s => fullBoundaryK hC hν p s * ‖g s‖) boundaryMeasure := by
    apply hKg.norm.congr
    exact Eventually.of_forall fun s => by
      change ‖fullBoundaryK hC hν p s • g s‖ = _
      rw [norm_smul,Real.norm_of_nonneg (fullBoundaryK_pos hC hν hT p s).le]
  apply HilbertMultipliers.coordinate_energy_sum boundaryMeasure e (fullBoundaryN hC hν)
    (fullBoundaryK hC hν p) b g (fullBoundaryN_nonneg hC hν hT) hidentity hKg
  · apply (hKn.mul_prod hKn).congr
    filter_upwards [hidentity] with z hz
    rw [hz]
    ring
  · intro i
    exact ((fullBoundaryN_measurable hC hν).mul
      ((continuous_const.inner ((hb.comp continuous_fst).sub (hb.comp continuous_snd))).measurable.pow_const 2)).mul
        ((hg.comp continuous_fst).inner (hg.comp continuous_snd)).measurable |>.aestronglyMeasurable

end StrictHotSpots.PlaneGreen
end
end HilbertKernelCoordinates


end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.StrictHotSpots.PlaneGreen.full_embedding_coordinate_sum_oai.{u_1, u_2, u_3} := @OAI.StrictHotSpots.PlaneGreen.full_embedding_coordinate_sum_oai.{u_1, u_2, u_3}
