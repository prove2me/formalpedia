-- Prove2me | solution 1 for OAI.StrictHotSpots.Conformal.ClosedDiskChart.lipschitzMultipliedGradient_closed
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T05:30:47.930627+00:00
-- url     : https://prove2.me/submissions/668a4c44-aeec-4b3b-aea4-43196d30e9fe

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho004
import Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_operator_norm_lt_one
import Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_scalarSolution_closed_ae
import Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_scalarSolution_mul_tendsto

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

lemma resolvent_right (A : E →L[ℝ] E) (hA : ‖A‖ < 1) :
    resolvent A * (1 - A) = 1 := geom_series_mul_neg A hA

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
namespace StrictHotSpots.BanachResolvent
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma apply_eq_add (T : H →L[ℝ] H) (hT : ‖T‖ < 1) (f : H) :
    resolvent T f = f + resolvent T (T f) := by
  have he := congrArg (fun A : H →L[ℝ] H => A f) (resolvent_right T hT)
  have hh : resolvent T f - resolvent T (T f) = f := by
    simpa only [mul_apply_eq_comp, sub_apply,
      one_apply_eq_self, map_sub] using he
  exact sub_eq_iff_eq_add.mp hh

end StrictHotSpots.BanachResolvent
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

end StrictHotSpots.PlaneGreen
end
end BoundaryMeasurabilityLayer
end BoundaryMeasurabilityScalarSupportLayer

section BochnerL2RowsScalarSupportLayer

open MeasureTheory Filter Set
open scoped ENNReal InnerProductSpace
namespace StrictHotSpots.L2Rows

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B} [IsFiniteMeasure μ] [IsFiniteMeasure ν]


lemma integral_eq_toLp {r : A → B → ℝ} {R : A → Lp ℝ 2 ν}
    (hR : Integrable R μ) (hr : ∀ a, R a =ᵐ[ν] r a)
    (havg : MemLp (fun x => ∫ a, r a x ∂μ) 2 ν)
    (hpair : ∀ g : Lp ℝ 2 ν, Integrable (fun z : A × B => g z.2 * r z.1 z.2) (μ.prod ν)) :
    (∫ a, R a ∂μ) = havg.toLp (fun x => ∫ a, r a x ∂μ) := by
  apply ext_inner_left ℝ
  intro g
  rw [← integral_inner hR g, L2.inner_def]
  calc
    (∫ a, inner ℝ g (R a) ∂μ) = ∫ a, ∫ x, g x * r a x ∂ν ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with a
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hr a] with x hx
      simp only [hx, Real.inner_apply]
    _ = ∫ x, ∫ a, g x * r a x ∂μ ∂ν := integral_integral_swap (hpair g)
    _ = ∫ x, inner ℝ (g x) ((havg.toLp (fun x => ∫ a, r a x ∂μ)) x) ∂ν := by
      apply integral_congr_ae
      filter_upwards [havg.coeFn_toLp] with x hx
      rw [hx, integral_const_mul]
      exact (Real.inner_apply _ _).symm

lemma integrable_pair_of_bound {r : A → B → ℝ}
    (hm : Measurable (fun z : A × B => r z.1 z.2)) {M : ℝ}
    (hM : ∀ᵐ z ∂μ.prod ν, ‖r z.1 z.2‖ ≤ M) (g : Lp ℝ 2 ν) :
    Integrable (fun z : A × B => g z.2 * r z.1 z.2) (μ.prod ν) := by
  have hg : Integrable (fun z : A × B => ‖g z.2‖ * M) (μ.prod ν) :=
    ((Lp.memLp g).integrable (by norm_num)).norm.comp_snd μ |>.mul_const M
  apply hg.mono' ((Lp.memLp g).aestronglyMeasurable.comp_snd.mul hm.aestronglyMeasurable)
  filter_upwards [hM] with z hz
  change ‖g z.2 * r z.1 z.2‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left hz (norm_nonneg _)

lemma integral_eq_toLp_of_bound {r : A → B → ℝ} {R : A → Lp ℝ 2 ν}
    (hR : Integrable R μ) (hr : ∀ a, R a =ᵐ[ν] r a)
    (hm : Measurable (fun z : A × B => r z.1 z.2)) {M : ℝ}
    (hM : ∀ᵐ z ∂μ.prod ν, ‖r z.1 z.2‖ ≤ M) :
    (∫ a, R a ∂μ) = (average_memLp hm hM).toLp (fun x => ∫ a, r a x ∂μ) :=
  integral_eq_toLp hR hr (average_memLp hm hM) (integrable_pair_of_bound hm hM)

end StrictHotSpots.L2Rows
end BochnerL2RowsScalarSupportLayer

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

lemma smoothedRow_integrable {f : Boundary → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    Integrable (fun s => f s • smoothedRow hC hν s) boundaryMeasure := by
  obtain ⟨M,hM,h⟩ := smoothedRow_uniform_bound hC hν
  apply Integrable.of_bound (hf.aestronglyMeasurable.smul
    (smoothedRow_stronglyMeasurable hC hν).aestronglyMeasurable) (B*M)
  filter_upwards [] with s
  change ‖f s • smoothedRow hC hν s‖ ≤ B*M
  rw [norm_smul]
  exact mul_le_mul (hB s) (h s) (norm_nonneg _) (le_trans (norm_nonneg (f s)) (hB s))

include hC hν in
lemma green_poisson_boundary_integrable (p : disk) :
    Integrable (fun z : Boundary × Plane => kernel p z.2 * poisson z.1 z.2)
      (boundaryMeasure.prod ν) := by
  have hm : Measurable (fun z : Boundary × Plane => kernel p z.2 * poisson z.1 z.2) :=
    (measurable_kernel.comp (measurable_const.prodMk measurable_snd)).mul poisson_joint_measurable
  apply (integrable_prod_iff' hm.aestronglyMeasurable).2
  constructor
  · filter_upwards [ae_mem_disk hν] with x hx
    exact (poisson_boundary_integrable ⟨x,hx⟩).const_mul (kernel p x)
  · apply ((kernel_memLp_weighted hC hν p p.property).integrable (by norm_num)).norm.congr
    filter_upwards [ae_mem_disk hν] with x hx
    rw [show (∫ s, ‖kernel p x * poisson s x‖ ∂boundaryMeasure) = ‖kernel p x‖ by
      simp_rw [norm_mul, Real.norm_of_nonneg (poisson_nonneg _ ⟨x,hx⟩)]
      rw [integral_const_mul, integral_poisson ⟨x,hx⟩, mul_one]]

include hC hν in
lemma green_poisson_data_integrable (p : disk) {f : Boundary → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    Integrable (fun z : Boundary × Plane => kernel p z.2 * poisson z.1 z.2 * f z.1)
      (boundaryMeasure.prod ν) := by
  apply ((green_poisson_boundary_integrable hC hν p).norm.mul_const B).mono'
    (((measurable_kernel.comp (measurable_const.prodMk measurable_snd)).mul
      poisson_joint_measurable).mul (hf.comp measurable_fst)).aestronglyMeasurable
  filter_upwards [] with z
  change ‖kernel p z.2 * poisson z.1 z.2 * f z.1‖ ≤ ‖kernel p z.2 * poisson z.1 z.2‖ * B
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hB z.1) (norm_nonneg (kernel p z.2 * poisson z.1 z.2))

include hC hν in
lemma smoothedPoisson_average (p : disk) {f : Boundary → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    (∫ s, f s * smoothedPoisson (ν := ν) s p ∂boundaryMeasure) =
      ∫ x, kernel p x * poissonExtension f x ∂ν := by
  calc
    _ = ∫ s, ∫ x, kernel p x * poisson s x * f s ∂ν ∂boundaryMeasure := by
      apply integral_congr_ae
      filter_upwards [] with s
      rw [integral_mul_const]
      exact mul_comm _ _
    _ = ∫ x, ∫ s, kernel p x * poisson s x * f s ∂boundaryMeasure ∂ν :=
      integral_integral_swap (green_poisson_data_integrable hC hν p hf hB)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [poissonExtension,smul_eq_mul, mul_assoc, integral_const_mul]

lemma smoothedRow_average {f : Boundary → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    (∫ s, f s • smoothedRow hC hν s ∂boundaryMeasure) =
      weightedIntegralOperator hC hν (poissonL2 hν hf hB) := by
  obtain ⟨M,_,hM⟩ := green_poisson_uniform_bound hC hν
  have hm : Measurable (fun z : Boundary × Plane => f z.1 * smoothedPoisson (ν := ν) z.1 z.2) :=
    (hf.comp measurable_fst).mul smoothedPoisson_joint_measurable
  have hb : ∀ᵐ z ∂boundaryMeasure.prod ν,
      ‖f z.1 * smoothedPoisson (ν := ν) z.1 z.2‖ ≤ B*M := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hm.norm measurable_const)).2
    filter_upwards [] with s
    filter_upwards [ae_mem_disk hν] with x hx
    change ‖f s * smoothedPoisson (ν := ν) s x‖ ≤ B*M
    rw [norm_mul]
    exact mul_le_mul (hB s) (hM x hx s) (norm_nonneg _)
      (le_trans (norm_nonneg (f s)) (hB s))
  have hr (s : Boundary) : (f s • smoothedRow hC hν s) =ᵐ[ν]
      (fun x => f s * smoothedPoisson (ν := ν) s x) := by
    filter_upwards [Lp.coeFn_smul (f s) (smoothedRow hC hν s),
      (smoothedPoisson_memLp hC hν s).coeFn_toLp] with x hx hpx
    rw [hx]
    change f s * smoothedRow hC hν s x = _
    rw [show smoothedRow hC hν s x = smoothedPoisson (ν := ν) s x from hpx]
  rw [L2Rows.integral_eq_toLp_of_bound (r := fun s x => f s * smoothedPoisson (ν := ν) s x)
    (smoothedRow_integrable hC hν hf hB) hr hm hb]
  · apply Lp.ext
    filter_upwards [(L2Rows.average_memLp (r := fun s x => f s * smoothedPoisson (ν := ν) s x) hm hb).coeFn_toLp,
      weightedIntegralOperator_ae hC hν (poissonL2 hν hf hB),ae_mem_disk hν] with x hx ht hxd
    rw [hx,ht,smoothedPoisson_average hC hν ⟨x,hxd⟩ hf hB]
    apply integral_congr_ae
    filter_upwards [(poissonExtension_memLp hν hf hB).coeFn_toLp] with y hy
    rw [show poissonL2 hν hf hB y = poissonExtension f y from hy]
end StrictHotSpots.PlaneGreen
end BoundaryExtensionScalarSupportLayer

section BoundaryKRepresentationScalarSupportLayer
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ ∞) (hν : ν ≤ C • volume.restrict disk)

omit [IsFiniteMeasure ν] in
lemma inner_row (p : disk) (g : Lp ℝ 2 ν) :
    inner ℝ (row hC hν p) g = ∫ x, kernel p x * g x ∂ν := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(column_memLp hC hν p).coeFn_toLp] with x hx
  change inner ℝ (row hC hν p x) (g x) = _
  rw [show row hC hν p x = kernel x p from hx,kernel_symm x p,Real.inner_apply]

lemma inner_row_poissonL2 (p : disk) {f : Boundary → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    inner ℝ (row hC hν p) (poissonL2 hν hf hB) =
      ∫ x, kernel p x * poissonExtension f x ∂ν := by
  rw [inner_row]
  apply integral_congr_ae
  filter_upwards [(poissonExtension_memLp hν hf hB).coeFn_toLp] with x hx
  rw [show poissonL2 hν hf hB x = poissonExtension f x from hx]


lemma fullBoundaryK_representation (hT : ‖weightedIntegralOperator hC hν‖ < 1)
    (p : disk) {f : Boundary → ℝ} (hf : Measurable f)
    {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    (∫ s, fullBoundaryK hC hν p s * f s ∂boundaryMeasure) =
      fullExtension hC hν hf hB p := by
  let T := weightedIntegralOperator hC hν
  let R := BanachResolvent.resolvent T
  have hI := smoothedRow_integrable hC hν hf hB
  have hRI := R.integrable_comp hI
  have htail : (∫ s, f s * inner ℝ (row hC hν p) (R (smoothedRow hC hν s)) ∂boundaryMeasure) =
      inner ℝ (row hC hν p) (R (T (poissonL2 hν hf hB))) := by
    calc
      _ = ∫ s, inner ℝ (row hC hν p) (R (f s • smoothedRow hC hν s)) ∂boundaryMeasure := by
        apply integral_congr_ae
        filter_upwards [] with s
        rw [map_smul,inner_smul_right]
      _ = _ := by rw [integral_inner hRI, R.integral_comp_comm hI,smoothedRow_average hC hν hf hB]
  have htailI : Integrable (fun s => f s * inner ℝ (row hC hν p) (R (smoothedRow hC hν s))) boundaryMeasure := by
    convert hRI.const_inner (row hC hν p) using 1
    funext s
    rw [map_smul,inner_smul_right]
  have hP : Integrable (fun s => poisson s p * f s) boundaryMeasure := by
    apply ((poisson_boundary_integrable p).norm.mul_const B).mono'
      ((poisson_continuous_boundary p).measurable.mul hf).aestronglyMeasurable
    filter_upwards [] with s
    change ‖poisson s p * f s‖ ≤ ‖poisson s p‖ * B
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB s) (norm_nonneg _)
  have hF : Integrable (fun s => f s * smoothedPoisson (ν := ν) s p) boundaryMeasure := by
    have h := (green_poisson_data_integrable hC hν p hf hB).integral_prod_left
    convert h using 1
    funext s
    change f s * smoothedPoisson (ν := ν) s p = ∫ x, kernel p x * poisson s x * f s ∂ν
    rw [integral_mul_const]
    exact mul_comm _ _
  calc
    _ = (∫ s, poisson s p * f s ∂boundaryMeasure) +
        (∫ s, f s * smoothedPoisson (ν := ν) s p ∂boundaryMeasure) +
        (∫ s, f s * inner ℝ (row hC hν p) (R (smoothedRow hC hν s)) ∂boundaryMeasure) := by
      have hPF : Integrable (fun s => poisson s p * f s + f s * smoothedPoisson (ν := ν) s p) boundaryMeasure := hP.add hF
      rw [← integral_add hP hF,← integral_add hPF htailI]
      apply integral_congr_ae
      filter_upwards [] with s
      unfold fullBoundaryK
      dsimp only [R,T]
      ring
    _ = fullExtension hC hν hf hB p := by
      rw [smoothedPoisson_average hC hν p hf hB, htail, ← inner_row_poissonL2 hC hν p hf hB]
      change poissonExtension f p + inner ℝ (row hC hν p) _ + inner ℝ (row hC hν p) _ = _
      have hr := BanachResolvent.apply_eq_add (weightedIntegralOperator hC hν) hT (poissonL2 hν hf hB)
      rw [fullExtension,hr,inner_add_right]
      ring
end StrictHotSpots.PlaneGreen
end BoundaryKRepresentationScalarSupportLayer

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

lemma expand (x : Plane) : c 0 x • e 0 + c 1 x • e 1 = x := by
  simpa only [Fin.sum_univ_two, OrthonormalBasis.repr_apply_apply, real_inner_comm] using planeBasis.sum_repr x
end StrictHotSpots.Hodge


end PlaneDifferentialInteriorSupportLayer



end

end ActualVectorSupport

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_GreenSolution
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section UniformL3

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StrictHotSpots.L2Limits



lemma unifIntegrable_iff'_compat {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ι → α → ℝ} {p : ℝ≥0∞}
    (h : ∀ ε : ℝ≥0∞, 0 < ε → ∃ δ : ℝ≥0∞, 0 < δ ∧ ∀ i s, MeasurableSet s → μ s ≤ δ →
      eLpNorm (f i) p (μ.restrict s) ≤ ε) : UnifIntegrable f p μ := by
  intro ε hε
  obtain ⟨δ, hδ, hs⟩ := h (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  refine ⟨(min δ 1).toNNReal, ?_, fun i s hmeas hμ => ?_⟩
  · exact ENNReal.toNNReal_pos (lt_min hδ one_pos).ne' (lt_of_le_of_lt (min_le_right _ _) ENNReal.one_lt_top).ne
  · rw [eLpNorm_indicator_eq_eLpNorm_restrict hmeas]
    apply hs i s hmeas
    refine hμ.trans ?_
    rw [ENNReal.ofReal_coe_nnreal, ENNReal.coe_toNNReal (lt_of_le_of_lt (min_le_right _ _) ENNReal.one_lt_top).ne]
    exact min_le_left _ _

lemma unifIntegrable_two_of_three {α ι : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ι → α → ℝ} (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hb : ∀ i, eLpNorm (f i) 3 μ ≤ B) :
    UnifIntegrable f 2 μ := by
  apply unifIntegrable_iff'_compat
  intro ε hε
  have ht : Tendsto (fun t : ℝ => B * (ENNReal.ofReal t) ^ (1/6 : ℝ)) (𝓝 0) (𝓝 0) := by
    exact (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hB (by norm_num : (0:ℝ)<1/6)).comp
      (by simpa using ENNReal.continuous_ofReal.tendsto (0:ℝ))
  have he : ∀ᶠ t : ℝ in 𝓝 0, B * (ENNReal.ofReal t) ^ (1/6:ℝ) < ε :=
    ht.eventually (eventually_lt_nhds hε)
  obtain ⟨r,hr,hrb⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨ENNReal.ofReal (r/2), ENNReal.ofReal_pos.mpr (half_pos hr),
    fun i s hs hμs => ?_⟩
  have htt : B * (ENNReal.ofReal (r/2)) ^ (1/6:ℝ) < ε :=
    hrb (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hr)]
      using (half_lt_self hr))
  calc
    eLpNorm (f i) 2 (μ.restrict s) ≤ eLpNorm (f i) 3 (μ.restrict s) * (μ s)^(1/6:ℝ) := by
      simpa only [Measure.restrict_apply MeasurableSet.univ, univ_inter,
        ENNReal.toReal_ofNat, show (1/(2:ℝ)-1/3) = 1/6 by norm_num] using
        (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict s)
          (by norm_num : (2:ℝ≥0∞)≤3) (hf i).restrict)
    _ ≤ B * (ENNReal.ofReal (r/2)) ^ (1/6:ℝ) := by
      gcongr
      exact (eLpNorm_mono_measure (f i) Measure.restrict_le_self).trans (hb i)
    _ ≤ ε := htt.le

end StrictHotSpots.L2Limits
end
end UniformL3

section GreenRowContinuous

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology InnerProductSpace ENNReal
namespace StrictHotSpots.PlaneGreen
open DiskH10

variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ (∞ : ℝ≥0∞))
  (hν : ν ≤ C • volume.restrict disk)

lemma row_eq_toLp (x : disk) : row hC hν x =
    (kernel_memLp_weighted hC hν x x.property).toLp (kernel x) := by
  apply Lp.ext
  filter_upwards [(column_memLp hC hν x).coeFn_toLp,
    (kernel_memLp_weighted hC hν x x.property).coeFn_toLp] with y hy hx
  exact hy.trans ((kernel_symm y x).trans hx.symm)



lemma green_integral_eq_inner (f : Lp ℝ 2 ν) (x : disk) :
    (∫ y, kernel x y * f y ∂ν) = inner ℝ (row hC hν x) f := by
  rw [row_eq_toLp hC hν,MeasurableL2Kernel.integral_mul_eq_inner
    (kernel_memLp_weighted hC hν x x.property) (Lp.memLp f),Lp.toLp_coeFn]

end StrictHotSpots.PlaneGreen
end
end GreenRowContinuous

section BoundaryPoissonTransport

noncomputable section
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.PlaneGreen
open DiskH10
local notation "τ" => (2*Real.pi)

lemma poissonExtension_eq_planePoisson (f : C(Boundary,ℝ)) {x : Plane} (hx : x ∈ disk) :
    poissonExtension f x = Douglas.planePoisson (boundaryAngleData f) x := by
  rw [poissonExtension,integral_boundary_angles]
  unfold Douglas.planePoisson
  rw [Douglas.poissonExtension_re_eq_circleAverage _
    (by simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hx)]
  unfold Real.circleAverage
  simp_rw [poisson_eq_standard]
  simp only [smul_eq_mul,Pi.mul_apply,mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [Douglas.circleDatum_circleMap,boundaryAngleData_apply,Complex.ofReal_re]
  have ha : angleBoundary (θ : AddCircle τ) = circleBoundary (Circle.exp θ) := rfl
  rw [ha]
  change poissonKernel 0 (complexIso.symm x)
      (complexIso.symm (complexIso (Circle.exp θ : ℂ))) * _ =
    poissonKernel 0 (complexIso.symm x) (circleMap 0 1 θ) * _
  simp [circleMap,Circle.coe_exp]


end StrictHotSpots.PlaneGreen
end
end BoundaryPoissonTransport

section GreenSolveContinuous

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ (∞ : ℝ≥0∞))
  (hν : ν ≤ C • volume.restrict disk)

lemma boundarySolutionValue_eq_fullExtension [IsFiniteMeasure ν]
    (f : C(Boundary,ℝ)) {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) (x : disk) :
    boundarySolutionValue hC hν f hB x = fullExtension hC hν f.continuous.measurable hB x := by
  rw [boundarySolutionValue,fullExtension,green_integral_eq_inner hC hν]



theorem boundarySolution_K [IsFiniteMeasure ν]
    (hT : ‖weightedIntegralOperator hC hν‖ < 1)
    (f : C(Boundary,ℝ)) {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) (x : disk) :
    boundarySolutionValue hC hν f hB x =
      ∫ s, fullBoundaryK hC hν x s * f s ∂boundaryMeasure := by
  rw [boundarySolutionValue_eq_fullExtension hC hν]
  exact (fullBoundaryK_representation hC hν hT x f.continuous.measurable hB).symm

end StrictHotSpots.PlaneGreen
end
end GreenSolveContinuous


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_VectorEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualVectorSupport
noncomputable section

section VectorSobolevActualCompatibleLayer
open Set MeasureTheory Filter
open scoped InnerProductSpace ContDiff
namespace StrictHotSpots.Hodge
variable {Ω : Set Plane}


lemma axisL_ae (i : Fin 2) (u : Lp ℝ 2 (volume.restrict Ω)) :
    axisL Ω i u =ᵐ[volume.restrict Ω] fun x => u x • e i :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight (e i)).coeFn_compLpL u

end StrictHotSpots.Hodge
end VectorSobolevActualCompatibleLayer

section VectorDefectEnergyActualCompatibleLayer
open Set MeasureTheory Filter
open scoped InnerProductSpace ContDiff
namespace StrictHotSpots.Hodge
variable {Ω : Set Plane}

lemma axis_sum_ae (a b : Lp ℝ 2 (volume.restrict Ω)) :
    axisL Ω 0 a+axisL Ω 1 b =ᵐ[volume.restrict Ω] fun x => a x • e 0+b x • e 1 := by
  filter_upwards [axisL_ae 0 a,axisL_ae 1 b,Lp.coeFn_add (axisL Ω 0 a) (axisL Ω 1 b)]
    with x ha hb hs
  exact hs.trans (congrArg₂ (fun u v : Plane => u+v) ha hb)

end StrictHotSpots.Hodge
end VectorDefectEnergyActualCompatibleLayer

section NormalMultiplierActualCompatibleLayer
open Set MeasureTheory Filter
open scoped InnerProductSpace ContDiff ENNReal
namespace StrictHotSpots.Hodge
variable {Ω : Set Plane}

lemma vectorValue_ae (X : Fin 2 → H1 Ω) : vectorValue X =ᵐ[volume.restrict Ω]
    fun x => H1.value (X 0) x • e 0+H1.value (X 1) x • e 1 := axis_sum_ae _ _

end StrictHotSpots.Hodge
end NormalMultiplierActualCompatibleLayer

open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
end
end ActualVectorSupport


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Multiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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

include hΩ in
lemma smooth_physical_boundary_bound {b : Plane → ℝ} {B : ℝ≥0}
    (hb : LipschitzWith B b) : ∃ M : ℝ, 0 ≤ M ∧ ∀ n (s : Boundary),
      ‖ambientSmooth (planeApproxBump n) b (c.F s)‖ ≤ M := by
  have hc : Bornology.IsBounded (closure Ω) := hΩ.2.2.1.closure
  obtain ⟨M,hM,hMb⟩ := ambientSmooth_uniform_bound hc hb
  exact ⟨M,hM,fun n s => hMb n (c.F s) (c.maps_closed (boundary_mem_closed s))⟩

end StrictHotSpots.Conformal.ClosedDiskChart
end
end LipschitzMultiplierKernel


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_ClosedSolution
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section GreenClosedContinuous

noncomputable section
open Set MeasureTheory Filter Metric
open scoped Topology InnerProductSpace ENNReal
namespace StrictHotSpots.PlaneGreen
open DiskH10

lemma kernel_continuousAt_left_closed {x y : Plane} (hx : x ∈ closure disk)
    (hy : y ∈ disk) (hxy : x ≠ y) : ContinuousAt (fun z => kernel z y) x := by
  have hx1 := norm_le_of_mem_closure_disk hx
  have hy1 : ‖y‖ < 1 := by simpa only [disk,mem_ball_zero_iff] using hy
  have hx2 : 0 ≤ 1-‖x‖^2 := by nlinarith [norm_nonneg x]
  have hy2 : 0 ≤ 1-‖y‖^2 := by nlinarith [norm_nonneg y]
  have hn : ‖x-y‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))
  have ha : 1+(1-‖x‖^2)*(1-‖y‖^2)/‖x-y‖^2 ≠ 0 := by positivity
  simp_rw [kernel_plane_formula]
  fun_prop (disch := assumption)

variable {ν : Measure Plane} {C : ℝ≥0∞} (hC : C ≠ (∞ : ℝ≥0∞))
  (hν : ν ≤ C • volume.restrict disk)

include hC hν in
lemma kernel_uniform_three_bound_closed : ∃ B : ℝ≥0∞, B ≠ ∞ ∧
    ∀ x ∈ closure disk, eLpNorm (kernel x) 3 ν ≤ B := by
  obtain ⟨B,hB,h⟩ := kernel_uniform_three_bound_weighted hC hν
  refine ⟨B,hB,fun x hx => ?_⟩
  by_cases hi : ‖x‖ < 1
  · exact h x (mem_disk_of_norm_lt hi)
  · have hn : ‖x‖ = 1 := le_antisymm (norm_le_of_mem_closure_disk hx) (not_lt.mp hi)
    have he : kernel x = 0 := funext (kernel_zero_left hn)
    rw [he,eLpNorm_zero]
    exact bot_le



lemma closedRow_continuous [IsFiniteMeasure ν] : Continuous (closedRow hC hν) := by
  apply continuous_iff_seqContinuous.mpr
  intro u x hu
  simp only [Function.comp_def,closedRow]
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => kernel (u n))
    (fun n => kernel_memLp_closed hC hν _ (u n).property) (kernel x)
    (kernel_memLp_closed hC hν _ x.property)).mpr
  apply tendsto_Lp_finite_of_tendsto_ae (by norm_num) (by norm_num)
    (fun n => (kernel_memLp_closed hC hν _ (u n).property).aestronglyMeasurable)
    (kernel_memLp_closed hC hν _ x.property)
  · obtain ⟨B,hB,h⟩ := kernel_uniform_three_bound_closed hC hν
    exact L2Limits.unifIntegrable_two_of_three
      (fun n => (kernel_memLp_closed hC hν _ (u n).property).aestronglyMeasurable)
      hB (fun n => h _ (u n).property)
  · have hne : ∀ᵐ y ∂ν, y ≠ (x:Plane) :=
      ((volume.restrict disk).ae_ne (x:Plane)).filter_mono
        (Measure.absolutelyContinuous_of_le_smul hν).ae_le
    filter_upwards [ae_mem_disk hν,hne] with y hyd hyx
    exact (kernel_continuousAt_left_closed x.property hyd hyx.symm).tendsto.comp
      ((continuous_subtype_val.tendsto x).comp hu)

lemma green_integral_eq_closedInner (f : Lp ℝ 2 ν) (x : closure disk) :
    (∫ y, kernel x y*f y ∂ν) = inner ℝ (closedRow hC hν x) f := by
  rw [MeasurableL2Kernel.integral_mul_eq_inner
    (kernel_memLp_closed hC hν x x.property) (Lp.memLp f),Lp.toLp_coeFn]
  rfl

include hC hν in
lemma green_integral_continuousOn_closure [IsFiniteMeasure ν] (f : Lp ℝ 2 ν) :
    ContinuousOn (fun x : Plane => ∫ y, kernel x y*f y ∂ν) (closure disk) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  change Continuous (fun x : closure disk => ∫ y, kernel x y*f y ∂ν)
  simp_rw [green_integral_eq_closedInner hC hν]
  exact (closedRow_continuous hC hν).inner continuous_const

lemma green_integral_boundary (f : Lp ℝ 2 ν) {x : Plane} (hx : x ∈ frontier disk) :
    (∫ y, kernel x y*f y ∂ν) = 0 := by
  have hn : ‖x‖ = 1 := by
    simpa only [disk,frontier_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0),
      mem_sphere_zero_iff_norm] using hx
  simp only [kernel_zero_left hn,zero_mul,integral_zero]

end StrictHotSpots.PlaneGreen
end
end GreenClosedContinuous

section BoundaryClosedSolution

noncomputable section
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.PlaneGreen
open DiskH10

lemma boundaryClosedPoisson_interior (f : C(Boundary,ℝ)) {x : Plane} (hx : x ∈ disk) :
    boundaryClosedPoisson f x = poissonExtension f x :=
  (Douglas.closedPlanePoisson_eqOn (boundaryAngleData f) hx).trans
    (poissonExtension_eq_planePoisson f hx).symm

lemma boundaryClosedPoisson_trace (f : C(Boundary,ℝ)) (s : Boundary) :
    boundaryClosedPoisson f s = f s := by
  obtain ⟨t,rfl⟩ := angleBoundary.surjective s
  rw [angleBoundary_coe]
  exact Douglas.closedPlanePoisson_boundary (boundaryAngleData f) t

lemma boundaryClosedPoisson_continuousOn (f : C(Boundary,ℝ)) {A : ℝ≥0}
    (hf : LipschitzWith A f) : ContinuousOn (boundaryClosedPoisson f) (closure disk) :=
  Douglas.closedPlanePoisson_continuousOn (boundaryAngleData f) A.coe_nonneg
    (boundaryAngleData_lipschitz f hf)

variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ (∞ : ℝ≥0∞)) (hν : ν ≤ C • volume.restrict disk)



lemma boundaryClosedSolution_interior (f : C(Boundary,ℝ)) {B : ℝ}
    (hB : ∀ s, ‖f s‖ ≤ B) {x : Plane} (hx : x ∈ disk) :
    boundaryClosedSolution hC hν f hB x = boundarySolutionValue hC hν f hB x := by
  exact congrArg (fun a => a + ∫ y, kernel x y *
    (BanachResolvent.resolvent (weightedIntegralOperator hC hν)
      (poissonL2 hν f.continuous.measurable hB)) y ∂ν) (boundaryClosedPoisson_interior f hx)

lemma boundaryClosedSolution_continuousOn (f : C(Boundary,ℝ)) {A : ℝ≥0}
    (hf : LipschitzWith A f) {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) :
    ContinuousOn (boundaryClosedSolution hC hν f hB) (closure disk) :=
  (boundaryClosedPoisson_continuousOn f hf).add
    (green_integral_continuousOn_closure hC hν _)

lemma boundaryClosedSolution_trace (f : C(Boundary,ℝ)) {B : ℝ}
    (hB : ∀ s, ‖f s‖ ≤ B) (s : Boundary) :
    boundaryClosedSolution hC hν f hB s = f s := by
  have hs : (s:Plane) ∈ frontier disk := by
    simpa only [disk,frontier_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0), mem_sphere, dist_zero_right] using s.property
  rw [boundaryClosedSolution,green_integral_boundary _ hs,add_zero,boundaryClosedPoisson_trace]


lemma boundaryClosedSolution_K (hT : ‖weightedIntegralOperator hC hν‖ < 1)
    (f : C(Boundary,ℝ)) {B : ℝ} (hB : ∀ s, ‖f s‖ ≤ B) (x : disk) :
    boundaryClosedSolution hC hν f hB x =
      ∫ s, fullBoundaryK hC hν x s*f s ∂boundaryMeasure := by
  rw [boundaryClosedSolution_interior hC hν f hB x.property]
  exact boundarySolution_K hC hν hT f hB x

end StrictHotSpots.PlaneGreen
end
end BoundaryClosedSolution

section BoundaryClosedConvergence

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal Topology
namespace StrictHotSpots.PlaneGreen
open DiskH10
variable {ν : Measure Plane} [IsFiniteMeasure ν] {C : ℝ≥0∞}
  (hC : C ≠ (∞ : ℝ≥0∞)) (hν : ν ≤ C • volume.restrict disk)

lemma boundaryClosedSolution_tendsto (hT : ‖weightedIntegralOperator hC hν‖ < 1)
    (fn : ℕ → C(Boundary,ℝ)) (f : C(Boundary,ℝ)) {M B : ℝ}
    (hm : ∀ n s, ‖fn n s‖ ≤ M) (hb : ∀ s, ‖f s‖ ≤ B)
    (ht : ∀ s, Tendsto (fun n => fn n s) atTop (𝓝 (f s))) (p : disk) :
    Tendsto (fun n => boundaryClosedSolution hC hν (fn n) (hm n) p)
      atTop (𝓝 (boundaryClosedSolution hC hν f hb p)) := by
  obtain ⟨A,hA,hAb⟩ := fullBoundaryK_bounded hC hν p
  have hn (s : Boundary) : ‖fullBoundaryK hC hν p s‖ ≤ A := by
    rw [Real.norm_of_nonneg (fullBoundaryK_pos hC hν hT p s).le]
    exact hAb s
  simp only [boundaryClosedSolution_K hC hν hT]
  apply tendsto_integral_of_dominated_convergence (fun _ : Boundary => A*M)
  · intro n
    exact ((fullBoundaryK_measurable hC hν p).mul (fn n).continuous.measurable).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Eventually.of_forall fun s => (norm_mul _ _).trans_le
      (mul_le_mul (hn s) (hm n s) (norm_nonneg _) hA)
  · exact Eventually.of_forall fun s => (ht s).const_mul _

end StrictHotSpots.PlaneGreen
end
end BoundaryClosedConvergence

section PhysicalMultiplierClosed

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal Topology
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω) (hΩ : AdmissibleDomain Ω)
variable (hμ : 0 < firstPositiveNeumannValue Ω)
variable {L : ℝ} (hl : firstPositiveNeumannValue Ω < L)
  (hD : ∀ j : H10 hΩ.2.1, L*‖H10.value hΩ.2.1 j‖^2 ≤ ‖H10.grad hΩ.2.1 j‖^2)

include hΩ in
lemma multiplierTrace_lipschitz {b w : Plane → ℝ} {B : ℝ≥0} (hb : LipschitzWith B b)
    (hw : ContDiffOn ℝ ∞ w (closure Ω)) :
    ∃ A : ℝ≥0, LipschitzWith A (c.multiplierTrace hb w hw.continuousOn) := by
  obtain ⟨D,hD⟩ := c.datumTrace_lipschitz hΩ.2.2.1 hΩ.2.2.2.2 hw
  exact boundary_smul_lipschitz (c.physical_boundary_lipschitz hb) hD

lemma physical_lipschitzMul_closed_ae {w b : Plane → ℝ}
    (hw : ContDiffOn ℝ ∞ w (closure Ω)) {B : ℝ≥0} (hb : LipschitzWith B b)
    {A : ℝ} (hA : ∀ s, ‖c.multiplierTrace hb w hw.continuousOn s‖ ≤ A) :
    let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
    (H1.value (PhysicalHelmholtz.extension hΩ.2.1 hΩ.2.2.1 hμ.le hl hD
      (H1.lipschitzMul hΩ.2.1 hΩ.2.2.1 hb (smooth_closure_H1 hΩ.2.1 hΩ.2.2.1 hΩ.2.2.2.2 hw).toH1)) : Plane → ℝ)
      =ᵐ[volume.restrict Ω]
      (boundaryClosedSolution c.densityBound_ne_top (c.density_bound hμ.le)
        (c.multiplierTrace hb w hw.continuousOn) hA) ∘ c.G := by
  let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
  let hn (n : ℕ) := (ambientSmooth_smooth (planeApproxBump n) hb).contDiffOn.mul hw
  let fn (n : ℕ) := c.datumTrace _ (hn n).continuousOn
  obtain ⟨M,hM,hMb⟩ := c.smooth_physical_boundary_bound hΩ hb
  obtain ⟨W,hW,hWb⟩ := boundary_continuous_bound (c.datumTrace w hw.continuousOn).continuous
  have hMW (n : ℕ) (s : Boundary) : ‖fn n s‖ ≤ M*W := by
    change ‖ambientSmooth (planeApproxBump n) b (c.F s)*w (c.F s)‖ ≤ M*W
    rw [norm_mul]
    exact mul_le_mul (hMb n s) (hWb s) (norm_nonneg _) hM
  have ht (s : Boundary) : Tendsto (fun n => fn n s) atTop
      (𝓝 (c.multiplierTrace hb w hw.continuousOn s)) :=
    (ambientSmooth_tendsto planeApproxBump_rOut_tendsto hb (c.F s)).mul_const _
  have he (n : ℕ) := c.scalarSolution_closed_ae hΩ hμ (hn n) (hMW n)
  have hv := H1.value.continuous.continuousAt.tendsto.comp
    (c.scalarSolution_mul_tendsto hΩ hμ hl hD hw hb)
  obtain ⟨φ,hφ,hφae⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  filter_upwards [hφae,ae_all_iff.mpr he,ae_restrict_mem hΩ.2.1.measurableSet] with x hx hxe hxΩ
  have hxD : c.G x ∈ disk := by
    rw [← c.diskMap_inverse_agrees hxΩ]
    exact c.diskMap.map_target hxΩ
  have hk := boundaryClosedSolution_tendsto c.densityBound_ne_top (c.density_bound hμ.le)
    (c.operator_norm_lt_one hΩ.2.2.1 hΩ.1 hμ) fn (c.multiplierTrace hb w hw.continuousOn)
    hMW hA ht ⟨c.G x,hxD⟩
  apply tendsto_nhds_unique hx
  exact (hk.comp hφ.tendsto_atTop).congr' (Eventually.of_forall fun n => (hxe (φ n)).symm)

end StrictHotSpots.Conformal.ClosedDiskChart
end
end PhysicalMultiplierClosed


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Eigenfunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ClosedNullGradient

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal Topology
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω) (hΩ : AdmissibleDomain Ω)
variable (hμ : 0 < firstPositiveNeumannValue Ω)
variable {L : ℝ} (hl : firstPositiveNeumannValue Ω < L)
  (hD : ∀ j : H10 hΩ.2.1, L*‖H10.value hΩ.2.1 j‖^2 ≤ ‖H10.grad hΩ.2.1 j‖^2)

include c



theorem lipschitzMultipliedGradient_closed_oai {u : Plane → ℝ}
    (hu : InFirstNeumannEigenspace Ω u) {b : Plane → ℝ} {B : ℝ≥0}
    (hb : LipschitzWith B b) :
    ∃ Y : Plane → Plane, ContinuousOn Y (closure Ω) ∧
      EqOn Y (fun x => b x • closedGradient Ω u x) (frontier Ω) ∧
      (vectorValue (lipschitzMultipliedGradient hΩ hμ hl hD hu hb) : Plane → Plane)
        =ᵐ[volume.restrict Ω] Y := by
  let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
  let w (i : Fin 2) (x : Plane) := fderivWithin ℝ u (closure Ω) x (Hodge.e i)
  have hw (i : Fin 2) : ContDiffOn ℝ ∞ (w i) (closure Ω) :=
    closure_directional_smooth hΩ.2.1 hΩ.2.2.2.2 hu.1 (Hodge.e i)
  let f (i : Fin 2) := c.multiplierTrace hb (w i) (hw i).continuousOn
  obtain ⟨A,hA⟩ : ∃ A : Fin 2 → ℝ, ∀ i s, ‖f i s‖ ≤ A i := by
    have hh (i : Fin 2) : ∃ a : ℝ, ∀ s, ‖f i s‖ ≤ a := by
      obtain ⟨a,_,ha⟩ := boundary_continuous_bound (f i).continuous
      exact ⟨a,ha⟩
    exact Classical.skolem.mp hh
  let S (i : Fin 2) := boundaryClosedSolution c.densityBound_ne_top (c.density_bound hμ.le) (f i) (hA i)
  have hSc (i : Fin 2) : ContinuousOn (S i) (closure disk) := by
    obtain ⟨D,hD⟩ := c.multiplierTrace_lipschitz hΩ hb (hw i)
    exact boundaryClosedSolution_continuousOn _ _ (f i) hD (hA i)
  let Y (x : Plane) := S 0 (c.G x) • Hodge.e 0 + S 1 (c.G x) • Hodge.e 1
  have hY : ContinuousOn Y (closure Ω) := by
    exact ((hSc 0).comp c.inverse_lipschitz.continuous.continuousOn c.inverse_maps_closed).smul continuousOn_const |>.add
      (((hSc 1).comp c.inverse_lipschitz.continuous.continuousOn c.inverse_maps_closed).smul continuousOn_const)
  have hae (i : Fin 2) :
      (H1.value (lipschitzMultipliedGradient hΩ hμ hl hD hu hb i) : Plane → ℝ)
        =ᵐ[volume.restrict Ω] (S i) ∘ c.G :=
    c.physical_lipschitzMul_closed_ae hΩ hμ hl hD (hw i) hb (hA i)
  refine ⟨Y,hY,?_,?_⟩
  · intro x hx
    have hxD := c.inverse_maps_boundary hx
    have hnorm : ‖c.G x‖ = 1 := by
      simpa only [disk,frontier_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0),
        Metric.mem_sphere,dist_zero_right] using hxD
    let s : Boundary := ⟨c.G x,hnorm⟩
    have he (i : Fin 2) : S i (c.G x) = b x*w i x := by
      change S i s = _
      rw [show S i s = f i s from boundaryClosedSolution_trace _ _ (f i) (hA i) s]
      change b (c.F (c.G x))*w i (c.F (c.G x)) = _
      rw [c.right_inverse x hx.1]
    have hwc (i : Fin 2) : w i x = Hodge.c i (closedGradient Ω u x) := by
      exact InnerProductSpace.toDual_symm_apply.symm
    change S 0 (c.G x) • Hodge.e 0 + S 1 (c.G x) • Hodge.e 1 = _
    rw [he 0,he 1,hwc 0,hwc 1,mul_smul,mul_smul,← smul_add,expand]
  · filter_upwards [vectorValue_ae (lipschitzMultipliedGradient hΩ hμ hl hD hu hb),hae 0,hae 1]
      with x hx h0 h1
    exact hx.trans (congrArg₂ (fun a b : ℝ => a • Hodge.e 0+b • Hodge.e 1) h0 h1)




end StrictHotSpots.Conformal.ClosedDiskChart
end
end ClosedNullGradient

end OAI
end

theorem solution : type_of% @OAI.StrictHotSpots.Conformal.ClosedDiskChart.lipschitzMultipliedGradient_closed_oai := @OAI.StrictHotSpots.Conformal.ClosedDiskChart.lipschitzMultipliedGradient_closed_oai
