-- Prove2me | solution 1 for OAI.StrictHotSpots.Conformal.ClosedDiskChart.multipliedGradient_coordinate_difference
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T05:34:27.307804+00:00
-- url     : https://prove2.me/submissions/47b127a4-a04c-43cf-b3c7-2701a663e314

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho004
import Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_operator_norm_lt_one
import Theorems.Thm_OAI_StrictHotSpots_Conformal_ClosedDiskChart_scalarSolution_eq_of_helmholtz
import Theorems.Thm_OAI_StrictHotSpots_PlaneGreen_boundarySolution_energy
import Theorems.Thm_OAI_StrictHotSpots_PlaneGreen_fullBoundaryR_symm

section
-- module Solutions.OAIQ3_Hot.HotSpots_Sobolev
attribute [-instance] _root_.OAI.StrictHotSpots.Douglas.haar_nullSingleton _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace _root_.OAI.StrictHotSpots.PlaneGreen.diskFinite
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
namespace StrictHotSpots

lemma integral_inner_gradient_test {Ω : Set Plane} {f φ : Plane → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    (∫ x in Ω, inner ℝ (gradient f x) (gradient φ x)) =
      -(∫ x in Ω, Δ f x * φ x) := by
  let b := stdOrthonormalBasis ℝ Plane
  have hd (i : Fin (Module.finrank ℝ Plane)) :
      ContDiffOn ℝ ∞ (fun x => fderiv ℝ f x (b i)) Ω :=
    (hf.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  have hdd (i : Fin (Module.finrank ℝ Plane)) :
      ContDiffOn ℝ ∞ (fun x => fderiv ℝ (fun y => fderiv ℝ f y (b i)) x (b i)) Ω :=
    ((hd i).fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  have he (x : Plane) : inner ℝ (gradient f x) (gradient φ x) =
      ∑ i, fderiv ℝ f x (b i) * fderiv ℝ φ x (b i) := by
    rw [← b.sum_inner_mul_inner (gradient f x) (gradient φ x)]
    simp only [inner_gradient_left, inner_gradient_right, starRingEnd_apply, star_trivial]
  have hl (x : Plane) (hx : x ∈ Ω) : Δ f x =
      ∑ i, fderiv ℝ (fun y => fderiv ℝ f y (b i)) x (b i) := by
    rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _ b]
    apply Finset.sum_congr rfl
    intro i _
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.isValue]
    rw [fderiv_clm_apply
      ((((hf x hx).contDiffAt (hΩ.mem_nhds hx)).fderiv_right (m := ∞) (by simp)).differentiableAt (by simp))
      (differentiableAt_const _)]
    simp
  have hi (i : Fin (Module.finrank ℝ Plane)) : Integrable
      (fun x => fderiv ℝ f x (b i) * fderiv ℝ φ x (b i)) (volume.restrict Ω) := by
    apply Integrable.restrict
    exact integrable_mul_test hΩ (hd i).continuousOn
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hc.fderiv_apply ℝ (b i)) ((tsupport_fderiv_apply_subset ℝ (b i)).trans hs)
  have hj (i : Fin (Module.finrank ℝ Plane)) : Integrable
      (fun x => fderiv ℝ (fun y => fderiv ℝ f y (b i)) x (b i) * φ x)
      (volume.restrict Ω) :=
    (integrable_mul_test hΩ (hdd i).continuousOn hφ.continuous hc hs).restrict
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [integral_mul_test_fderiv hΩ (hd _) hφ hc hs]
  rw [Finset.sum_neg_distrib]
  congr 1
  rw [← integral_finsetSum _ (fun i _ => hj i)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
  rw [hl x hx, Finset.sum_mul]

end StrictHotSpots







end WeightedLayer

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
-- module Solutions.OAIQ3_Hot.HotSpots_Variational
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section

section H10InclusionCombinedLayer
open Set MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots

lemma dense_smoothTestToH10 {Ω : Set Plane} (hΩ : IsOpen Ω) :
    DenseRange (smoothTestToH10 hΩ) := by
  intro u
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hu : (u : H1 Ω) ∈ closure (Set.range (smoothTestToH1 hΩ)) := u.property
  obtain ⟨v,⟨f,rfl⟩,hv⟩ := Metric.mem_closure_iff.mp hu ε hε
  exact ⟨smoothTestToH10 hΩ f, ⟨f,rfl⟩, hv⟩

end StrictHotSpots
end H10InclusionCombinedLayer


end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Helmholtz
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section

section GapWeakPDECombinedLayer
open scoped Laplacian ContDiff InnerProductSpace
open Set MeasureTheory Filter
namespace StrictHotSpots
open Laplacian

lemma directionalDerivative_contDiffOn {Ω : Set Plane} {f : Plane → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) (e : Plane) :
    ContDiffOn ℝ ∞ (directionalDerivative f e) Ω :=
  (hf.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const

lemma laplacian_eq_sum_directional {Ω : Set Plane} {f : Plane → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) {x : Plane} (hx : x ∈ Ω) :
    (Δ f) x = ∑ i : Fin 2, directionalDerivative (directionalDerivative f (planeBasis i))
      (planeBasis i) x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f planeBasis]
  apply Finset.sum_congr rfl
  intro i _
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_of_isOpen hΩ (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞) x hx).contDiffAt
      (hΩ.mem_nhds hx)).differentiableAt (by simp)
  simp only [iteratedFDeriv_two_apply]
  change ((fderiv ℝ (fderiv ℝ f) x) (planeBasis i)) (planeBasis i) =
    (fderiv ℝ (fun y => (fderiv ℝ f y) (planeBasis i)) x) (planeBasis i)
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp


end StrictHotSpots

end GapWeakPDECombinedLayer


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
-- module Solutions.OAIQ3_Hot.HotSpots_Conformal
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ConformalCoordinates


noncomputable section
open Set MeasureTheory _root_.Complex ComplexConjugate InnerProductSpace
open scoped InnerProductSpace Topology ContDiff
namespace StrictHotSpots.Conformal

lemma plane_integral_target (e : OpenPartialHomeomorph CoordinatePlane CoordinatePlane)
    (d : CoordinatePlane → ℂ) (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    (g : CoordinatePlane → ℝ) :
    (∫ y in e.target, g y) = ∫ x in e.source, ‖d x‖^2 * g (e x) := by
  have hh := integral_target_eq_integral_abs_det_fderiv_smul volume hd g
  simpa only [planeMul_det,abs_sq, smul_eq_mul] using hh

lemma plane_dirichlet_energy (e : OpenPartialHomeomorph CoordinatePlane CoordinatePlane)
    (d : CoordinatePlane → ℂ) (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    {w : CoordinatePlane → ℝ} (hw : DifferentiableOn ℝ w e.target) :
    (∫ y in e.target, ‖gradient w y‖^2) =
      ∫ x in e.source, ‖gradient (w ∘ e) x‖^2 := by
  rw [plane_integral_target e d hd]
  apply setIntegral_congr_fun e.open_source.measurableSet
  intro x hx
  dsimp only
  rw [plane_norm_gradient_comp (hd x hx)
    ((hw (e x) (e.map_source hx)).differentiableAt
      (e.open_target.mem_nhds (e.map_source hx))),mul_pow]


end StrictHotSpots.Conformal
end
end ConformalCoordinates

section CompactChartTransport




noncomputable section
open Set Filter
open scoped Topology ContDiff Classical
namespace CompactChart
variable {E : Type*} [NormedAddCommGroup E]

variable (e : OpenPartialHomeomorph E E)

lemma transport_source (f : E → ℝ) {x : E} (hx : x ∈ e.source) :
    transport e f (e x) = f x := by
  rw [transport_apply e (e.map_source hx),e.left_inv hx]

lemma transport_comp_eventuallyEq {f : E → ℝ} {x : E} (hx : x ∈ e.source) :
    (transport e f) ∘ e =ᶠ[𝓝 x] f := by
  filter_upwards [e.open_source.mem_nhds hx] with z hz
  exact transport_source e f hz

end CompactChart
end
end CompactChartTransport

section ConformalH10Tests


noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology ENNReal
namespace StrictHotSpots.Conformal

variable (e : OpenPartialHomeomorph Plane Plane)
variable (he : ContDiffOn ℝ ∞ e.symm e.target)

lemma test_grad_sq {Ω : Set Plane} (ho : IsOpen Ω) (f : smoothTestSpace Ω) :
    ‖H10.grad ho (smoothTestToH10 ho f)‖^2 = ∫ x in Ω, ‖gradient (f : Plane → ℝ) x‖^2 := by
  rw [L2VectorLimits.norm_sq_eq_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [(test_gradient_memLp (Ω:=Ω) f.property.1 f.property.2.1).coeFn_toLp] with x hx
  exact congrArg (fun t : Plane => ‖t‖^2) hx

lemma transportTest_grad_sq (d : Plane → ℂ)
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x) (f : smoothTestSpace e.source) :
    ‖H10.grad e.open_target (smoothTestToH10 e.open_target (transportTest e he f))‖^2 =
      ‖H10.grad e.open_source (smoothTestToH10 e.open_source f)‖^2 := by
  rw [test_grad_sq,test_grad_sq,plane_dirichlet_energy e d hd
    ((transportTest e he f).property.1.differentiable (by simp)).differentiableOn]
  apply setIntegral_congr_fun e.open_source.measurableSet
  intro x hx
  dsimp only
  congr 2
  change gradient ((CompactChart.transport e f) ∘ e) x = gradient (f : Plane → ℝ) x
  unfold gradient
  rw [(CompactChart.transport_comp_eventuallyEq e (f:=f) hx).fderiv_eq]

private lemma scalar_norm_bound {s t a b C : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : 0 ≤ C)
    (hsplit : t^2 = a^2+b^2) (hbsq : b^2 ≤ s^2) (hP : a ≤ C*b) :
    t ≤ (C+1)*s := by
  have hbs : b ≤ s := (sq_le_sq₀ hb hs).mp hbsq
  have ht' : t ≤ a+b := (sq_le_sq₀ ht (add_nonneg ha hb)).mp (by nlinarith)
  calc
    t ≤ a+b := ht'
    _ ≤ C*b+b := by linarith
    _ = (C+1)*b := by ring
    _ ≤ (C+1)*s := mul_le_mul_of_nonneg_left hbs (by linarith)

lemma transportTest_bound (d : Plane → ℂ)
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    (hb : Bornology.IsBounded e.target) :
    ∃ C : ℝ, ∀ f : smoothTestSpace e.source,
      ‖smoothTestToH10 e.open_target (transportTest e he f)‖ ≤
        C * ‖smoothTestToH10 e.open_source f‖ := by
  obtain ⟨C,hC,hP⟩ := H10.poincare e.open_target hb
  refine ⟨C+1,fun f => ?_⟩
  let v : H10 e.open_source := smoothTestToH10 e.open_source f
  let w : H10 e.open_target := smoothTestToH10 e.open_target (transportTest e he f)
  have hs := H10.norm_sq e.open_source v
  have ht := H10.norm_sq e.open_target w
  have heq : ‖H10.grad e.open_target w‖^2 = ‖H10.grad e.open_source v‖^2 :=
    transportTest_grad_sq e he d hd f
  have hp : ‖H10.value e.open_target w‖ ≤ C*‖H10.grad e.open_target w‖ := hP w
  have hle : ‖H10.grad e.open_source v‖^2 ≤ ‖v‖^2 := by
    calc
      ‖H10.grad e.open_source v‖^2 ≤
          ‖H10.value e.open_source v‖^2+‖H10.grad e.open_source v‖^2 :=
        le_add_of_nonneg_left (sq_nonneg _)
      _ = ‖v‖^2 := hs.symm
  exact scalar_norm_bound (norm_nonneg v) (norm_nonneg w)
    (norm_nonneg (H10.value e.open_target w)) (norm_nonneg (H10.grad e.open_target w))
    hC.le ht (heq.le.trans hle) hp

end StrictHotSpots.Conformal
end
end ConformalH10Tests

section ConformalH10





noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology ENNReal
namespace StrictHotSpots.Conformal

variable (e : OpenPartialHomeomorph Plane Plane)
variable (he : ContDiffOn ℝ ∞ e.symm e.target)

lemma transportH10_test (d : Plane → ℂ)
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    (hb : Bornology.IsBounded e.target) (f : smoothTestSpace e.source) :
    transportH10 e he (smoothTestToH10 e.open_source f) =
      smoothTestToH10 e.open_target (transportTest e he f) :=
  LinearMap.extendOfNorm_eq (dense_smoothTestToH10 e.open_source)
    (transportTest_bound e he d hd hb) f

lemma transportH10_grad_sq (d : Plane → ℂ)
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    (hb : Bornology.IsBounded e.target) (v : H10 e.open_source) :
    ‖H10.grad e.open_target (transportH10 e he v)‖^2 =
      ‖H10.grad e.open_source v‖^2 := by
  have H : (fun v : H10 e.open_source => ‖H10.grad e.open_target (transportH10 e he v)‖^2) =
      (fun v => ‖H10.grad e.open_source v‖^2) := by
    apply (dense_smoothTestToH10 e.open_source).equalizer
      (((H10.grad e.open_target).continuous.comp (transportH10 e he).continuous).norm.pow 2)
      ((H10.grad e.open_source).continuous.norm.pow 2)
    funext f
    dsimp only [Function.comp_apply]
    exact (congrArg (fun w : H10 e.open_target => ‖H10.grad e.open_target w‖^2)
      (transportH10_test e he d hd hb f)).trans (transportTest_grad_sq e he d hd f)
  exact congrFun H v

lemma transportH10_inner_grad (d : Plane → ℂ)
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    (hb : Bornology.IsBounded e.target) (v w : H10 e.open_source) :
    inner ℝ (H10.grad e.open_target (transportH10 e he v))
      (H10.grad e.open_target (transportH10 e he w)) =
      inner ℝ (H10.grad e.open_source v) (H10.grad e.open_source w) := by
  have hv := transportH10_grad_sq e he d hd hb v
  have hw := transportH10_grad_sq e he d hd hb w
  have hsum := transportH10_grad_sq e he d hd hb (v+w)
  simp only [map_add,norm_add_sq_real] at hsum
  linarith

end StrictHotSpots.Conformal
end
end ConformalH10

section ConformalMeasure




noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace StrictHotSpots.Conformal

variable (e : OpenPartialHomeomorph CoordinatePlane CoordinatePlane) (d : CoordinatePlane → ℂ)

lemma chartPull_ae (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    (f : Lp ℝ 2 (volume.restrict e.target)) :
    chartPull e d hd f =ᵐ[chartMeasure e d] f ∘ e := by
  exact (Lp.coeFn_compMeasurePreserving f (measurableChart_preserving e d hd)).trans
    ((measurableChart_ae e d).fun_comp f)

lemma chartPull_test_ae
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    {f : CoordinatePlane → ℝ} (hf : MemLp f 2 (volume.restrict e.target)) :
    chartPull e d hd (hf.toLp f) =ᵐ[chartMeasure e d] f ∘ e := by
  apply (chartPull_ae e d hd _).trans
  have hh : (hf.toLp f : CoordinatePlane → ℝ) =ᵐ[(chartMeasure e d).map e] f := by
    rw [map_chartMeasure e d hd]
    exact hf.coeFn_toLp
  exact ae_of_ae_map (chart_aemeasurable e d) hh

lemma ae_chart_source : ∀ᵐ x ∂chartMeasure e d, x ∈ e.source :=
  (chartMeasure_ac e d).ae_le (ae_restrict_mem e.open_source.measurableSet)

end StrictHotSpots.Conformal
end
end ConformalMeasure

section LpDensityClosure





noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace LpDensityClosure

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}
variable {E : Type*} [NormedAddCommGroup E]

lemma ae_eq_of_tendsto (hν : ν ≪ μ)
    {f : ℕ → Lp E 2 μ} {g : ℕ → Lp E 2 ν} {u : Lp E 2 μ} {v : Lp E 2 ν}
    (he : ∀ n, (f n : α → E) =ᵐ[ν] (g n : α → E))
    (hf : Tendsto f atTop (𝓝 u)) (hg : Tendsto g atTop (𝓝 v)) :
    (u : α → E) =ᵐ[ν] (v : α → E) := by
  obtain ⟨φ,hφ,hφae⟩ := (tendstoInMeasure_of_tendsto_Lp hf).exists_seq_tendsto_ae
  obtain ⟨ψ,hψ,hψae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hg.comp hφ.tendsto_atTop)).exists_seq_tendsto_ae
  filter_upwards [hν.ae_le hφae,hψae,ae_all_iff.mpr he] with x hx hx' heq
  apply tendsto_nhds_unique (hx.comp hψ.tendsto_atTop)
  exact hx'.congr' (Filter.Eventually.of_forall (fun n => (heq (φ (ψ n))).symm))

lemma isClosed_graph (hν : ν ≪ μ) :
    IsClosed {fg : Lp E 2 μ × Lp E 2 ν | (fg.1 : α → E) =ᵐ[ν] (fg.2 : α → E)} := by
  apply IsSeqClosed.isClosed
  intro fg uv hfg ht
  exact ae_eq_of_tendsto hν hfg (continuous_fst.tendsto uv |>.comp ht)
    (continuous_snd.tendsto uv |>.comp ht)

lemma ae_eq_of_dense {X Y : Type*} [TopologicalSpace X]
    {j : Y → X} (hj : DenseRange j) (hν : ν ≪ μ)
    {f : X → Lp E 2 μ} {g : X → Lp E 2 ν}
    (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ y, (f (j y) : α → E) =ᵐ[ν] (g (j y) : α → E)) (x : X) :
    (f x : α → E) =ᵐ[ν] (g x : α → E) := by
  have hc : IsClosed {x | (f x : α → E) =ᵐ[ν] (g x : α → E)} :=
    (isClosed_graph hν).preimage (hf.prodMk hg)
  exact closure_minimal (by rintro _ ⟨y,rfl⟩; exact hfg y) hc (hj x)

end LpDensityClosure
end
end LpDensityClosure

section ConformalWeightedValue





noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology ENNReal
namespace StrictHotSpots.Conformal
variable (e : OpenPartialHomeomorph Plane Plane)
variable (he : ContDiffOn ℝ ∞ e.symm e.target)
variable (d : Plane → ℂ)
variable (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)


lemma weightedValue_test (hb : Bornology.IsBounded e.target)
    (f : smoothTestSpace e.source) :
    (weightedValue e he d hd (smoothTestToH10 e.open_source f) : Plane → ℝ)
      =ᵐ[chartMeasure e d] f := by
  have ht := transportH10_test e he d hd hb f
  have hp : weightedValue e he d hd (smoothTestToH10 e.open_source f) =
      chartPull e d hd (H10.value e.open_target
        (smoothTestToH10 e.open_target (transportTest e he f))) :=
    congrArg (fun w : H10 e.open_target => chartPull e d hd (H10.value e.open_target w)) ht
  rw [hp]
  have ha := chartPull_test_ae e d hd
    (test_memLp (Ω:=e.target) (transportTest e he f).property.1
      (transportTest e he f).property.2.1)
  apply ha.trans
  filter_upwards [ae_chart_source e d] with x hx
  exact CompactChart.transport_source e f hx



lemma weightedValue_ae (hb : Bornology.IsBounded e.target) (v : H10 e.open_source) :
    (H10.value e.open_source v : Plane → ℝ) =ᵐ[chartMeasure e d]
      (weightedValue e he d hd v : Plane → ℝ) := by
  apply LpDensityClosure.ae_eq_of_dense (dense_smoothTestToH10 e.open_source)
    (chartMeasure_ac e d) (H10.value e.open_source).continuous
    (weightedValue e he d hd).continuous _ v
  intro f
  have hs : (H10.value e.open_source (smoothTestToH10 e.open_source f) : Plane → ℝ)
      =ᵐ[chartMeasure e d] f :=
    (chartMeasure_ac e d).ae_le
      (test_memLp (Ω:=e.source) f.property.1 f.property.2.1).coeFn_toLp
  exact hs.trans (weightedValue_test e he d hd hb f).symm

end StrictHotSpots.Conformal
end
end ConformalWeightedValue


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Riemann
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ConformalPotential





noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology ENNReal
namespace StrictHotSpots.Conformal

variable (e : OpenPartialHomeomorph Plane Plane) (d : Plane → ℂ)
variable (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)

lemma potentialMeasure_integral {μ : ℝ} (hμ : 0 ≤ μ) (f : Plane → ℝ) :
    (∫ x, f x ∂potentialMeasure e d μ) = μ * ∫ x, f x ∂chartMeasure e d := by
  rw [potentialMeasure,integral_smul_measure,ENNReal.toReal_ofReal hμ,smul_eq_mul]

end StrictHotSpots.Conformal
end
end ConformalPotential


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_ClosedChart
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_finite _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_nullSingleton _root_.OAI.StrictHotSpots.PlaneGreen.boundaryMeasure_openPos _root_.OAI.StrictHotSpots.PlaneGreen.boundary_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ClosedConformalData

noncomputable section
open Set Filter Metric
open scoped ContDiff NNReal
namespace StrictHotSpots.Conformal.ClosedDiskChart
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)



lemma diskMap_eq : c.diskMap = c.e := by
  apply OpenPartialHomeomorph.ext c.diskMap c.e (fun _ => rfl) (fun _ => rfl)
  exact c.source_eq.symm

end StrictHotSpots.Conformal.ClosedDiskChart
end
end ClosedConformalData

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

section ActualBoundaryDatum

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ContDiff InnerProductSpace NNReal
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)

lemma pullDatum_comp_toH1 (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) :
    (c.pullDatum_comp_H1 hb hs hw).toH1 = (c.pullDatum_H1 hb hs hw).toH1 := by
  apply H1.value_injective diskOpen
  apply Lp.ext
  filter_upwards [(c.pullDatum_comp_H1 hb hs hw).1.coeFn_toLp,
    (c.pullDatum_H1 hb hs hw).1.coeFn_toLp,ae_restrict_mem diskOpen.measurableSet]
    with x hx hy hxd
  exact hx.trans ((c.pullDatum_eq_inner hxd).symm.trans hy.symm)

end StrictHotSpots.Conformal.ClosedDiskChart
end
end ActualBoundaryDatum


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Pullback
attribute [-instance] _root_.OAI.StrictHotSpots.N1.completeSpace _root_.OAI.StrictHotSpots.N1.innerProductSpace _root_.OAI.StrictHotSpots.N1.normedAddCommGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ConformalSmoothEnergy

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace
namespace StrictHotSpots.Conformal

lemma complex_real_inner_mul (a u v : ℂ) :
    inner ℝ (a*u) (a*v) = ‖a‖^2 * inner ℝ u v := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.inner,Complex.mul_re,Complex.mul_im,Complex.conj_re,
    Complex.conj_im,Complex.normSq_apply]
  ring

lemma plane_inner_gradient_comp {f : Plane → Plane} {u v : Plane → ℝ}
    {a : ℂ} {x : Plane} (hf : HasFDerivAt f (planeMul a) x)
    (hu : DifferentiableAt ℝ u (f x)) (hv : DifferentiableAt ℝ v (f x)) :
    inner ℝ (gradient (u ∘ f) x) (gradient (v ∘ f) x) =
      ‖a‖^2 * inner ℝ (gradient u (f x)) (gradient v (f x)) := by
  rw [plane_gradient_comp hf hu,plane_gradient_comp hf hv,coordinate.inner_map_map,
    complex_real_inner_mul,Complex.norm_conj,coordinate.symm.inner_map_map]

lemma plane_dirichlet_pair (e : OpenPartialHomeomorph Plane Plane)
    (d : Plane → ℂ) (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    {u v : Plane → ℝ} (hu : DifferentiableOn ℝ u e.target) (hv : DifferentiableOn ℝ v e.target) :
    (∫ y in e.target, inner ℝ (gradient u y) (gradient v y)) =
      ∫ x in e.source, inner ℝ (gradient (u ∘ e) x) (gradient (v ∘ e) x) := by
  rw [plane_integral_target e d hd]
  apply setIntegral_congr_fun e.open_source.measurableSet
  intro x hx
  exact (plane_inner_gradient_comp (hd x hx)
    ((hu _ (e.map_source hx)).differentiableAt (e.open_target.mem_nhds (e.map_source hx)))
    ((hv _ (e.map_source hx)).differentiableAt (e.open_target.mem_nhds (e.map_source hx)))).symm

lemma inner_grad_toH1 {Ω : Set Plane} {u v : Plane → ℝ}
    (hu : HasH1Gradient Ω u (gradient u)) (hv : HasH1Gradient Ω v (gradient v)) :
    inner ℝ (H1.grad hu.toH1) (H1.grad hv.toH1) =
      ∫ x in Ω, inner ℝ (gradient u x) (gradient v x) := by
  rw [H1.grad_toH1,H1.grad_toH1,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu.2.1.coeFn_toLp,hv.2.1.coeFn_toLp] with x hx hy
  rw [hx,hy]

lemma inner_grad_test {Ω : Set Plane} (ho : IsOpen Ω) {w : Plane → ℝ}
    (hW : HasH1Gradient Ω w (gradient w)) (f : smoothTestSpace Ω) :
    inner ℝ (H1.grad hW.toH1) (H10.grad ho (smoothTestToH10 ho f)) =
      ∫ x in Ω, inner ℝ (gradient w x) (gradient (f : Plane → ℝ) x) := by
  change inner ℝ (H1.grad hW.toH1)
    (H1.grad ((HasH1Gradient.test ho f.property.1 f.property.2.1).toH1)) = _
  exact inner_grad_toH1 hW (HasH1Gradient.test ho f.property.1 f.property.2.1)

variable (e : OpenPartialHomeomorph Plane Plane)
    (he : ContDiffOn ℝ ∞ e.symm e.target) (d : Plane → ℂ)
    (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
    (hb : Bornology.IsBounded e.target)

include d hd in
lemma transportTest_dirichlet_pair {w : Plane → ℝ}
    (hw : DifferentiableOn ℝ w e.target) (f : smoothTestSpace e.source) :
    (∫ x in e.target, inner ℝ (gradient w x) (gradient (transportTest e he f : Plane → ℝ) x)) =
      ∫ x in e.source, inner ℝ (gradient (w ∘ e) x) (gradient (f : Plane → ℝ) x) := by
  calc
    _ = ∫ x in e.source, inner ℝ (gradient (w ∘ e) x)
        (gradient ((transportTest e he f : Plane → ℝ) ∘ e) x) :=
      plane_dirichlet_pair e d hd hw
        ((transportTest e he f).property.1.differentiable (by simp)).differentiableOn
    _ = _ := by
      apply setIntegral_congr_fun e.open_source.measurableSet
      intro x hx
      have hg : gradient ((CompactChart.transport e f) ∘ e) x = gradient (f : Plane → ℝ) x := by
        unfold gradient
        rw [(CompactChart.transport_comp_eventuallyEq e (f:=f) hx).fderiv_eq]
      exact congrArg (fun a : Plane => inner ℝ (gradient (w ∘ e) x) a) hg

include d hd in
lemma transportTest_mixed_grad {w : Plane → ℝ} (hw : DifferentiableOn ℝ w e.target)
    (hW : HasH1Gradient e.target w (gradient w))
    (hV : HasH1Gradient e.source (w ∘ e) (gradient (w ∘ e))) (f : smoothTestSpace e.source) :
    inner ℝ (H1.grad hW.toH1)
      (H10.grad e.open_target (smoothTestToH10 e.open_target (transportTest e he f))) =
      inner ℝ (H1.grad hV.toH1) (H10.grad e.open_source (smoothTestToH10 e.open_source f)) :=
  (inner_grad_test e.open_target hW (transportTest e he f)).trans
    ((transportTest_dirichlet_pair e he d hd hw f).trans (inner_grad_test e.open_source hV f).symm)

include d hd hb in


lemma transportH10_mixed_grad {w : Plane → ℝ} (hw : DifferentiableOn ℝ w e.target)
    (hW : HasH1Gradient e.target w (gradient w))
    (hV : HasH1Gradient e.source (w ∘ e) (gradient (w ∘ e))) (v : H10 e.open_source) :
    inner ℝ (H1.grad hW.toH1) (H10.grad e.open_target (transportH10 e he v)) =
      inner ℝ (H1.grad hV.toH1) (H10.grad e.open_source v) := by
  have H : (fun v : H10 e.open_source =>
      inner ℝ (H1.grad hW.toH1) (H10.grad e.open_target (transportH10 e he v))) =
      (fun v : H10 e.open_source => inner ℝ (H1.grad hV.toH1) (H10.grad e.open_source v)) := by
    apply (dense_smoothTestToH10 e.open_source).equalizer
      (continuous_const.inner ((H10.grad e.open_target).continuous.comp (transportH10 e he).continuous))
      (continuous_const.inner (H10.grad e.open_source).continuous)
    funext f
    dsimp only [Function.comp_apply]
    exact (congrArg (fun z : H10 e.open_target =>
      inner ℝ (H1.grad hW.toH1) (H10.grad e.open_target z))
      (transportH10_test e he d hd hb f)).trans (transportTest_mixed_grad e he d hd hw hW hV f)
  exact congrFun H v

end StrictHotSpots.Conformal
end
end ConformalSmoothEnergy

section ConformalAffine

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal
namespace StrictHotSpots.Conformal

variable (e : OpenPartialHomeomorph Plane Plane)
  (he : ContDiffOn ℝ ∞ e.symm e.target) (d : Plane → ℂ)
  (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
  (hb : Bornology.IsBounded e.target)

include d hd in
lemma smooth_pair_grad {w z : Plane → ℝ}
    (hw : DifferentiableOn ℝ w e.target) (hz : DifferentiableOn ℝ z e.target)
    (hW : HasH1Gradient e.target w (gradient w))
    (hZ : HasH1Gradient e.target z (gradient z))
    (hV : HasH1Gradient e.source (w ∘ e) (gradient (w ∘ e)))
    (hU : HasH1Gradient e.source (z ∘ e) (gradient (z ∘ e))) :
    inner ℝ (H1.grad hW.toH1) (H1.grad hZ.toH1) =
      inner ℝ (H1.grad hV.toH1) (H1.grad hU.toH1) :=
  (inner_grad_toH1 hW hZ).trans ((plane_dirichlet_pair e d hd hw hz).trans
    (inner_grad_toH1 hV hU).symm)

lemma inner_sum_pair {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (a b c d : E) (a' b' c' d' : F)
    (h00 : inner ℝ a c = inner ℝ a' c') (h01 : inner ℝ a d = inner ℝ a' d')
    (h10 : inner ℝ c b = inner ℝ c' b') (h11 : inner ℝ b d = inner ℝ b' d') :
    inner ℝ (a+b) (c+d) = inner ℝ (a'+b') (c'+d') := by
  simp only [inner_add_left,inner_add_right]
  have ht : inner ℝ b c = inner ℝ b' c' :=
    (real_inner_comm _ _).trans (h10.trans (real_inner_comm _ _))
  rw [h00,h01,h11,ht]

lemma inner_H1grad_add {S : Set Plane} (a b c d : H1 S) :
    inner ℝ (H1.grad (a+b)) (H1.grad (c+d)) =
      inner ℝ (H1.grad a+H1.grad b) (H1.grad c+H1.grad d) := by
  rw [map_add,map_add]

include d hd hb in
lemma affine_grad_pair {w z : Plane → ℝ}
    (hw : DifferentiableOn ℝ w e.target) (hz : DifferentiableOn ℝ z e.target)
    (hW : HasH1Gradient e.target w (gradient w))
    (hZ : HasH1Gradient e.target z (gradient z))
    (hV : HasH1Gradient e.source (w ∘ e) (gradient (w ∘ e)))
    (hU : HasH1Gradient e.source (z ∘ e) (gradient (z ∘ e)))
    (v u : H10 e.open_source) :
    inner ℝ (H1.grad (hW.toH1+(transportH10 e he v).val))
      (H1.grad (hZ.toH1+(transportH10 e he u).val)) =
    inner ℝ (H1.grad (hV.toH1+v.val)) (H1.grad (hU.toH1+u.val)) := by
  have h00 := smooth_pair_grad e d hd hw hz hW hZ hV hU
  have h01 := transportH10_mixed_grad e he d hd hb hw hW hV u
  have h10 := transportH10_mixed_grad e he d hd hb hz hZ hU v
  have h11 := transportH10_inner_grad e he d hd hb v u
  exact (inner_H1grad_add hW.toH1 (transportH10 e he v).val
    hZ.toH1 (transportH10 e he u).val).trans
    ((inner_sum_pair _ _ _ _ _ _ _ _ h00 h01 h10 h11).trans
      (inner_H1grad_add hV.toH1 v.val hU.toH1 u.val).symm)

lemma pull_affine_value {w : Plane → ℝ}
    (hW : HasH1Gradient e.target w (gradient w)) (v : H10 e.open_source) :
    chartPull e d hd (H1.value (hW.toH1+(transportH10 e he v).val)) =
      chartPull e d hd (H1.value hW.toH1)+weightedValue e he d hd v := by
  exact (chartPull e d hd).map_add (H1.value hW.toH1)
    (H1.value (transportH10 e he v).val)

lemma value_add_H10 {S : Set Plane} (ho : IsOpen S) (a : H1 S) (v : H10 ho) :
    H1.value (a+v.val) = H1.value a+H10.value ho v := H1.value.map_add a v.val

lemma ae_lp_sums {μ ν : Measure Plane} (ha : μ ≪ ν)
    (a b : Lp ℝ 2 μ) (c d : Lp ℝ 2 ν)
    (hac : (a : Plane → ℝ) =ᵐ[μ] c) (hbd : (b : Plane → ℝ) =ᵐ[μ] d) :
    (a+b : Lp ℝ 2 μ) =ᵐ[μ] (c+d : Lp ℝ 2 ν) :=
  (Lp.coeFn_add a b).trans ((hac.add hbd).trans (Filter.EventuallyEq.symm (ha.ae_le (Lp.coeFn_add c d))))

include hb in
lemma affine_value_ae {w : Plane → ℝ}
    (hW : HasH1Gradient e.target w (gradient w))
    (hV : HasH1Gradient e.source (w ∘ e) (gradient (w ∘ e))) (v : H10 e.open_source) :
    (chartPull e d hd (H1.value (hW.toH1+(transportH10 e he v).val)) : Plane → ℝ)
      =ᵐ[chartMeasure e d] H1.value (hV.toH1+v.val) := by
  have ha := chartPull_test_ae e d hd hW.1
  have hc := (chartMeasure_ac e d).ae_le hV.1.coeFn_toLp
  have hv := weightedValue_ae e he d hd hb v
  have hs := ae_lp_sums (chartMeasure_ac e d)
    (chartPull e d hd (H1.value hW.toH1)) (weightedValue e he d hd v)
    (H1.value hV.toH1) (H10.value e.open_source v) (ha.trans (Filter.EventuallyEq.symm hc)) hv.symm
  exact (Filter.EventuallyEq.of_eq (congrArg (fun f : Lp ℝ 2 (chartMeasure e d) => (f : Plane → ℝ))
    (pull_affine_value e he d hd hW v))).trans
    (hs.trans (Filter.EventuallyEq.of_eq (congrArg (fun f : Lp ℝ 2 (volume.restrict e.source) =>
      (f : Plane → ℝ)) (value_add_H10 e.open_source hV.toH1 v))).symm)

lemma isometry_value_pair {μ ν : Measure Plane}
    (L : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 ν) (a b : Lp ℝ 2 μ) {f g : Plane → ℝ}
    (ha : (L a : Plane → ℝ) =ᵐ[ν] f) (hb : (L b : Plane → ℝ) =ᵐ[ν] g) :
    inner ℝ a b = ∫ x, f x*g x ∂ν := by
  apply (L.inner_map_map a b).symm.trans
  apply (L2.inner_def _ _).trans
  apply integral_congr_ae
  filter_upwards [ha,hb] with x hx hy
  rw [hx,hy,Real.inner_apply,mul_comm]

include hd hb in
lemma affine_value_pair {w z : Plane → ℝ}
    (hW : HasH1Gradient e.target w (gradient w))
    (hZ : HasH1Gradient e.target z (gradient z))
    (hV : HasH1Gradient e.source (w ∘ e) (gradient (w ∘ e)))
    (hU : HasH1Gradient e.source (z ∘ e) (gradient (z ∘ e)))
    (v u : H10 e.open_source) :
    inner ℝ (H1.value (hW.toH1+(transportH10 e he v).val))
      (H1.value (hZ.toH1+(transportH10 e he u).val)) =
      ∫ x, H1.value (hV.toH1+v.val) x*H1.value (hU.toH1+u.val) x ∂chartMeasure e d :=
  isometry_value_pair (chartPull e d hd) _ _
    (affine_value_ae e he d hd hb hW hV v) (affine_value_ae e he d hd hb hZ hU u)

end StrictHotSpots.Conformal
end
end ConformalAffine

section ActualScalarPull

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal Laplacian
namespace StrictHotSpots.Conformal

lemma observe_inner {S : Set Plane} {ν : Measure Plane} {C : ℝ≥0∞}
    (hC : C ≠ (∞ : ℝ≥0∞)) (hν : ν ≤ C • volume.restrict S) (u v : H1 S) :
    inner ℝ (SubcriticalExtension.observe hC hν u) (SubcriticalExtension.observe hC hν v) =
      ∫ x, H1.value u x * H1.value v x ∂ν := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_LpToLpOfMeasureLeSMul hC hν (H1.value u),
    Lp.coeFn_LpToLpOfMeasureLeSMul hC hν (H1.value v)] with x hx hy
  change inner ℝ (Lp.LpToLpOfMeasureLeSMul hC hν (H1.value u) x)
    (Lp.LpToLpOfMeasureLeSMul hC hν (H1.value v) x) = _
  rw [hx,hy,real_inner_comm]
  rfl

variable (e : OpenPartialHomeomorph Plane Plane)
  (he : ContDiffOn ℝ ∞ e.symm e.target) (d : Plane → ℂ)
  (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)
  (hb : Bornology.IsBounded e.target)

namespace ClosedDiskChart
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)

lemma potential_diskMap : potentialMeasure c.diskMap c.d (firstPositiveNeumannValue Ω) =
    c.potential := congrArg (fun e => potentialMeasure e c.d (firstPositiveNeumannValue Ω)) c.diskMap_eq

end ClosedDiskChart
end StrictHotSpots.Conformal
end
end ActualScalarPull

section OriginalGradientKernel

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology InnerProductSpace Laplacian
namespace StrictHotSpots
lemma laplacian_continuousOn {Ω : Set Plane} {f : Plane → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) : ContinuousOn (Δ f) Ω := by
  have hh : ContinuousOn (fun x => ∑ i : Fin 2,
      directionalDerivative (directionalDerivative f (planeBasis i)) (planeBasis i) x) Ω :=
    continuousOn_finsetSum _ fun i _ =>
      (directionalDerivative_contDiffOn hΩ
        (directionalDerivative_contDiffOn hΩ hf (planeBasis i)) (planeBasis i)).continuousOn
  exact hh.congr fun x hx => (laplacian_eq_sum_directional hΩ hf hx)



lemma eigenfunction_helmholtz {Ω : Set Plane} {u : Plane → ℝ}
    (hΩ : IsOpen Ω) (hu : InFirstNeumannEigenspace Ω u) {x : Plane} (hx : x ∈ Ω) :
    (Δ u) x + firstPositiveNeumannValue Ω * u x = 0 := by
  have hsu : ContDiffOn ℝ ∞ u Ω := hu.1.mono subset_closure
  have hcont : ContinuousOn (fun y => (Δ u) y + firstPositiveNeumannValue Ω * u y) Ω :=
    (laplacian_continuousOn hΩ hsu).add (hsu.continuousOn.const_mul _)
  have hae := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hcont.locallyIntegrableOn hΩ.measurableSet (μ := volume)) ?_
  · have hre : (fun y => (Δ u) y + firstPositiveNeumannValue Ω * u y) =ᵐ[volume.restrict Ω]
        (fun _ => 0) := (ae_restrict_iff' hΩ.measurableSet).mpr hae
    exact (Measure.eqOn_open_of_ae_eq hre hΩ hcont continuousOn_const) hx
  intro φ hφ hc hs
  have htest := HasH1Gradient.test hΩ hφ hc
  have heq := hu.2.2.2 φ (gradient φ) htest
  rw [integral_inner_gradient_test hΩ hsu hφ hc hs] at heq
  have h1 : IntegrableOn (fun y => (Δ u) y * φ y) Ω :=
    (integrable_mul_test hΩ (laplacian_continuousOn hΩ hsu) hφ.continuous hc hs).integrableOn
  have h2 : IntegrableOn (fun y => u y * φ y) Ω :=
    (integrable_mul_test hΩ hsu.continuousOn hφ.continuous hc hs).integrableOn
  have heq0 : (∫ y in Ω, ((Δ u) y + firstPositiveNeumannValue Ω * u y) * φ y) = 0 := by
    simp only [add_mul, mul_assoc]
    rw [integral_add h1 (h2.const_mul _), integral_const_mul]
    linarith
  rw [setIntegral_mul_test hs] at heq0
  simpa only [smul_eq_mul, mul_comm] using heq0


lemma directionalDerivative_commute {Ω : Set Plane} {f : Plane → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) {x : Plane} (hx : x ∈ Ω)
    (e d : Plane) : directionalDerivative (directionalDerivative f e) d x =
      directionalDerivative (directionalDerivative f d) e x := by
  have hh := (hf x hx).contDiffAt (hΩ.mem_nhds hx)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_of_isOpen hΩ (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞) x hx).contDiffAt
      (hΩ.mem_nhds hx)).differentiableAt (by simp)
  change (fderiv ℝ (fun y => (fderiv ℝ f y) e) x) d =
    (fderiv ℝ (fun y => (fderiv ℝ f y) d) x) e
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  simpa using hh.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; decide) d e

lemma directionalDerivative_congr {Ω : Set Plane} (hΩ : IsOpen Ω)
    {f g : Plane → ℝ} (heq : EqOn f g Ω) {x : Plane} (hx : x ∈ Ω) (e : Plane) :
    directionalDerivative f e x = directionalDerivative g e x := by
  have hh : f =ᶠ[nhds x] g := Filter.eventually_of_mem (hΩ.mem_nhds hx) heq
  exact congrArg (fun L : Plane →L[ℝ] ℝ => L e) hh.fderiv_eq

lemma laplacian_directionalDerivative {Ω : Set Plane} {f : Plane → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω) {x : Plane} (hx : x ∈ Ω) (e : Plane) :
    (Δ (directionalDerivative f e)) x = directionalDerivative (Δ f) e x := by
  have D (d : Plane) := directionalDerivative_contDiffOn hΩ hf d
  have DD (d c : Plane) := directionalDerivative_contDiffOn hΩ (D d) c
  rw [laplacian_eq_sum_directional hΩ (D e) hx]
  have hs : EqOn (Δ f) (fun y => ∑ i : Fin 2,
      directionalDerivative (directionalDerivative f (planeBasis i)) (planeBasis i) y) Ω :=
    fun y hy => laplacian_eq_sum_directional hΩ hf hy
  rw [directionalDerivative_congr hΩ hs hx e]
  have heq (i : Fin 2) :
      directionalDerivative (directionalDerivative (directionalDerivative f e) (planeBasis i))
        (planeBasis i) x =
      directionalDerivative (directionalDerivative (directionalDerivative f (planeBasis i))
        (planeBasis i)) e x := by
    rw [directionalDerivative_congr hΩ
      (fun y hy => directionalDerivative_commute hΩ hf hy e (planeBasis i)) hx]
    exact directionalDerivative_commute hΩ (D (planeBasis i)) hx e (planeBasis i)
  simp_rw [heq]
  unfold directionalDerivative
  rw [fderiv_fun_sum]
  · simp
  · intro i _
    exact ((DD (planeBasis i) (planeBasis i) x hx).contDiffAt
      (hΩ.mem_nhds hx)).differentiableAt (by simp)



lemma eigenfunction_derivative_helmholtz {Ω : Set Plane} {u : Plane → ℝ}
    (hΩ : IsOpen Ω) (hu : InFirstNeumannEigenspace Ω u) {x : Plane} (hx : x ∈ Ω)
    (e : Plane) : (Δ (directionalDerivative u e)) x +
      firstPositiveNeumannValue Ω * directionalDerivative u e x = 0 := by
  have hf : ContDiffOn ℝ ∞ u Ω := hu.1.mono subset_closure
  have hs : EqOn (Δ u) (fun y => -(firstPositiveNeumannValue Ω) * u y) Ω := by
    intro y hy
    linear_combination eigenfunction_helmholtz hΩ hu hy
  rw [laplacian_directionalDerivative hΩ hf hx,
    directionalDerivative_congr hΩ hs hx e]
  have hd := ((hf x hx).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
  simp only [directionalDerivative, fderiv_const_mul hd,
    smul_apply, smul_eq_mul]
  ring

end StrictHotSpots
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Laplacian Topology
namespace StrictHotSpots
lemma closed_directional_eq {Ω : Set Plane} {u : Plane → ℝ}
    (ho : IsOpen Ω) {x : Plane} (hx : x ∈ Ω) (e : Plane) :
    fderivWithin ℝ u (closure Ω) x e = directionalDerivative u e x := by
  rw [fderivWithin_of_mem_nhds (mem_of_superset (ho.mem_nhds hx) subset_closure)]
  rfl

end StrictHotSpots
end
end
end OriginalGradientKernel


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_VectorEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualScalarEnergy

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)
variable (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
variable (hμ : 0 ≤ firstPositiveNeumannValue Ω)

lemma datumCorrection_spec {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) {B : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn)) :
    boundarySolution c.densityBound_ne_top (c.density_bound hμ)
      (c.datumTrace w hw.continuousOn) hl =
    (c.pullDatum_H1 hb hs hw).toH1+(c.datumCorrection hb hs hμ hw hl).val :=
  (c.boundarySolution_datum_class hb hs hμ hw hl).choose_spec

lemma physicalSolution_grad_pair {w z : Plane → ℝ}
    (hw : ContDiffOn ℝ ∞ w (closure Ω)) (hz : ContDiffOn ℝ ∞ z (closure Ω)) {B D : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn))
    (hk : LipschitzWith D (c.datumTrace z hz.continuousOn)) :
    inner ℝ (H1.grad (c.physicalSolution hb hs hμ hw hl))
      (H1.grad (c.physicalSolution hb hs hμ hz hk)) =
    inner ℝ (H1.grad (boundarySolution c.densityBound_ne_top (c.density_bound hμ)
      (c.datumTrace w hw.continuousOn) hl))
      (H1.grad (boundarySolution c.densityBound_ne_top (c.density_bound hμ)
      (c.datumTrace z hz.continuousOn) hk)) := by
  have hh := affine_grad_pair c.diskMap c.diskMap_inverse_smooth c.d c.diskMap_deriv hb
    ((hw.mono subset_closure).differentiableOn (by simp))
    ((hz.mono subset_closure).differentiableOn (by simp))
    (smooth_closure_H1 (Ω := Ω) (show IsOpen Ω from c.diskMap.open_target) hb hs hw)
    (smooth_closure_H1 (Ω := Ω) (show IsOpen Ω from c.diskMap.open_target) hb hs hz)
    (c.pullDatum_comp_H1 hb hs hw) (c.pullDatum_comp_H1 hb hs hz)
    (c.datumCorrection hb hs hμ hw hl) (c.datumCorrection hb hs hμ hz hk)
  apply hh.trans
  apply congrArg₂ (fun U V : H1 disk => inner ℝ (H1.grad U) (H1.grad V))
  · exact (congrArg (fun U : H1 disk => U+(c.datumCorrection hb hs hμ hw hl).val)
      (c.pullDatum_comp_toH1 hb hs hw)).trans (c.datumCorrection_spec hb hs hμ hw hl).symm
  · exact (congrArg (fun U : H1 disk => U+(c.datumCorrection hb hs hμ hz hk).val)
      (c.pullDatum_comp_toH1 hb hs hz)).trans (c.datumCorrection_spec hb hs hμ hz hk).symm

lemma physicalSolution_mass_pair {w z : Plane → ℝ}
    (hw : ContDiffOn ℝ ∞ w (closure Ω)) (hz : ContDiffOn ℝ ∞ z (closure Ω)) {B D : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn))
    (hk : LipschitzWith D (c.datumTrace z hz.continuousOn)) :
    firstPositiveNeumannValue Ω * inner ℝ (H1.value (c.physicalSolution hb hs hμ hw hl))
      (H1.value (c.physicalSolution hb hs hμ hz hk)) =
    inner ℝ (SubcriticalExtension.observe c.densityBound_ne_top (c.density_bound hμ)
      (boundarySolution c.densityBound_ne_top (c.density_bound hμ)
      (c.datumTrace w hw.continuousOn) hl))
      (SubcriticalExtension.observe c.densityBound_ne_top (c.density_bound hμ)
      (boundarySolution c.densityBound_ne_top (c.density_bound hμ)
      (c.datumTrace z hz.continuousOn) hk)) := by
  let S := boundarySolution c.densityBound_ne_top (c.density_bound hμ)
    (c.datumTrace w hw.continuousOn) hl
  let T := boundarySolution c.densityBound_ne_top (c.density_bound hμ)
    (c.datumTrace z hz.continuousOn) hk
  have hh := affine_value_pair c.diskMap c.diskMap_inverse_smooth c.d c.diskMap_deriv hb
    (smooth_closure_H1 (Ω := Ω) (show IsOpen Ω from c.diskMap.open_target) hb hs hw)
    (smooth_closure_H1 (Ω := Ω) (show IsOpen Ω from c.diskMap.open_target) hb hs hz)
    (c.pullDatum_comp_H1 hb hs hw) (c.pullDatum_comp_H1 hb hs hz)
    (c.datumCorrection hb hs hμ hw hl) (c.datumCorrection hb hs hμ hz hk)
  have hw' : (c.pullDatum_comp_H1 hb hs hw).toH1+(c.datumCorrection hb hs hμ hw hl).val=S :=
    (congrArg (fun U : H1 disk => U+(c.datumCorrection hb hs hμ hw hl).val)
      (c.pullDatum_comp_toH1 hb hs hw)).trans (c.datumCorrection_spec hb hs hμ hw hl).symm
  have hz' : (c.pullDatum_comp_H1 hb hs hz).toH1+(c.datumCorrection hb hs hμ hz hk).val=T :=
    (congrArg (fun U : H1 disk => U+(c.datumCorrection hb hs hμ hz hk).val)
      (c.pullDatum_comp_toH1 hb hs hz)).trans (c.datumCorrection_spec hb hs hμ hz hk).symm
  have hr := congrArg₂ (fun U V : H1 disk =>
    ∫ x, H1.value U x*H1.value V x ∂chartMeasure c.diskMap c.d) hw' hz'
  have hp := potentialMeasure_integral c.diskMap c.d hμ (fun x => H1.value S x*H1.value T x)
  have hq := congrArg (fun ν : Measure Plane => ∫ x, H1.value S x*H1.value T x ∂ν)
    c.potential_diskMap
  exact (congrArg (fun t : ℝ => firstPositiveNeumannValue Ω*t) (hh.trans hr)).trans
    (hp.symm.trans (hq.trans (observe_inner c.densityBound_ne_top (c.density_bound hμ) S T).symm))



theorem physicalSolution_energy (hne : Ω.Nonempty) (hμp : 0 < firstPositiveNeumannValue Ω)
    {w z : Plane → ℝ}
    (hw : ContDiffOn ℝ ∞ w (closure Ω)) (hz : ContDiffOn ℝ ∞ z (closure Ω)) {B D : ℝ≥0}
    (hl : LipschitzWith B (c.datumTrace w hw.continuousOn))
    (hk : LipschitzWith D (c.datumTrace z hz.continuousOn)) :
    let _ : IsFiniteMeasure c.potential := c.potential_finite hb
    inner ℝ (H1.grad (c.physicalSolution hb hs hμ hw hl))
      (H1.grad (c.physicalSolution hb hs hμ hz hk)) -
    firstPositiveNeumannValue Ω * inner ℝ (H1.value (c.physicalSolution hb hs hμ hw hl))
      (H1.value (c.physicalSolution hb hs hμ hz hk)) =
    (1/2:ℝ)*(∫ q : Boundary × Boundary, boundaryInteraction q.1 q.2 *
      inner ℝ (w (c.F q.1)-w (c.F q.2)) (z (c.F q.1)-z (c.F q.2))
      ∂boundaryMeasure.prod boundaryMeasure) -
    (∫ q : Boundary × Boundary, fullBoundaryR c.densityBound_ne_top (c.density_bound hμ) q.1 q.2 *
      w (c.F q.1) * z (c.F q.2) ∂boundaryMeasure.prod boundaryMeasure) := by
  let _ : IsFiniteMeasure c.potential := c.potential_finite hb
  have he := boundarySolution_energy c.densityBound_ne_top (c.density_bound hμ)
    (c.operator_norm_lt_one hb hne hμp) (c.datumTrace w hw.continuousOn)
      (c.datumTrace z hz.continuousOn) hl hk
  exact (congrArg₂ (fun a b : ℝ => a-b)
    (c.physicalSolution_grad_pair hb hs hμ hw hz hl hk)
    (c.physicalSolution_mass_pair hb hs hμ hw hz hl hk)).trans he

end StrictHotSpots.Conformal.ClosedDiskChart
end
end ActualScalarEnergy

section ActualVectorEnergy

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal Laplacian
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)
variable (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
variable (hμ : 0 < firstPositiveNeumannValue Ω)


lemma scalarSolution_energy (hne : Ω.Nonempty)
    {w z : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω))
    (hz : ContDiffOn ℝ ∞ z (closure Ω)) :
    let _ : IsFiniteMeasure c.potential := c.potential_finite hb
    inner ℝ (H1.grad (c.scalarSolution hb hs hμ hw)) (H1.grad (c.scalarSolution hb hs hμ hz)) -
    firstPositiveNeumannValue Ω*inner ℝ (H1.value (c.scalarSolution hb hs hμ hw))
      (H1.value (c.scalarSolution hb hs hμ hz)) =
    (1/2:ℝ)*(∫ q : Boundary × Boundary, boundaryInteraction q.1 q.2 *
      inner ℝ (w (c.F q.1)-w (c.F q.2)) (z (c.F q.1)-z (c.F q.2))
      ∂boundaryMeasure.prod boundaryMeasure) -
    (∫ q : Boundary × Boundary, fullBoundaryR c.densityBound_ne_top (c.density_bound hμ.le) q.1 q.2 *
      w (c.F q.1) * z (c.F q.2) ∂boundaryMeasure.prod boundaryMeasure) :=
  c.physicalSolution_energy hb hs hμ.le hne hμ hw hz _ _

end StrictHotSpots.Conformal.ClosedDiskChart
namespace StrictHotSpots

lemma closed_directional_helmholtz {Ω : Set Plane} (ho : IsOpen Ω)
    {u : Plane → ℝ} (hu : InFirstNeumannEigenspace Ω u) (e : Plane) {x : Plane} (hx : x ∈ Ω) :
    Δ (fun z => fderivWithin ℝ u (closure Ω) z e) x =
      -firstPositiveNeumannValue Ω * fderivWithin ℝ u (closure Ω) x e := by
  have heq : (fun z => fderivWithin ℝ u (closure Ω) z e) =ᶠ[nhds x]
      directionalDerivative u e :=
    Filter.eventually_of_mem (ho.mem_nhds hx) (fun _ hz => closed_directional_eq ho hz e)
  rw [(InnerProductSpace.laplacian_congr_nhds heq).eq_of_nhds,closed_directional_eq ho hx e]
  linear_combination eigenfunction_derivative_helmholtz ho hu hx e

end StrictHotSpots
end
end ActualVectorEnergy

section ActualBoundaryMultiplier

noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma harmonic_multiplier_integral {g : Boundary → E} {b : Boundary → ℝ} {A B : ℝ≥0}
    (hg : LipschitzWith A g) (hb : LipschitzWith B b) :
    (∫ z : Boundary × Boundary, boundaryInteraction z.1 z.2 *
      inner ℝ (b z.1 • g z.1-b z.2 • g z.2) (b z.1 • g z.1-b z.2 • g z.2)
        ∂boundaryMeasure.prod boundaryMeasure) -
    (∫ z : Boundary × Boundary, boundaryInteraction z.1 z.2 *
      inner ℝ (g z.1-g z.2) (b z.1^2 • g z.1-b z.2^2 • g z.2)
        ∂boundaryMeasure.prod boundaryMeasure) =
    ∫ z : Boundary × Boundary, boundaryInteraction z.1 z.2 * (b z.1-b z.2)^2 *
      inner ℝ (g z.1) (g z.2) ∂boundaryMeasure.prod boundaryMeasure := by
  obtain ⟨L,hL⟩ := boundary_smul_lipschitz hb hg
  obtain ⟨D,hD⟩ := boundary_smul_lipschitz hb hb
  have hD' : LipschitzWith D (fun s => b s^2) := by simpa only [smul_eq_mul,pow_two] using hD
  obtain ⟨F,hF⟩ := boundary_smul_lipschitz hD' hg
  rw [← integral_sub (harmonic_boundary_integrable hL hL) (harmonic_boundary_integrable hg hF)]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [← mul_sub,harmonic_multiplier_algebra,mul_assoc]

lemma interaction_multiplier_integral {R : Boundary → Boundary → ℝ}
    (hR : Integrable (fun z : Boundary × Boundary => R z.1 z.2) (boundaryMeasure.prod boundaryMeasure))
    (hRs : ∀ s t, R s t = R t s) {g : Boundary → E} {b : Boundary → ℝ}
    (hg : Continuous g) (hb : Continuous b) :
    (∫ z : Boundary × Boundary, R z.1 z.2 * inner ℝ (g z.1) (b z.2^2 • g z.2)
        ∂boundaryMeasure.prod boundaryMeasure) -
    (∫ z : Boundary × Boundary, R z.1 z.2 * inner ℝ (b z.1 • g z.1) (b z.2 • g z.2)
        ∂boundaryMeasure.prod boundaryMeasure) =
    (1/2:ℝ) * ∫ z : Boundary × Boundary, R z.1 z.2 * (b z.1-b z.2)^2 *
      inner ℝ (g z.1) (g z.2) ∂boundaryMeasure.prod boundaryMeasure := by
  let q : Measure (Boundary × Boundary) := boundaryMeasure.prod boundaryMeasure
  let f₁ := fun z : Boundary × Boundary => R z.1 z.2 * inner ℝ (b z.1^2 • g z.1) (g z.2)
  let f₂ := fun z : Boundary × Boundary => R z.1 z.2 * inner ℝ (g z.1) (b z.2^2 • g z.2)
  let f₃ := fun z : Boundary × Boundary => R z.1 z.2 * inner ℝ (b z.1 • g z.1) (b z.2 • g z.2)
  have h1 : Integrable f₁ q := interaction_boundary_integrable hR ((hb.pow 2).smul hg) hg
  have h2 : Integrable f₂ q := interaction_boundary_integrable hR hg ((hb.pow 2).smul hg)
  have h3 : Integrable f₃ q := interaction_boundary_integrable hR (hb.smul hg) (hb.smul hg)
  have hswap : (∫ z, f₁ z ∂q) = ∫ z, f₂ z ∂q := by
    change (∫ z, f₁ z ∂boundaryMeasure.prod boundaryMeasure) = _
    rw [← integral_prod_swap f₁]
    apply integral_congr_ae
    filter_upwards [] with z
    dsimp [f₁,f₂]
    rw [hRs z.2 z.1,real_inner_comm (g z.1) (b z.2^2 • g z.2)]
  have he : (fun z : Boundary × Boundary => R z.1 z.2 * (b z.1-b z.2)^2 * inner ℝ (g z.1) (g z.2)) =
      fun z => f₁ z+f₂ z-2*f₃ z := by
    funext z
    dsimp [f₁,f₂,f₃]
    simp only [real_inner_smul_left,real_inner_smul_right]
    ring
  rw [he]
  change (∫ z, f₂ z ∂q)-(∫ z, f₃ z ∂q) = (1/2:ℝ)*(∫ z, f₁ z+f₂ z-2*f₃ z ∂q)
  have h12 : Integrable (fun z => f₁ z+f₂ z) q := h1.add h2
  rw [integral_sub h12 (h3.const_mul 2),integral_add h1 h2,integral_const_mul,hswap]
  ring

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


theorem boundaryForm_multiplier_difference {R : Boundary → Boundary → ℝ} {c : Boundary → ℝ}
    (hR : Integrable (fun z : Boundary × Boundary => R z.1 z.2) (boundaryMeasure.prod boundaryMeasure))
    (hRs : ∀ s t, R s t = R t s)
    {g : Boundary → E} {b : Boundary → ℝ} {A B : ℝ≥0}
    (hg : LipschitzWith A g) (hb : LipschitzWith B b) :
    boundaryForm R c (fun s => b s • g s) (fun s => b s • g s) -
      boundaryForm R c g (fun s => b s^2 • g s) =
    (1/2:ℝ) * ∫ z : Boundary × Boundary, (boundaryInteraction z.1 z.2+R z.1 z.2) *
      (b z.1-b z.2)^2 * inner ℝ (g z.1) (g z.2) ∂boundaryMeasure.prod boundaryMeasure := by
  have hcurv : (∫ s, c s * inner ℝ (b s • g s) (b s • g s) ∂boundaryMeasure) =
      ∫ s, c s * inner ℝ (g s) (b s^2 • g s) ∂boundaryMeasure := by
    apply integral_congr_ae
    filter_upwards [] with s
    simp only [real_inner_smul_left,real_inner_smul_right]
    ring
  obtain ⟨L,hL⟩ := boundary_smul_lipschitz hb hg
  obtain ⟨D,hD⟩ := boundary_smul_lipschitz hb hb
  have hD' : LipschitzWith D (fun s => b s^2) := by simpa only [smul_eq_mul,pow_two] using hD
  obtain ⟨F,hF⟩ := boundary_smul_lipschitz hD' hg
  have h0 : Integrable (fun z : Boundary × Boundary => boundaryInteraction z.1 z.2 *
      (b z.1-b z.2)^2 * inner ℝ (g z.1) (g z.2)) (boundaryMeasure.prod boundaryMeasure) := by
    apply ((harmonic_boundary_integrable hL hL).sub (harmonic_boundary_integrable hg hF)).congr
    filter_upwards [] with z
    simp only [Pi.sub_apply]
    rw [← mul_sub,harmonic_multiplier_algebra,mul_assoc]
  have h1 : Integrable (fun z : Boundary × Boundary => R z.1 z.2 *
      (b z.1-b z.2)^2 * inner ℝ (g z.1) (g z.2)) (boundaryMeasure.prod boundaryMeasure) := by
    have := (multiplier_integrand_integrable hR hg hb).sub h0
    apply this.congr
    filter_upwards [] with z
    simp only [Pi.sub_apply]
    ring
  have he : (fun z : Boundary × Boundary => (boundaryInteraction z.1 z.2+R z.1 z.2) *
      (b z.1-b z.2)^2 * inner ℝ (g z.1) (g z.2)) =
      fun z => boundaryInteraction z.1 z.2*(b z.1-b z.2)^2*inner ℝ (g z.1) (g z.2) +
        R z.1 z.2*(b z.1-b z.2)^2*inner ℝ (g z.1) (g z.2) := by
    funext z; ring
  rw [he,integral_add h0 h1]
  have hh := harmonic_multiplier_integral hg hb
  have hi := interaction_multiplier_integral hR hRs hg.continuous hb.continuous
  unfold boundaryForm
  rw [hcurv]
  linarith

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

section ScalarBoundaryForm

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen Hodge
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)
variable (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
variable (hμ : 0 < firstPositiveNeumannValue Ω)

lemma scalarSolution_form (hne : Ω.Nonempty)
    {w z : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω))
    (hz : ContDiffOn ℝ ∞ z (closure Ω)) :
    let _ : IsFiniteMeasure c.potential := c.potential_finite hb
    H1.form (firstPositiveNeumannValue Ω) (c.scalarSolution hb hs hμ hw)
      (c.scalarSolution hb hs hμ hz) =
    boundaryForm (fullBoundaryR c.densityBound_ne_top (c.density_bound hμ.le)) 0
      (fun s : Boundary => w (c.F s)) (fun s : Boundary => z (c.F s)) := by
  let _ : IsFiniteMeasure c.potential := c.potential_finite hb
  have he := c.scalarSolution_energy hb hs hμ hne hw hz
  simp only [boundaryForm,Pi.zero_apply,zero_mul,integral_zero,add_zero,
    RCLike.inner_apply,conj_trivial] at ⊢
  change _ = _
  rw [show H1.form (firstPositiveNeumannValue Ω) (c.scalarSolution hb hs hμ hw)
    (c.scalarSolution hb hs hμ hz) = _ from he]
  congr 1
  congr 1
  funext q
  ring

end StrictHotSpots.Conformal.ClosedDiskChart
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

lemma multipliedGradient_coordinate_difference_oai {b : Plane → ℝ} (hb : ContDiff ℝ ∞ b) (i : Fin 2) :
    let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
    H1.form (firstPositiveNeumannValue Ω) (c.multipliedGradient hΩ hu hμ hb i)
      (c.multipliedGradient hΩ hu hμ hb i)-
    H1.form (firstPositiveNeumannValue Ω) (eigenGradientField hΩ hu i)
      (c.multipliedGradient hΩ hu hμ (hb.mul hb) i) =
    (1/2:ℝ)*∫ z : Boundary × Boundary,
      (boundaryInteraction z.1 z.2+fullBoundaryR c.densityBound_ne_top (c.density_bound hμ.le) z.1 z.2)*
      (b (c.F z.1)-b (c.F z.2))^2*
      inner ℝ (fderivWithin ℝ u (closure Ω) (c.F z.1) (Hodge.e i))
        (fderivWithin ℝ u (closure Ω) (c.F z.2) (Hodge.e i)) ∂boundaryMeasure.prod boundaryMeasure := by
  let _ : IsFiniteMeasure c.potential := c.potential_finite hΩ.2.2.1
  let hw := closure_directional_smooth hΩ.2.1 hΩ.2.2.2.2 hu.1 (Hodge.e i)
  have hx : eigenGradientField hΩ hu i = c.scalarSolution hΩ.2.2.1 hΩ.2.2.2.2 hμ hw :=
    (c.scalarSolution_eq_of_helmholtz hΩ.2.2.1 hΩ.2.2.2.2 hμ hΩ.1 hw
      (fun _ hx => closed_directional_helmholtz hΩ.2.1 hu (Hodge.e i) hx)).symm
  rw [hx]
  change H1.form _ (c.scalarSolution _ _ hμ (hb.contDiffOn.mul hw))
    (c.scalarSolution _ _ hμ (hb.contDiffOn.mul hw))-
    H1.form _ (c.scalarSolution _ _ hμ hw)
      (c.scalarSolution _ _ hμ ((hb.contDiffOn.mul hb.contDiffOn).mul hw)) = _
  rw [c.scalarSolution_form _ _ _ hΩ.1,c.scalarSolution_form _ _ _ hΩ.1]
  obtain ⟨A,hA⟩ := c.datumTrace_lipschitz hΩ.2.2.1 hΩ.2.2.2.2 hw
  obtain ⟨B,hB⟩ := c.datumTrace_lipschitz hΩ.2.2.1 hΩ.2.2.2.2 hb.contDiffOn
  change LipschitzWith A (fun s : Boundary => fderivWithin ℝ u (closure Ω) (c.F s) (Hodge.e i)) at hA
  change LipschitzWith B (fun s : Boundary => b (c.F s)) at hB
  exact (by simpa only [smul_eq_mul,pow_two] using
    (boundaryForm_multiplier_difference (c := (0 : Boundary → ℝ))
      (fullBoundaryR_integrable c.densityBound_ne_top (c.density_bound hμ.le))
      (fullBoundaryR_symm c.densityBound_ne_top (c.density_bound hμ.le)
        (c.operator_norm_lt_one hΩ.2.2.1 hΩ.1 hμ)) hA hB))

end StrictHotSpots.Conformal.ClosedDiskChart
end
end SmoothMultiplierKernel


end OAI
end

theorem solution : type_of% @OAI.StrictHotSpots.Conformal.ClosedDiskChart.multipliedGradient_coordinate_difference_oai := @OAI.StrictHotSpots.Conformal.ClosedDiskChart.multipliedGradient_coordinate_difference_oai
