-- Prove2me | solution 1 for OAI.CubicTorus.cmc_weak_continuous_C1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:18:17.424596+00:00
-- url     : https://prove2.me/submissions/d7a71259-c82f-4913-8a0d-e8e7537f1aa7

import Mathlib
import Definitions.Def_OAIQ079A000
import Theorems.Thm_OAI_CubicTorus_cmc_linearized_holder_gradient

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVNormalTiltMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution
open Laplacian
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]

lemma fderiv_compact_convolution {f k : X → ℝ} (hf : LocallyIntegrable f μ)
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hs : HasCompactSupport k) (x v : X) :
    fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) x v =
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] (fun y ↦ fderiv ℝ k y v)) x := by
  rw [(hs.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf
    (hk.of_le (by simp)) x).fderiv]
  exact convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hf (hs.fderiv ℝ)
    (hk.continuous_fderiv (by simp)) x v

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]

lemma real_convolution_comm (f g : X → ℝ) :
    f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] g = g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] f := by
  ext x
  rw [convolution_mul_swap, convolution_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun _ ↦ mul_comm _ _)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Compactness_BVWeyl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]

omit [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] in
lemma continuous_compact_norm_bound {Y : Type*} [NormedAddCommGroup Y]
    {g : X → Y} (hg : Continuous g) (hs : HasCompactSupport g) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖g x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hg.norm.bddAbove_range_of_hasCompactSupport hs.norm
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  exact (hC (mem_range_self x)).trans (le_max_left _ _)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_BVTorusGraphFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Convolution
namespace CubicTorus

lemma graphSmoothingMeasure_radius (b : ContDiffBump (0 : Plane)) :
    ∀ᵐ y ∂graphSmoothingMeasure b, ‖y‖ ≤ b.rOut := by
  rw [graphSmoothingMeasure, ae_withDensity_iff b.continuous_normed.measurable.ennreal_ofReal]
  filter_upwards [] with y hy
  have hh : y ∈ Function.support (b.normed volume) := by
    change b.normed volume y ≠ 0
    intro he
    simp [he] at hy
  rw [b.support_normed_eq, Metric.mem_ball, dist_zero_right] at hh
  exact hh.le

lemma graphSmooth_eq_convolution (b : ContDiffBump (0 : Plane)) (f : Plane → ℝ) :
    graphSmooth b f = b.normed volume ⋆ f := by
  funext x
  rw [graphSmooth, graphSmoothingMeasure,
    integral_withDensity_eq_integral_toReal_smul b.continuous_normed.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (b.nonneg_normed _), convolution_def,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Compactness_GraphMollifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphMollifier_radius_tendsto :
    Tendsto (fun i ↦ (graphMollifier i).rOut) atTop (𝓝 0) := by
  simpa only [graphMollifier,one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_DifferenceStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_local_cutoff {f η : Plane → ℝ} {U : Set Plane}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hη : Continuous η)
    (hs : tsupport η⊆U) : Continuous (fun y ↦ η y*f y) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y∈tsupport η
  · exact hη.continuousAt.mul ((hf y (hs hy)).continuousAt (hU.mem_nhds (hs hy)))
  · apply (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp [hz]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_local_vector_cutoff {f : Plane → Plane} {η : Plane → ℝ} {U : Set Plane}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hη : Continuous η)
    (hs : tsupport η⊆U) : Continuous (fun y ↦ η y • f y) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y∈tsupport η
  · exact hη.continuousAt.smul ((hf y (hs hy)).continuousAt (hU.mem_nhds (hs hy)))
  · apply (continuousAt_const (y := (0:Plane))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp [hz]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_PlaneWeakGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma PlaneWeakGradient.congr {S : Set Plane} {u u' : Plane → ℝ} {G G' : Plane → Plane}
    (h : PlaneWeakGradient S u G) (hu : u'=ᵐ[volume] u) (hG : G'=ᵐ[volume] G) :
    PlaneWeakGradient S u' G' := by
  intro v ψ hψ hc hs
  have ha : (∫ y,⟪G' y,v⟫*ψ y)=(∫ y,⟪G y,v⟫*ψ y) :=
    integral_congr_ae (hG.mono fun _ he ↦ by dsimp only; rw [he])
  have hb : (∫ y,u' y*fderiv ℝ ψ y v)=(∫ y,u y*fderiv ℝ ψ y v) :=
    integral_congr_ae (hu.mono fun _ he ↦ by dsimp only; rw [he])
  rw [ha,hb]
  exact h v ψ hψ hc hs

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_CmcStretch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma PlaneWeakGradient.local_congr {S : Set Plane} (hS : MeasurableSet S)
    {u u' : Plane → ℝ} {G G' : Plane → Plane} (h : PlaneWeakGradient S u G)
    (hu : u'=ᵐ[volume.restrict S] u) (hG : G'=ᵐ[volume.restrict S] G) :
    PlaneWeakGradient S u' G' := by
  have hu' := (ae_restrict_iff' hS).mp hu
  have hG' := (ae_restrict_iff' hS).mp hG
  intro v ψ hψ hc hs
  have hleft : (∫ y,⟪G' y,v⟫*ψ y)=(∫ y,⟪G y,v⟫*ψ y) := by
    apply integral_congr_ae
    filter_upwards [hG'] with y hy
    by_cases hys : y∈S
    · rw [hy hys]
    · rw [image_eq_zero_of_notMem_tsupport (fun hh ↦ hys (hs hh)),mul_zero,mul_zero]
  have hright : (∫ y,u' y*fderiv ℝ ψ y v)=(∫ y,u y*fderiv ℝ ψ y v) := by
    apply integral_congr_ae
    filter_upwards [hu'] with y hy
    by_cases hys : y∈S
    · rw [hy hys]
    · rw [fderiv_of_notMem_tsupport ℝ (fun hh ↦ hys (hs hh)),zero_apply,mul_zero,mul_zero]
  rw [hleft,hright]
  exact h v ψ hψ hc hs

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma PlaneWeakGradient.mono {S T : Set Plane} {u : Plane → ℝ} {G : Plane → Plane}
    (h : PlaneWeakGradient S u G) (hTS : T⊆S) : PlaneWeakGradient T u G := by
  intro v ψ hψ hc hs
  exact h v ψ hψ hc (hs.trans hTS)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_HolderNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace Convolution
namespace CubicTorus

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [NormedSpace ℝ F] [CompleteSpace F] in
lemma compact_probability_average_integrable [NormedSpace ℝ F] [CompleteSpace F] {f : Plane → F}
    (hf : Continuous f) (hc : HasCompactSupport f) (b : ContDiffBump (0 : Plane)) (x : Plane) :
    Integrable (fun y ↦ f (x-y)) (graphSmoothingMeasure b) := by
  obtain ⟨C,hC,hbound⟩ := continuous_compact_norm_bound hf hc
  exact Integrable.of_bound (hf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    C (Eventually.of_forall fun y ↦ hbound (x-y))

lemma compact_probability_average_uniform {f : Plane → F}
    (hf : Continuous f) (hc : HasCompactSupport f) :
    TendstoUniformly (fun i x ↦ ∫ y,f (x-y) ∂graphSmoothingMeasure (graphMollifier i)) f atTop := by
  have hu : UniformContinuous f := hf.uniformContinuous_of_tendsto_cocompact hc.is_zero_at_infty
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuous_iff.mp hu (ε/2) (half_pos hε)
  filter_upwards [graphMollifier_radius_tendsto.eventually (Iio_mem_nhds hδ)] with i hi x
  have hfi := compact_probability_average_integrable hf hc (graphMollifier i) x
  have he : (∫ _y : Plane,f x ∂graphSmoothingMeasure (graphMollifier i))=f x := by simp
  rw [dist_comm,dist_eq_norm,← he,← integral_sub hfi (integrable_const _)]
  calc
    _ ≤ ∫ _y : Plane,ε/2 ∂graphSmoothingMeasure (graphMollifier i) :=
      norm_integral_le_of_norm_le (integrable_const _) (by
        filter_upwards [graphSmoothingMeasure_radius (graphMollifier i)] with y hy
        have hd : dist (x-y) x<δ := by
          simpa only [dist_eq_norm,sub_sub_cancel_left,norm_neg] using hy.trans_lt hi
        simpa only [dist_eq_norm] using (hclose hd).le)
    _ < ε := by simp; linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace Convolution
namespace CubicTorus

lemma test_kernel_support {R : ℝ} {x : Plane} (hx : x∈Metric.ball (0 : Plane) (R/2))
    (b : ContDiffBump (0 : Plane)) (hb : b.rOut<R/2) :
    tsupport (fun y ↦ b.normed volume (x-y))⊆Metric.ball 0 R := by
  have hs : tsupport (fun y ↦ b.normed volume (x-y))⊆
      (fun y ↦ x-y) ⁻¹' tsupport (b.normed volume) :=
    tsupport_comp_subset_preimage (f := fun y : Plane ↦ x-y) (b.normed volume)
      ((continuous_const : Continuous (fun _ : Plane ↦ x)).sub continuous_id)
  intro y hy
  have hh := hs hy
  have he : tsupport (b.normed (volume : Measure Plane))=Metric.closedBall 0 b.rOut :=
    b.tsupport_normed_eq
  change x-y∈tsupport (b.normed volume) at hh
  rw [he,Metric.mem_closedBall,dist_zero_right] at hh
  have hx' : ‖x‖<R/2 := by simpa only [Metric.mem_ball,dist_zero_right] using hx
  change dist y 0<R
  rw [dist_zero_right]
  calc
    ‖y‖ = ‖x-(x-y)‖ := by rw [sub_sub_cancel]
    _ ≤ ‖x‖+‖x-y‖ := norm_sub_le _ _
    _ < R/2+R/2 := add_lt_add hx' (hh.trans_lt hb)
    _ = R := by ring

lemma PlaneWeakGradient.smooth_hasFDerivAt {R : ℝ} {f : Plane → ℝ} {G : Plane → Plane}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hG : Continuous G) (hGc : HasCompactSupport G)
    (hw : PlaneWeakGradient (Metric.ball 0 R) f G)
    (b : ContDiffBump (0 : Plane)) (hb : b.rOut<R/2)
    {x : Plane} (hx : x∈Metric.ball (0 : Plane) (R/2)) :
    HasFDerivAt (graphSmooth b f)
      ((InnerProductSpace.toDual ℝ Plane) (∫ y,G (x-y) ∂graphSmoothingMeasure b)) x := by
  have hfi : Integrable f (volume : Measure Plane) := hf.integrable_of_hasCompactSupport hfc
  have he : graphSmooth b f=f ⋆[ContinuousLinearMap.mul ℝ ℝ,volume] b.normed volume := by
    rw [graphSmooth_eq_convolution]
    exact real_convolution_comm _ _
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (graphSmooth b f) := by
    rw [he]
    exact b.hasCompactSupport_normed.contDiff_convolution_right
      (ContinuousLinearMap.mul ℝ ℝ) hfi.locallyIntegrable b.contDiff_normed
  apply (hsm.differentiable (by simp)).differentiableAt.hasFDerivAt.congr_fderiv
  ext v
  rw [he,fderiv_compact_convolution hfi.locallyIntegrable b.contDiff_normed b.hasCompactSupport_normed,
    convolution_mul]
  have hw' := hw v (fun y ↦ b.normed volume (x-y))
    (b.contDiff_normed.comp (contDiff_const.sub contDiff_id))
    (b.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft x))
    (test_kernel_support hx b hb)
  have hder (y : Plane) : fderiv ℝ (fun z ↦ b.normed volume (x-z)) y v=
      -(fderiv ℝ (b.normed volume) (x-y) v) := by
    have hbn : Differentiable ℝ (b.normed (volume : Measure Plane)) :=
      (b.contDiff_normed (μ := volume) (n := (⊤ : ℕ∞))).differentiable (by simp)
    have ht := hbn.differentiableAt.hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x)
    have he := ht.fderiv
    dsimp only [Function.comp_def,id_eq] at he
    rw [he]
    simp
  simp_rw [hder,mul_neg,integral_neg,neg_neg] at hw'
  rw [← hw']
  change (∫ y,⟪G y,v⟫*b.normed volume (x-y))=⟪∫ y,G (x-y) ∂graphSmoothingMeasure b,v⟫
  have hie : (∫ y,⟪G (x-y),v⟫ ∂graphSmoothingMeasure b)=
      ⟪∫ y,G (x-y) ∂graphSmoothingMeasure b,v⟫ := by
    simpa only [real_inner_comm] using
      integral_inner (compact_probability_average_integrable hG hGc b x) v
  rw [← hie]
  rw [graphSmoothingMeasure,
    integral_withDensity_eq_integral_toReal_smul b.continuous_normed.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (b.nonneg_normed _),smul_eq_mul]
  rw [← integral_sub_left_eq_self (fun y ↦ b.normed volume y*⟪G (x-y),v⟫)
    (volume : Measure Plane) x]
  simp only [sub_sub_cancel]
  apply integral_congr_ae
  exact Eventually.of_forall fun y ↦ mul_comm _ _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma PlaneWeakGradient.compact_hasFDerivAt {R : ℝ} {f : Plane → ℝ} {G : Plane → Plane}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hG : Continuous G) (hGc : HasCompactSupport G)
    (hw : PlaneWeakGradient (Metric.ball 0 R) f G)
    {x : Plane} (hx : x∈Metric.ball (0 : Plane) (R/2)) :
    HasFDerivAt f ((InnerProductSpace.toDual ℝ Plane) (G x)) x := by
  have hR : 0<R/2 := Metric.nonempty_ball.mp ⟨x,hx⟩
  have hGu := (InnerProductSpace.toDual ℝ Plane).isometry.uniformContinuous.comp_tendstoUniformly
    (compact_probability_average_uniform hG hGc)
  apply hasFDerivAt_of_tendstoUniformlyOnFilter (f := fun i ↦ graphSmooth (graphMollifier i) f) (g := f)
    (hGu.tendstoUniformlyOnFilter.mono_right le_top)
  · apply Filter.Eventually.prod_mk
      (graphMollifier_radius_tendsto.eventually (Iio_mem_nhds hR))
      (Metric.isOpen_ball.mem_nhds hx) |>.mono
    rintro ⟨i,y⟩ ⟨hi,hy⟩
    exact hw.smooth_hasFDerivAt hf hfc hG hGc (graphMollifier i) hi hy
  · exact Eventually.of_forall fun y ↦ compact_probability_average_uniform hf hfc |>.tendsto_at y

lemma PlaneWeakGradient.continuous_hasFDerivAt {R : ℝ} (hR : 0<R)
    {f : Plane → ℝ} {G : Plane → Plane}
    (hf : ContinuousOn f (Metric.ball 0 R)) (hG : ContinuousOn G (Metric.ball 0 R))
    (hw : PlaneWeakGradient (Metric.ball 0 R) f G)
    {x : Plane} (hx : x∈Metric.ball (0 : Plane) (R/4)) :
    HasFDerivAt f ((InnerProductSpace.toDual ℝ Plane) (G x)) x := by
  let b : ContDiffBump (0 : Plane) := ⟨R/2,3*R/4,by linarith,by linarith⟩
  have hbs : tsupport b⊆Metric.ball 0 R := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  let f' : Plane → ℝ := fun y ↦ b y*f y
  let G' : Plane → Plane := fun y ↦ b y • G y
  have hf' : Continuous f' := continuous_local_cutoff Metric.isOpen_ball hf b.continuous hbs
  have hG' : Continuous G' := continuous_local_vector_cutoff Metric.isOpen_ball hG b.continuous hbs
  have he (y : Plane) (hy : y∈Metric.ball (0 : Plane) (R/2)) : b y=1 :=
    b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
  have hw' : PlaneWeakGradient (Metric.ball 0 (R/2)) f' G' :=
    (hw.mono (Metric.ball_subset_ball (by linarith))).local_congr measurableSet_ball
      (by filter_upwards [ae_restrict_mem measurableSet_ball] with y hy; simp [f',he y hy])
      (by filter_upwards [ae_restrict_mem measurableSet_ball] with y hy; simp [G',he y hy])
  have hx' : x∈Metric.ball (0 : Plane) ((R/2)/2) := by
    have he : (R/2)/2=R/4 := by ring
    rwa [he]
  have hh := hw'.compact_hasFDerivAt hf' b.hasCompactSupport.mul_right hG'
    b.hasCompactSupport.smul_right hx'
  have hx2 : x∈Metric.ball (0 : Plane) (R/2) :=
    (Metric.ball_subset_ball (by linarith : R/4≤R/2)) hx
  have hloc : f'=ᶠ[𝓝 x] f := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx2] with y hy
    simp [f',he y hy]
  have heG : G' x=G x := by simp [G',he x hx2]
  rw [heG] at hh
  exact hh.congr_of_eventuallyEq hloc.symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem PlaneWeakGradient.holder_C1 {R L α : ℝ} (hR : 0<R) {f : Plane → ℝ} {G : Plane → Plane}
    (hw : PlaneWeakGradient (Metric.ball 0 R) f G)
    (hf : ContinuousOn f (Metric.ball 0 R)) (hG : ContinuousOn G (Metric.ball 0 R))
    (hHolder : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      dist (G x) (G y)≤L*(dist x y)^α) :
    ContDiffOn ℝ 1 f (Metric.ball 0 (R/4)) ∧
      ∀ x∈Metric.ball (0 : Plane) (R/4),∀ y∈Metric.ball (0 : Plane) (R/4),
        dist (fderiv ℝ f x) (fderiv ℝ f y)≤L*(dist x y)^α := by
  have hd : ∀ x∈Metric.ball (0 : Plane) (R/4),
      HasFDerivAt f ((InnerProductSpace.toDual ℝ Plane) (G x)) x :=
    fun x hx ↦ hw.continuous_hasFDerivAt hR hf hG hx
  have hsub : Metric.ball (0 : Plane) (R/4)⊆Metric.ball 0 R := Metric.ball_subset_ball (by linarith)
  constructor
  · rw [show (1 : WithTop ℕ∞)=0+1 by rfl,contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball]
    refine ⟨fun x hx ↦ (hd x hx).differentiableAt.differentiableWithinAt,by simp,?_⟩
    rw [contDiffOn_zero]
    apply ((InnerProductSpace.toDual ℝ Plane).continuous.comp_continuousOn (hG.mono hsub)).congr
    intro x hx
    exact (hd x hx).fderiv
  · intro x hx y hy
    rw [(hd x hx).fderiv,(hd y hy).fderiv,(InnerProductSpace.toDual ℝ Plane).isometry.dist_eq]
    exact hHolder x (hsub hx) y (hsub hy)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_PlanarWeakGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem cmc_weak_continuous_C1_oai {p : Plane → Plane} (hp : Continuous p)
    (hpb : ∀ y,‖p y‖≤1) {R α D : ℝ} (hR : 0<R) (hα : 0<α) (hα1 : α≤1) (hD : 0≤D)
    (hHolder : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*(dist x y)^α)
    {u : Plane → ℝ} {G : Plane → Plane}
    (hu : MemLp u 2 volume) (hG : MemLp G 2 volume)
    (hc : ContinuousOn u (Metric.ball 0 R))
    (hg : PlaneWeakGradient (Metric.ball 0 R) u G)
    (hd : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 R → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)))=0) :
    ∃ s K β : ℝ,0 < s ∧ s≤R/16 ∧ 0≤K ∧ 0<β ∧ β≤1 ∧
      ContDiffOn ℝ 1 u (Metric.ball 0 s) ∧
      ∀ x∈Metric.ball (0 : Plane) s,∀ y∈Metric.ball (0 : Plane) s,
        dist (fderiv ℝ u x) (fderiv ℝ u y)≤K*(dist x y)^β := by
  have hg' := hg.congr hu.coeFn_toLp hG.coeFn_toLp
  have hd' : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 R →
      (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (hG.toLp G y)))=0 := by
    intro ψ hψ hs hts
    rw [← hd ψ hψ hs hts]
    apply integral_congr_ae
    filter_upwards [hG.coeFn_toLp] with y hy
    rw [hy]
  obtain ⟨H,s,K,β,hs,hsR,hK,hβ,hβ1,hH,hHe,hHp⟩ :=
    cmc_linearized_holder_gradient hp hpb hR hα hα1 hD hHolder
      (hu.toLp u) (hG.toLp G) hg' hd'
  have hsub : Metric.ball (0 : Plane) s⊆Metric.ball 0 R := Metric.ball_subset_ball (by linarith)
  have he : H=ᵐ[volume.restrict (Metric.ball (0 : Plane) s)] G :=
    hHe.trans (ae_mono Measure.restrict_le_self hG.coeFn_toLp)
  have hw := (hg.mono hsub).local_congr measurableSet_ball EventuallyEq.rfl he
  obtain ⟨hC,hCd⟩ := hw.holder_C1 hs (hc.mono hsub) hH hHp
  exact ⟨s/4,K,β,by positivity,by linarith,hK,hβ,hβ1,hC,hCd⟩

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.cmc_weak_continuous_C1_oai := @OAI.CubicTorus.cmc_weak_continuous_C1_oai
