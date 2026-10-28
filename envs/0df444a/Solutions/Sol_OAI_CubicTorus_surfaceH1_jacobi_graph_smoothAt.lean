-- Prove2me | solution 1 for OAI.CubicTorus.surfaceH1_jacobi_graph_smoothAt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T19:32:42.195909+00:00
-- url     : https://prove2.me/submissions/726ef87c-edba-49d2-bbd8-cd96fb3972ac

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003
import Theorems.Thm_OAI_CubicTorus_cmc_linearized_holder_gradient
import Theorems.Thm_OAI_CubicTorus_forced_cmc_linearized_holder_gradient

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_NormalFirstVariation
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open scoped RealInnerProductSpace
open Set Filter MeasureTheory
open scoped Topology RealInnerProductSpace

namespace CubicTorus

lemma translate_not_mem_tsupport {Y : Type*} [Zero Y] {f : Cover → Y}
    (hs : tsupport f ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    {x : Cover} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) {n : Fin 3 → ℤ} (hn : n ≠ 0) :
    x + latticeVector n ∉ tsupport f := by
  intro h
  apply hn
  ext i
  have hi := hs h i
  simp only [PiLp.add_apply, latticeVector] at hi
  have hlo : (-1 : ℝ) < (n i : ℝ) := by linarith [(hx i).2]
  have hhi : (n i : ℝ) < 1 := by linarith [(hx i).1]
  have hνlo : (-1 : ℤ) < n i := by exact_mod_cast hlo
  have hνhi : n i < (1 : ℤ) := by exact_mod_cast hhi
  change n i = 0
  omega

lemma latticePeriodize_eventuallyEq {Y : Type*} [NormedAddCommGroup Y]
    {f : Cover → Y} (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ {x | ∀ i, 0 < x i ∧ x i < 1})
    {x : Cover} (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    latticePeriodize f =ᶠ[𝓝 x] f := by
  classical
  obtain ⟨s, hlocal⟩ := finite_lattice_support_near hc x
  have hz (n : Fin 3 → ℤ) (hn : n ≠ 0) :
      ∀ᶠ y in 𝓝 x, f (y + latticeVector n) = 0 := by
    have h := notMem_tsupport_iff_eventuallyEq.mp (translate_not_mem_tsupport hs hx hn)
    exact h.comp_tendsto (continuous_id.add continuous_const).continuousAt
  have hfin : ∀ᶠ y in 𝓝 x, ∀ n ∈ s, n ≠ 0 → f (y + latticeVector n) = 0 := by
    apply (eventually_all_finset s).mpr
    intro n _
    by_cases hn : n = 0
    · exact Eventually.of_forall fun y h ↦ False.elim (h hn)
    · exact (hz n hn).mono fun y h _ ↦ h
  filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1), hfin] with y hy hz
  unfold latticePeriodize
  rw [tsum_eq_single (0 : Fin 3 → ℤ)]
  · simp only [latticeVector_zero, add_zero]
  · intro n hn
    by_cases hs : n ∈ s
    · exact hz n hs hn
    · exact hlocal y hy n hs

end CubicTorus

namespace CubicTorus
open scoped RealInnerProductSpace

lemma compactCell_coordinates (z : CompactCell) (i : Fin 3) :
    0 ≤ (z : Cover) i ∧ (z : Cover) i ≤ 1 := by
  obtain ⟨x, hx, he⟩ := z.property
  rw [← he]
  exact ⟨hx.1 i, hx.2 i⟩

end CubicTorus

end
end
end

end OAI
end

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
open scoped ENNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] in
lemma fderiv_fderiv_apply {f : X → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x u v : X) :
    fderiv ℝ (fun y ↦ fderiv ℝ f y v) x u = fderiv ℝ (fderiv ℝ f) x u v := by
  rw [fderiv_clm_apply ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable
    (by simp) |>.differentiableAt) (differentiableAt_const v)]
  simp

end CubicTorus

end
end

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

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma integral_mul_eq_restrict_of_tsupport {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] {μ : Measure X} {K : Set X} (hK : MeasurableSet K)
    (f q : X → ℝ) (hq : tsupport q ⊆ K) :
    (∫ x, f x * q x ∂μ) = ∫ x in K, f x * q x ∂μ := by
  rw [← integral_indicator hK]
  apply integral_congr_ae
  exact Eventually.of_forall fun x ↦ by
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx]
      change f x * q x = 0
      rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hq h)), mul_zero]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVGraphEnergy
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.graphSmoothingMeasure_probability _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalPlaneCoordinates_graph {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (y : Plane) : normalPlaneCoordinates n (normalGraph n g y) = y := by
  simp [normalGraph, map_add, map_smul, normalPlaneCoordinates_embedding,
    normalPlaneCoordinates_normal hn]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_BVTorusGraphFlux
attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_gradient_norm (g : Plane → ℝ) (y : Plane) :
    ‖gradient g y‖ = ‖fderiv ℝ g y‖ := by
  exact (InnerProductSpace.toDual ℝ Plane).symm.norm_map _

lemma graphAreaVector_norm_sq {n : Cover} (hn : ‖n‖ = 1) (g : Plane → ℝ) (y : Plane) :
    ‖graphAreaVector n g y‖ ^ 2 = 1 + ‖fderiv ℝ g y‖ ^ 2 := by
  rw [graphAreaVector, norm_sub_sq_real, hn, one_pow,
    normalPlaneEmbedding_norm, normalPlaneEmbedding_inner hn, plane_gradient_norm]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma lipschitz_probability_average_integrable {ν : Measure Plane} [IsProbabilityMeasure ν]
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {δ : ℝ} (_hδ : 0 ≤ δ) (hb : ∀ᵐ y ∂ν, ‖y‖ ≤ δ) (x : Plane) :
    Integrable (fun y ↦ f (x-y)) ν := by
  apply (integrable_const (|f x|+(K : ℝ)*δ)).mono'
    (hf.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  filter_upwards [hb] with y hy
  have hh := hf.dist_le_mul (x-y) x
  rw [Real.dist_eq, dist_eq_norm, sub_sub_cancel_left, norm_neg] at hh
  rw [Real.norm_eq_abs]
  have ht := abs_add_le (f (x-y)-f x) (f x)
  rw [sub_add_cancel] at ht
  exact ht.trans (by nlinarith [mul_le_mul_of_nonneg_left hy K.coe_nonneg])

lemma lipschitz_probability_average_error {ν : Measure Plane} [IsProbabilityMeasure ν]
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {δ : ℝ} (hδ : 0 ≤ δ) (hb : ∀ᵐ y ∂ν, ‖y‖ ≤ δ) (x : Plane) :
    |(∫ y, f (x-y) ∂ν)-f x| ≤ (K : ℝ)*δ := by
  have hi := lipschitz_probability_average_integrable hf hδ hb x
  have he : f x = ∫ _y : Plane, f x ∂ν := by simp
  rw [he, ← integral_sub hi (integrable_const _)]
  rw [← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  change (∫ y, ‖f (x-y)-f x‖ ∂ν) ≤ _
  calc
    _ ≤ ∫ _y : Plane, (K : ℝ)*δ ∂ν := by
      apply integral_mono_ae (hi.sub (integrable_const _)).norm (integrable_const _)
      filter_upwards [hb] with y hy
      have hh := hf.dist_le_mul (x-y) x
      rw [Real.dist_eq, dist_eq_norm, sub_sub_cancel_left, norm_neg] at hh
      rw [Real.norm_eq_abs]
      exact hh.trans (mul_le_mul_of_nonneg_left hy K.coe_nonneg)
    _ = _ := by simp

lemma lipschitz_probability_average_hasFDerivAt {ν : Measure Plane} [IsProbabilityMeasure ν]
    (hν : ν ≪ (volume : Measure Plane)) {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {δ : ℝ} (hδ : 0 ≤ δ) (hb : ∀ᵐ y ∂ν, ‖y‖ ≤ δ) (x : Plane) :
    Integrable (fun y ↦ fderiv ℝ f (x-y)) ν ∧
      HasFDerivAt (fun z ↦ ∫ y, f (z-y) ∂ν) (∫ y, fderiv ℝ f (x-y) ∂ν) x := by
  refine hasFDerivAt_integral_of_dominated_loc_of_lip
    (F := fun z y : Plane ↦ f (z-y)) (F' := fun y ↦ fderiv ℝ f (x-y))
    (x₀ := x) (s := univ) (bound := fun _ ↦ (K : ℝ)) (Filter.univ_mem)
    (Eventually.of_forall fun z ↦ (hf.continuous.comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (lipschitz_probability_average_integrable hf hδ hb x)
    ((measurable_fderiv ℝ f).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    ?_ (integrable_const _) ?_
  · exact Eventually.of_forall fun y ↦ by
      have hl : LipschitzWith K (fun z : Plane ↦ f (z-y)) := by
        apply LipschitzWith.of_dist_le_mul
        intro z w
        simpa only [dist_sub_right] using hf.dist_le_mul (z-y) (w-y)
      simpa only [Real.nnabs_of_nonneg K.coe_nonneg, Real.toNNReal_coe] using hl.lipschitzOnWith
  · have hd : ∀ᵐ y ∂ν, DifferentiableAt ℝ f (x-y) := hν.ae_le
      ((volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae hf.ae_differentiableAt)
    filter_upwards [hd] with y hy
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using
      hy.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const y)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Convolution
namespace CubicTorus

lemma graphSmoothingMeasure_ac (b : ContDiffBump (0 : Plane)) :
    graphSmoothingMeasure b ≪ volume := withDensity_absolutelyContinuous _ _

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

lemma graphSmooth_contDiff (b : ContDiffBump (0 : Plane)) {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) : ContDiff ℝ (⊤ : ℕ∞) (graphSmooth b f) := by
  rw [graphSmooth_eq_convolution]
  exact b.hasCompactSupport_normed.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) b.contDiff_normed hf.continuous.locallyIntegrable

lemma graphSmooth_error (b : ContDiffBump (0 : Plane)) {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (x : Plane) :
    |graphSmooth b f x-f x| ≤ (K : ℝ)*b.rOut :=
  lipschitz_probability_average_error hf b.rOut_pos.le (graphSmoothingMeasure_radius b) x

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_BVGraphRescaling
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

lemma graphSmooth_integrable (b : ContDiffBump (0 : Plane))
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (x : Plane) :
    Integrable (fun y ↦ f (x-y)) (graphSmoothingMeasure b) :=
  lipschitz_probability_average_integrable hf b.rOut_pos.le (graphSmoothingMeasure_radius b) x

lemma graphSmooth_lipschitz (b : ContDiffBump (0 : Plane))
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith K (graphSmooth b f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x z
  rw [Real.dist_eq,graphSmooth,graphSmooth,← integral_sub
    (graphSmooth_integrable b hf x) (graphSmooth_integrable b hf z)]
  calc
    _ ≤ ∫ y, |f (x-y)-f (z-y)| ∂graphSmoothingMeasure b := abs_integral_le_integral_abs
    _ ≤ ∫ _y : Plane, (K : ℝ)*dist x z ∂graphSmoothingMeasure b := by
      apply integral_mono ((graphSmooth_integrable b hf x).sub (graphSmooth_integrable b hf z)).norm
        (integrable_const _)
      intro y
      change ‖f (x-y)-f (z-y)‖ ≤ (K : ℝ)*dist x z
      simpa only [Real.norm_eq_abs,← Real.dist_eq,dist_sub_right] using hf.dist_le_mul (x-y) (z-y)
    _ = _ := by simp

lemma graphSmooth_affine (b : ContDiffBump (0 : Plane))
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (m e : ℝ) (x : Plane) :
    m+e*graphSmooth b f x = ∫ y, (m+e*f (x-y)) ∂graphSmoothingMeasure b := by
  rw [integral_add (integrable_const _) ((graphSmooth_integrable b hf x).const_mul e),
    integral_const_mul]
  simp [graphSmooth]

lemma graphSmooth_affine_abs_le (b : ContDiffBump (0 : Plane))
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (m e H : ℝ)
    (hH : ∀ y, |m+e*f y| ≤ H) (x : Plane) : |m+e*graphSmooth b f x| ≤ H := by
  rw [graphSmooth_affine b hf]
  calc
    _ ≤ ∫ y, |m+e*f (x-y)| ∂graphSmoothingMeasure b := abs_integral_le_integral_abs
    _ ≤ ∫ _y : Plane, H ∂graphSmoothingMeasure b := by
      apply integral_mono ((integrable_const m).add ((graphSmooth_integrable b hf x).const_mul e)).norm
        (integrable_const _)
      exact fun y ↦ hH _
    _ = _ := by simp

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

lemma graphSmooth_tendsto {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) (y : Plane) :
    Tendsto (fun i ↦ graphSmooth (graphMollifier i) g y) atTop (𝓝 (g y)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ norm_nonneg _) (fun i ↦ ?_)
    (by simpa only [mul_zero] using graphMollifier_radius_tendsto.const_mul (K:ℝ))
  exact graphSmooth_error _ hg y

theorem graphSmooth_fderiv_tendsto {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {y : Plane} (hc : ContinuousAt (fderiv ℝ g) y) :
    Tendsto (fun i ↦ fderiv ℝ (graphSmooth (graphMollifier i) g) y)
      atTop (𝓝 (fderiv ℝ g y)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp hc (ε/2) (by positivity)
  filter_upwards [graphMollifier_radius_tendsto.eventually (Iio_mem_nhds hδ)] with i hi
  have ha := lipschitz_probability_average_hasFDerivAt (graphSmoothingMeasure_ac (graphMollifier i))
    hg (graphMollifier i).rOut_pos.le (graphSmoothingMeasure_radius (graphMollifier i)) y
  change dist (fderiv ℝ (fun z ↦ ∫ w, g (z-w) ∂graphSmoothingMeasure (graphMollifier i)) y) _ < ε
  rw [ha.2.fderiv,dist_eq_norm]
  have he : (∫ _w : Plane, fderiv ℝ g y ∂graphSmoothingMeasure (graphMollifier i)) = fderiv ℝ g y := by simp
  rw [← he,← integral_sub ha.1 (integrable_const _)]
  apply lt_of_le_of_lt (norm_integral_le_integral_norm _) ?_
  have hb : (∫ w, ‖fderiv ℝ g (y-w)-fderiv ℝ g y‖ ∂graphSmoothingMeasure (graphMollifier i)) ≤ ε/2 := by
    calc
      _ ≤ ∫ _w : Plane, ε/2 ∂graphSmoothingMeasure (graphMollifier i) := by
        apply integral_mono_ae (ha.1.sub (integrable_const _)).norm (integrable_const _)
        filter_upwards [graphSmoothingMeasure_radius (graphMollifier i)] with w hw
        have hh : dist (y-w) y < δ := by simpa only [dist_eq_norm,sub_sub_cancel_left,norm_neg] using hw.trans_lt hi
        simpa only [dist_eq_norm,Pi.sub_apply] using (hclose hh).le
      _ = _ := by simp
  exact hb.trans_lt (by linarith)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphUnitNormalExtension_graph (a : Cover) {n : Cover} (hn : ‖n‖ = 1)
    (g f : Plane → ℝ) (y : Plane) :
    graphUnitNormalExtension a n f (a+normalGraph n g y) = graphSlopeNormal n (gradient f y) := by
  unfold graphUnitNormalExtension
  rw [add_sub_cancel_left,normalGraph, map_add,map_smul,
    normalPlaneCoordinates_embedding,normalPlaneCoordinates_normal hn,smul_zero,add_zero]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_MinimalGraphDensity
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

lemma graphAreaVector_norm_sqrt {n : Cover} (hn : ‖n‖=1) (g : Plane → ℝ) (y : Plane) :
    ‖graphAreaVector n g y‖ = Real.sqrt (1+‖gradient g y‖^2) := by
  rw [plane_gradient_norm,← graphAreaVector_norm_sq hn g y,Real.sqrt_sq (norm_nonneg _)]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma normalPlaneEmbedding_inner_coordinates {n : Cover} (hn : ‖n‖=1) (y : Plane) (x : Cover) :
    ⟪normalPlaneEmbedding n y,x⟫ = ⟪y,normalPlaneCoordinates n x⟫ := by
  conv_lhs => rhs; rw [← normalPlaneCoordinates_reconstruct hn x]
  have hz : ⟪normalPlaneEmbedding n y,n⟫=0 :=
    (real_inner_comm _ _).trans (normalPlaneEmbedding_inner hn y)
  rw [inner_add_right,inner_smul_right,hz,mul_zero,add_zero]
  exact (normalPlaneLinearIsometry n).inner_map_map y (normalPlaneCoordinates n x)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_TorusC1Boundary
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

lemma cmcWeight_ge_one (p : Plane) : 1 ≤ cmcWeight p := by
  have hp := cmcWeight_sq p
  have hh := cmcWeight_pos p
  nlinarith [sq_nonneg ‖p‖]
lemma cmcWeight_le_two {p : Plane} (hp : ‖p‖≤1) : cmcWeight p≤2 := by
  have hh := cmcWeight_sq p
  nlinarith [sq_nonneg (cmcWeight p),norm_nonneg p]

lemma cmcWeight_contDiff : ContDiff ℝ (⊤ : ℕ∞) cmcWeight := by
  apply (contDiff_const.add (contDiff_id.norm_sq ℝ)).sqrt
  intro p
  positivity

lemma cmcFlux_contDiff : ContDiff ℝ (⊤ : ℕ∞) cmcFlux :=
  (cmcWeight_contDiff.inv (fun p ↦ (cmcWeight_pos p).ne')).smul contDiff_id

lemma cmcWeight_hasFDerivAt (p : Plane) :
    HasFDerivAt cmcWeight ((cmcWeight p)⁻¹ • innerSL ℝ p) p := by
  have h := ((hasStrictFDerivAt_norm_sq p).hasFDerivAt.const_add 1).sqrt
    (by positivity : (1 : ℝ)+‖p‖^2≠0)
  change HasFDerivAt cmcWeight ((1/(2*cmcWeight p)) • (2 • innerSL ℝ p)) p at h
  have he : (1/(2*cmcWeight p)) • (2 • innerSL ℝ p) =
      (cmcWeight p)⁻¹ • innerSL ℝ p := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [smul_apply,innerSL_apply_apply,smul_eq_mul,two_smul,add_apply]
    field_simp
    ring
  exact he ▸ h

lemma cmcFlux_hasFDerivAt (p : Plane) : HasFDerivAt cmcFlux (cmcJacobian p) p := by
  have h := ((hasDerivAt_inv (cmcWeight_pos p).ne').comp_hasFDerivAt p (cmcWeight_hasFDerivAt p)).smul (hasFDerivAt_id p)
  have he : (cmcWeight p)⁻¹ • ContinuousLinearMap.id ℝ Plane +
      ((-((cmcWeight p)^2)⁻¹) • ((cmcWeight p)⁻¹ • innerSL ℝ p)).smulRight p =
      cmcJacobian p := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [cmcJacobian,add_apply,sub_apply,smul_apply,ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,smul_eq_mul,smul_smul]
    have hc : -((cmcWeight p)^2)⁻¹*(cmcWeight p)⁻¹*⟪p,v⟫ =
        -(((cmcWeight p)^3)⁻¹*⟪p,v⟫) := by field_simp
    rw [hc,neg_smul,sub_eq_add_neg]
  exact he ▸ h

lemma cmcJacobian_apply (p v : Plane) :
    cmcJacobian p v=(cmcWeight p)⁻¹ • v -
      (((cmcWeight p)^3)⁻¹*⟪p,v⟫) • p := by
  simp only [cmcJacobian,sub_apply,smul_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,smul_smul]

lemma cmcJacobian_self (p v : Plane) :
    ⟪v,cmcJacobian p v⟫=
      ((cmcWeight p)^2*‖v‖^2-⟪p,v⟫^2)/(cmcWeight p)^3 := by
  rw [cmcJacobian_apply,inner_sub_right,inner_smul_right,inner_smul_right,
    real_inner_self_eq_norm_sq,real_inner_comm v p]
  field_simp

lemma cmcJacobian_coercive {p : Plane} (hp : ‖p‖≤1) (v : Plane) :
    (1/8)*‖v‖^2≤⟪v,cmcJacobian p v⟫ := by
  have hs := cmcWeight_pos p
  have hsq := cmcWeight_sq p
  have hcs := real_inner_mul_inner_self_le p v
  simp only [real_inner_self_eq_norm_sq] at hcs
  have h8 : (cmcWeight p)^3≤8 := by
    have hh := cmcWeight_le_two hp
    nlinarith [sq_nonneg (cmcWeight p-2)]
  rw [cmcJacobian_self,le_div_iff₀ (by positivity : 0<(cmcWeight p)^3)]
  have hh := mul_le_mul_of_nonneg_right h8 (sq_nonneg ‖v‖)
  nlinarith [sq_nonneg ⟪p,v⟫]

lemma cmcJacobian_norm_le {p : Plane} (hp : ‖p‖≤1) (v : Plane) :
    ‖cmcJacobian p v‖≤2*‖v‖ := by
  have hs := cmcWeight_ge_one p
  have hs0 := cmcWeight_pos p
  have hsi : (cmcWeight p)⁻¹≤1 := inv_le_one₀ hs0 |>.mpr hs
  have hs3 : ((cmcWeight p)^3)⁻¹≤1 := by
    apply (inv_le_one₀ (by positivity : 0<(cmcWeight p)^3)).mpr
    nlinarith [sq_nonneg (cmcWeight p-1)]
  rw [cmcJacobian_apply]
  calc
    _ ≤ ‖(cmcWeight p)⁻¹ • v‖ + ‖(((cmcWeight p)^3)⁻¹*⟪p,v⟫) • p‖ := norm_sub_le _ _
    _ = (cmcWeight p)⁻¹*‖v‖+((cmcWeight p)^3)⁻¹*|⟪p,v⟫| *‖p‖ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (inv_nonneg.mpr hs0.le),
        abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hs0.le 3))]
    _ ≤ ‖v‖+‖v‖ := by
      apply add_le_add
      · exact mul_le_of_le_one_left (norm_nonneg _) hsi
      · apply (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) hs3) (norm_nonneg _)).trans
        apply (mul_le_mul_of_nonneg_right (abs_real_inner_le_norm p v) (norm_nonneg _)).trans
        exact (mul_le_of_le_one_right (mul_nonneg (norm_nonneg p) (norm_nonneg v)) hp).trans
          (mul_le_of_le_one_left (norm_nonneg v) hp)
    _ = _ := by ring

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_LinearCMCEquation
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

lemma exists_plane_test_cutoff {R : ℝ} (hR : 0<R) {ψ : Plane → ℝ}
    (hs : tsupport ψ⊆Metric.ball 0 R) :
    ∃ b : ContDiffBump (0 : Plane), b.rOut<R ∧ ∀ y, b y*ψ y=ψ y := by
  obtain ⟨s,hsR,hsb⟩ := exists_lt_subset_ball isClosed_closure hs
  let t := max (R/2) s
  have ht : 0<t := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have htR : t<R := max_lt (by linarith) hsR
  let b : ContDiffBump (0 : Plane) := ⟨t,(t+R)/2,ht,by linarith⟩
  refine ⟨b,by change (t+R)/2<R; linarith,fun y ↦ ?_⟩
  by_cases hy : ψ y=0
  · rw [hy,mul_zero]
  · have hym : y∈Metric.closedBall (0 : Plane) b.rIn :=
      Metric.ball_subset_closedBall ((Metric.ball_subset_ball (le_max_right _ _))
        (hsb (subset_tsupport ψ hy)))
    rw [b.one_of_mem_closedBall hym,one_mul]

theorem exists_C1_test_approximants {R : ℝ} (hR : 0<R) {ψ : Plane → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆Metric.ball 0 R) :
    ∃ (f : ℕ → Plane → ℝ) (K : Set Plane) (M : ℝ), IsCompact K ∧
      K⊆Metric.ball 0 R ∧ 0≤M ∧
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i) ∧ tsupport (f i)⊆K) ∧
      (∀ i y, ‖f i y‖≤M ∧ ‖fderiv ℝ (f i) y‖≤M) ∧
      (∀ y, Tendsto (fun i ↦ f i y) atTop (𝓝 (ψ y))) ∧
      (∀ y, Tendsto (fun i ↦ fderiv ℝ (f i) y) atTop (𝓝 (fderiv ℝ ψ y))) := by
  obtain ⟨b,hbR,hbψ⟩ := exists_plane_test_cutoff hR hs
  obtain ⟨L,hL⟩ := hψ.lipschitzWith_of_hasCompactSupport hc (by simp)
  have hbc : ContDiff ℝ (⊤ : ℕ∞) b := b.contDiff
  obtain ⟨Lb,hLb⟩ := hbc.lipschitzWith_of_hasCompactSupport b.hasCompactSupport (by simp)
  obtain ⟨C,hC⟩ := hψ.continuous.norm.bddAbove_range_of_hasCompactSupport hc.norm
  have hCb (y : Plane) : ‖ψ y‖≤C := hC (mem_range_self y)
  have hC0 : 0≤C := (norm_nonneg (ψ 0)).trans (hCb 0)
  let f (i : ℕ) : Plane → ℝ := fun y ↦ b y*graphSmooth (graphMollifier i) ψ y
  have hfs (i : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (f i) := b.contDiff.mul (graphSmooth_contDiff _ hL)
  have hsm (i : ℕ) (y : Plane) : ‖graphSmooth (graphMollifier i) ψ y‖≤C := by
    simpa only [zero_add,one_mul,Real.norm_eq_abs] using
      graphSmooth_affine_abs_le (graphMollifier i) hL 0 1 C (by simpa only [zero_add,one_mul,Real.norm_eq_abs] using hCb) y
  have hb1 (y : Plane) : ‖b y‖≤1 := by simpa only [Real.norm_eq_abs,abs_of_nonneg b.nonneg] using b.le_one (x := y)
  have hdf (i : ℕ) (y : Plane) : fderiv ℝ (f i) y =
      b y • fderiv ℝ (graphSmooth (graphMollifier i) ψ) y +
      graphSmooth (graphMollifier i) ψ y • fderiv ℝ b y := by
    exact fderiv_fun_mul (hbc.differentiable (by simp)).differentiableAt
      ((graphSmooth_contDiff _ hL).differentiable (by simp)).differentiableAt
  refine ⟨f,tsupport b,C+(L:ℝ)+C*(Lb:ℝ),b.hasCompactSupport,?_,by positivity,
    fun i ↦ ⟨hfs i,tsupport_mul_subset_left⟩,?_,?_,?_⟩
  · rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball hbR
  · intro i y
    constructor
    · have hh : ‖f i y‖≤C := by
        change ‖b y*graphSmooth (graphMollifier i) ψ y‖≤C
        rw [norm_mul]
        exact (mul_le_mul (hb1 y) (hsm i y) (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
      nlinarith [Lb.coe_nonneg,L.coe_nonneg]
    · rw [hdf]
      calc
        _ ≤ ‖b y • fderiv ℝ (graphSmooth (graphMollifier i) ψ) y‖+
            ‖graphSmooth (graphMollifier i) ψ y • fderiv ℝ b y‖ := norm_add_le _ _
        _ ≤ (L:ℝ)+C*(Lb:ℝ) := by
          simp only [norm_smul]
          apply add_le_add
          · exact (mul_le_mul (hb1 y) (norm_fderiv_le_of_lipschitz ℝ (graphSmooth_lipschitz _ hL))
              (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
          · exact mul_le_mul (hsm i y) (norm_fderiv_le_of_lipschitz ℝ hLb) (norm_nonneg _) hC0
        _ ≤ _ := by linarith
  · intro y
    simpa only [hbψ y] using (graphSmooth_tendsto hL y).const_mul (b y)
  · intro y
    have he : (fun y ↦ b y*ψ y)=ψ := funext hbψ
    have hdp : fderiv ℝ ψ y=b y • fderiv ℝ ψ y+ψ y • fderiv ℝ b y := by
      conv_lhs => rw [← he]
      exact fderiv_fun_mul (hbc.differentiable (by simp)).differentiableAt
        (hψ.differentiable (by simp)).differentiableAt
    rw [hdp]
    simpa only [hdf] using
      ((graphSmooth_fderiv_tendsto hL (hψ.continuous_fderiv (by simp)).continuousAt).const_smul (b y)).add
        ((graphSmooth_tendsto hL y).smul_const (fderiv ℝ b y))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma measurable_differential_apply {F : Plane → Plane} (hF : Measurable F) (ψ : Plane → ℝ) :
    Measurable (fun y ↦ fderiv ℝ ψ y (F y)) :=
  (continuous_fst.clm_apply continuous_snd).measurable.comp
    ((measurable_fderiv ℝ ψ).prodMk hF)

theorem weak_flux_C1_test {R : ℝ} (hR : 0<R) {F : Plane → Plane}
    (hF : Measurable F) {N : ℝ} (hN : ∀ y, ‖F y‖≤N) (A : ℝ)
    (hw : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ⊆Metric.ball 0 R → (∫ y, fderiv ℝ φ y (F y))=A*(∫ y, φ y))
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆Metric.ball 0 R) :
    (∫ y, fderiv ℝ ψ y (F y))=A*(∫ y, ψ y) := by
  obtain ⟨f,K,M,hK,hKR,hM,hf,hb,ht,hdt⟩ := exists_C1_test_approximants hR hψ hc hs
  have hN0 : 0≤N := (norm_nonneg (F 0)).trans (hN 0)
  let B : Plane → ℝ := K.indicator (fun _ ↦ M*N)
  let C : Plane → ℝ := K.indicator (fun _ ↦ M)
  have hBi : Integrable B := (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  have hCi : Integrable C := (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  have htd : Tendsto (fun i ↦ ∫ y, fderiv ℝ (f i) y (F y)) atTop
      (𝓝 (∫ y, fderiv ℝ ψ y (F y))) := by
    apply tendsto_integral_of_dominated_convergence B
      (fun _ ↦ (measurable_differential_apply hF _).aestronglyMeasurable) hBi
    · intro i
      filter_upwards [] with y
      by_cases hy : y∈K
      · rw [show B y=M*N from indicator_of_mem hy _]
        exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul (hb i y).2 (hN y) (norm_nonneg _) hM)
      · have hz := fderiv_of_notMem_tsupport ℝ (fun hy' ↦ hy ((hf i).2 hy'))
        rw [hz,zero_apply,norm_zero,show B y=0 from indicator_of_notMem hy _]
    · apply Eventually.of_forall
      intro y
      exact ((show Continuous (fun L : Plane →L[ℝ] ℝ ↦ L (F y)) from
        continuous_id.clm_apply continuous_const).tendsto _).comp (hdt y)
  have htv : Tendsto (fun i ↦ ∫ y, f i y) atTop (𝓝 (∫ y, ψ y)) := by
    apply tendsto_integral_of_dominated_convergence C
      (fun i ↦ (hf i).1.continuous.aestronglyMeasurable) hCi
    · intro i
      filter_upwards [] with y
      by_cases hy : y∈K
      · rw [show C y=M from indicator_of_mem hy _]
        exact (hb i y).1
      · have hz : f i y=0 := image_eq_zero_of_notMem_tsupport (fun hy' ↦ hy ((hf i).2 hy'))
        rw [hz,norm_zero,show C y=0 from indicator_of_notMem hy _]
    · exact Eventually.of_forall ht
  have he (i : ℕ) : (∫ y, fderiv ℝ (f i) y (F y))=A*(∫ y, f i y) :=
    hw (f i) (hf i).1 (hK.of_isClosed_subset isClosed_closure (hf i).2) ((hf i).2.trans hKR)
  exact tendsto_nhds_unique htd (by simpa only [he] using htv.const_mul A)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma integrable_differential_apply_of_bounded {F : Plane → Plane} (hF : Measurable F)
    {N : ℝ} (hN : ∀ y, ‖F y‖≤N) {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) : Integrable (fun y ↦ fderiv ℝ ψ y (F y)) := by
  obtain ⟨L,hL⟩ := hψ.lipschitzWith_of_hasCompactSupport hc (by simp)
  have hi := (integrableOn_const (μ := (volume : Measure Plane)) (C := (L:ℝ)*N) hc.measure_lt_top.ne).integrable_indicator
    isClosed_closure.measurableSet
  apply hi.mono' (measurable_differential_apply hF ψ).aestronglyMeasurable
  filter_upwards [] with y
  by_cases hy : y∈tsupport ψ
  · rw [indicator_of_mem hy]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hL) (hN y) (norm_nonneg _) L.coe_nonneg)
  · rw [indicator_of_notMem hy,fderiv_of_notMem_tsupport ℝ hy,zero_apply,norm_zero]

lemma translated_test_support {R r : ℝ} {ψ : Plane → ℝ} {a : Plane}
    (hs : tsupport ψ⊆Metric.ball 0 r) (ha : r+‖a‖≤R) :
    tsupport (fun y ↦ ψ (y-a))⊆Metric.ball 0 R := by
  intro y hy
  have hys := hs (tsupport_comp_subset_preimage ψ (by fun_prop : Continuous (fun y : Plane ↦ y-a)) hy)
  have hh : ‖y-a‖ < r := by simpa only [Metric.mem_ball,dist_zero_right] using hys
  rw [Metric.mem_ball,dist_zero_right]
  calc
    ‖y‖ = ‖(y-a)+a‖ := by rw [sub_add_cancel]
    _ ≤ ‖y-a‖+‖a‖ := norm_add_le _ _
    _ < r+‖a‖ := by linarith
    _ ≤ R := ha

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma local_C1_cutoff_product {U : Set Plane} (hU : IsOpen U)
    {η w : Plane → ℝ} (hη : ContDiff ℝ 1 η) (hw : ContDiffOn ℝ 1 w U)
    (hs : tsupport η⊆U) : ContDiff ℝ 1 (fun y ↦ η y^2*w y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y∈tsupport η
  · exact (hη.contDiffAt.pow 2).mul ((hw y (hs hy)).contDiffAt (hU.mem_nhds (hs hy)))
  · apply (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp [hz]

lemma energyTest_tsupport {η w : Plane → ℝ} : tsupport (fun y ↦ η y^2*w y)⊆tsupport η := by
  apply closure_mono
  intro y hy
  contrapose! hy
  simp only [Function.mem_support,not_not] at hy ⊢
  simp [hy]

lemma integrable_bounded_compact {f : Plane → ℝ} (hf : Measurable f)
    {K : Set Plane} (hK : IsCompact K) {M : ℝ} (hb : ∀ y, ‖f y‖≤M)
    (hz : ∀ y, y∉K → f y=0) : Integrable f := by
  have hi : Integrable (K.indicator (fun _ : Plane ↦ M)) :=
    (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  apply hi.mono' hf.aestronglyMeasurable
  filter_upwards [] with y
  by_cases hy : y∈K
  · rw [indicator_of_mem hy]; exact hb y
  · rw [indicator_of_notMem hy,hz y hy,norm_zero]

lemma translated_difference_contDiffOn {g : Plane → ℝ} {R r : ℝ} {a : Plane}
    (hg : ContDiffOn ℝ 1 g (Metric.ball 0 R)) (ha : r+‖a‖≤R) :
    ContDiffOn ℝ 1 (fun y ↦ g (y+a)-g y) (Metric.ball 0 r) := by
  apply (hg.comp (contDiff_id.add contDiff_const).contDiffOn ?_).sub
    (hg.mono (Metric.ball_subset_ball (by linarith [norm_nonneg a])))
  intro y hy
  rw [Metric.mem_ball,dist_zero_right]
  have hy' : ‖y‖ < r := by simpa only [Metric.mem_ball,dist_zero_right] using hy
  change ‖y+a‖<R
  exact (norm_add_le _ _).trans_lt (by linarith)

lemma translated_difference_fderiv {g : Plane → ℝ} {R r : ℝ} {a y : Plane}
    (hg : ContDiffOn ℝ 1 g (Metric.ball 0 R)) (ha : r+‖a‖≤R)
    (hy : y∈Metric.ball 0 r) (v : Plane) :
    fderiv ℝ (fun y ↦ g (y+a)-g y) y v=⟪gradient g (y+a)-gradient g y,v⟫ := by
  have hy0 : y∈Metric.ball (0 : Plane) R := Metric.ball_subset_ball (by linarith [norm_nonneg a]) hy
  have hya : y+a∈Metric.ball (0 : Plane) R := by
    rw [Metric.mem_ball,dist_zero_right]
    have hh : ‖y‖ < r := by simpa only [Metric.mem_ball,dist_zero_right] using hy
    exact (norm_add_le _ _).trans_lt (by linarith)
  have hd := ((hg y hy0).contDiffAt (Metric.isOpen_ball.mem_nhds hy0)).differentiableAt (by simp)
  have hda := ((hg (y+a) hya).contDiffAt (Metric.isOpen_ball.mem_nhds hya)).differentiableAt (by simp)
  have hdc : DifferentiableAt ℝ (fun y ↦ g (y+a)) y :=
    hda.comp y (differentiableAt_id.add_const a)
  change fderiv ℝ ((fun y ↦ g (y+a))-g) y v=_
  rw [fderiv_sub hdc hd,fderiv_comp_add_right,
    sub_apply,inner_sub_left,inner_gradient_left,inner_gradient_left]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cmc_linear_energy_absorption {p : Plane} (hp : ‖p‖≤1)
    (q D : Plane) (a w : ℝ) (L : Plane →L[ℝ] ℝ) :
    (1/16)*a^2*‖q‖^2-256*w^2*‖L‖^2-16*a^2*‖D‖^2 ≤
      a^2*⟪q,cmcJacobian p q-D⟫+2*a*w*L (cmcJacobian p q-D) := by
  let F := cmcJacobian p q-D
  have hc : (1/8)*‖q‖^2-‖q‖*‖D‖≤⟪q,F⟫ := by
    dsimp only [F]
    rw [inner_sub_right]
    linarith [cmcJacobian_coercive hp q,real_inner_le_norm q D]
  have hF : ‖F‖≤2*‖q‖+‖D‖ := (norm_sub_le _ _).trans
    (add_le_add (cmcJacobian_norm_le hp q) le_rfl)
  have hL : |L F|≤‖L‖*(2*‖q‖+‖D‖) :=
    (ContinuousLinearMap.le_opNorm L F).trans (mul_le_mul_of_nonneg_left hF (norm_nonneg L))
  have he : |2*a*w*L F|≤2*|a| *|w| *‖L‖*(2*‖q‖+‖D‖) := by
    rw [abs_mul,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    have hh := mul_le_mul_of_nonneg_left hL (show 0≤2*|a| *|w| by positivity)
    nlinarith
  have hn := (neg_le_neg he).trans (neg_abs_le (2*a*w*L F))
  have hca := mul_le_mul_of_nonneg_left hc (sq_nonneg a)
  have hs₁ := sq_nonneg (|a| *‖q‖/4-4*|a| *‖D‖)
  have hs₂ := sq_nonneg (|a| *‖q‖/4-16*|w| *‖L‖)
  have hs₃ := sq_nonneg (|a| *‖D‖-|w| *‖L‖)
  simp only [sub_sq,mul_pow,div_pow,sq_abs] at hs₁ hs₂ hs₃
  ring_nf at hs₁
  simp only [sq_abs] at hs₁
  change (1/16)*a^2*‖q‖^2-256*w^2*‖L‖^2-16*a^2*‖D‖^2 ≤ a^2*⟪q,F⟫+2*a*w*L F
  nlinarith [mul_nonneg (sq_nonneg a) (sq_nonneg ‖D‖),mul_nonneg (sq_nonneg w) (sq_nonneg ‖L‖)]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma gradient_difference_norm_le {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (y a : Plane) :
    ‖gradient g (y+a)-gradient g y‖≤2*(K:ℝ) := by
  have hb (x : Plane) : ‖gradient g x‖≤(K:ℝ) := by
    rw [plane_gradient_norm]; exact norm_fderiv_le_of_lipschitz ℝ hg
  exact (norm_sub_le _ _).trans (by linarith [hb (y+a),hb y])

lemma height_difference_norm_le {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (y a : Plane) : ‖g (y+a)-g y‖≤(K:ℝ)*‖a‖ := by
  simpa only [dist_eq_norm,add_sub_cancel_left] using hg.dist_le_mul (y+a) y

lemma measurable_plane_gradient (g : Plane → ℝ) : Measurable (gradient g) :=
  (InnerProductSpace.toDual ℝ Plane).symm.continuous.measurable.comp (measurable_fderiv ℝ g)

lemma cmc_cutoff_energies_integrable {g η : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) (a : Plane) :
    Integrable (fun y ↦ η y^2*‖gradient g (y+a)-gradient g y‖^2) ∧
    Integrable (fun y ↦ (g (y+a)-g y)^2*‖fderiv ℝ η y‖^2) := by
  obtain ⟨M,hMb⟩ := hη.continuous.norm.bddAbove_range_of_hasCompactSupport hc.norm
  have hM (y : Plane) : ‖η y‖≤M := hMb (mem_range_self y)
  have hM0 : 0≤M := (norm_nonneg (η 0)).trans (hM 0)
  obtain ⟨D,hD⟩ := hη.lipschitzWith_of_hasCompactSupport hc (by simp)
  have hDη (y : Plane) := norm_fderiv_le_of_lipschitz ℝ hD (x₀ := y)
  have hgrad := measurable_plane_gradient g
  have hgrad' : Measurable (fun y ↦ gradient g (y+a)-gradient g y) :=
    (hgrad.comp (measurable_id.add_const a)).sub hgrad
  constructor
  · apply integrable_bounded_compact (hη.continuous.measurable.pow_const 2 |>.mul (hgrad'.norm.pow_const 2)) hc
      (M := M^2*(2*(K:ℝ))^2)
    · intro y
      dsimp only [Pi.mul_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      have hh : η y^2≤M^2 := by
        simpa only [Real.norm_eq_abs,sq_abs] using (pow_le_pow_left₀ (norm_nonneg _) (hM y) 2)
      exact mul_le_mul hh (pow_le_pow_left₀ (norm_nonneg _) (gradient_difference_norm_le hg y a) 2)
        (sq_nonneg _) (sq_nonneg M)
    · intro y hy
      dsimp only [Pi.mul_apply]
      rw [image_eq_zero_of_notMem_tsupport hy,zero_pow (by norm_num : 2≠0),zero_mul]
  · have hm : Measurable (fun y ↦ g (y+a)-g y) :=
      (hg.continuous.measurable.comp (measurable_id.add_const a)).sub hg.continuous.measurable
    apply integrable_bounded_compact ((hm.pow_const 2).mul ((measurable_fderiv ℝ η).norm.pow_const 2)) hc
      (M := ((K:ℝ)*‖a‖)^2*(D:ℝ)^2)
    · intro y
      dsimp only [Pi.mul_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      have hh : (g (y+a)-g y)^2≤((K:ℝ)*‖a‖)^2 := by
        simpa only [Real.norm_eq_abs,sq_abs] using (pow_le_pow_left₀ (norm_nonneg _) (height_difference_norm_le hg y a) 2)
      exact mul_le_mul hh (pow_le_pow_left₀ (norm_nonneg _) (hDη y) 2)
        (sq_nonneg _) (sq_nonneg _)
    · intro y hy
      dsimp only [Pi.mul_apply]
      rw [fderiv_of_notMem_tsupport ℝ hy,norm_zero,zero_pow (by norm_num : 2≠0),mul_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cmcJacobian_contDiff : ContDiff ℝ (⊤ : ℕ∞) cmcJacobian := by
  have he : cmcJacobian=fderiv ℝ cmcFlux := funext (fun p ↦ (cmcFlux_hasFDerivAt p).fderiv.symm)
  rw [he]
  exact cmcFlux_contDiff.fderiv_right (by simp)

lemma cmcJacobian_symmetric (p v w : Plane) :
    ⟪v,cmcJacobian p w⟫=⟪cmcJacobian p v,w⟫ := by
  simp only [cmcJacobian_apply,inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
    RCLike.conj_to_real]
  rw [real_inner_comm v p]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma measurable_plane_clm_apply {A : Plane → Plane →L[ℝ] Plane} {v : Plane → Plane}
    (hA : Measurable A) (hv : Measurable v) : Measurable (fun y ↦ A y (v y)) := by
  have hc : Continuous (fun z : (Plane →L[ℝ] Plane) × Plane ↦ z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  exact hc.measurable.comp (hA.prodMk hv)

lemma linear_cmc_flux_measurable (g : Plane → ℝ) {p B : Plane → Plane}
    (hp : Continuous p) (hB : Continuous B) :
    Measurable (fun y ↦ cmcJacobian (p y) (gradient g y)-B y) :=
  (measurable_plane_clm_apply (cmcJacobian_contDiff.continuous.comp hp).measurable (measurable_plane_gradient g)).sub hB.measurable

lemma linear_cmc_flux_bound {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {p B : Plane → Plane} (hp : ∀ y,‖p y‖≤1) {M : ℝ} (hB : ∀ y,‖B y‖≤M) (y : Plane) :
    ‖cmcJacobian (p y) (gradient g y)-B y‖≤2*(K:ℝ)+M := by
  have hh : ‖gradient g y‖≤(K:ℝ) := by rw [plane_gradient_norm]; exact norm_fderiv_le_of_lipschitz ℝ hg
  exact (norm_sub_le _ _).trans (add_le_add
    ((cmcJacobian_norm_le (hp y) _).trans (by linarith)) (hB y))

lemma LinearCMCEquation.difference_test {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {p B : Plane → Plane} (hp : Continuous p) (hpb : ∀ y,‖p y‖≤1)
    (hB : Continuous B) {M : ℝ} (hBb : ∀ y,‖B y‖≤M) {R r : ℝ} (hr : 0 < r)
    (hw : LinearCMCEquation g p B (Metric.ball 0 R)) {a : Plane} (ha : r+‖a‖≤R)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆Metric.ball 0 r) :
    (∫ y,fderiv ℝ ψ y ((cmcJacobian (p (y+a)) (gradient g (y+a))-B (y+a))-
      (cmcJacobian (p y) (gradient g y)-B y)))=0 := by
  let F : Plane → Plane := fun y ↦ cmcJacobian (p y) (gradient g y)-B y
  have hFm : Measurable F := linear_cmc_flux_measurable g hp hB
  have hFb : ∀ y,‖F y‖≤2*(K:ℝ)+M := linear_cmc_flux_bound hg hpb hBb
  have hFt : Measurable (fun y ↦ F (y+a)) := hFm.comp (measurable_id.add_const a)
  have hFdb : ∀ y,‖F (y+a)-F y‖≤2*(2*(K:ℝ)+M) := fun y ↦
    (norm_sub_le _ _).trans (by linarith [hFb (y+a),hFb y])
  apply weak_flux_C1_test hr (hFt.sub hFm) hFdb 0 ?_ hψ hc hs |>.trans (by simp)
  intro φ hφ hφc hφs
  let χ : Plane → ℝ := fun y ↦ φ (y-a)
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := hφ.comp (contDiff_id.sub contDiff_const)
  have hχs := translated_test_support hφs ha
  have hχc : HasCompactSupport χ := hφc.comp_homeomorph (Homeomorph.addRight (-a))
  have hχe := hw χ hχ hχc hχs
  have hi := integral_add_right_eq_self (μ := (volume : Measure Plane)) (fun y ↦ fderiv ℝ χ y (F y)) a
  simp only [χ,fderiv_comp_sub,add_sub_cancel_right] at hi
  simp only [χ,fderiv_comp_sub] at hχe
  have ht : (∫ y,fderiv ℝ φ y (F (y+a)))=0 := hi.trans hχe
  have hz := hw φ hφ hφc (hφs.trans (Metric.ball_subset_ball (by linarith [norm_nonneg a])))
  change (∫ y,fderiv ℝ φ y (F (y+a)-F y))=0*(∫ y,φ y)
  simp_rw [map_sub]
  rw [integral_sub
    (integrable_differential_apply_of_bounded hFt (fun y ↦ hFb (y+a)) (hφ.of_le (by simp)) hφc)
    (integrable_differential_apply_of_bounded hFm hFb (hφ.of_le (by simp)) hφc),ht,hz]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma compact_weighted_energy_integrable {η : Plane → ℝ} (hη : Continuous η)
    (hc : HasCompactSupport η) {D : Plane → Plane} (hD : Measurable D)
    {M : ℝ} (hDb : ∀ y,‖D y‖≤M) : Integrable (fun y ↦ η y^2*‖D y‖^2) := by
  obtain ⟨N,hN⟩ := hη.norm.bddAbove_range_of_hasCompactSupport hc.norm
  have hb (y : Plane) : ‖η y‖≤N := hN (mem_range_self y)
  apply integrable_bounded_compact ((hη.measurable.pow_const 2).mul (hD.norm.pow_const 2)) hc
    (M := N^2*M^2)
  · intro y
    dsimp only [Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    have hηb : η y^2≤N^2 := by
      simpa only [Real.norm_eq_abs,sq_abs] using (pow_le_pow_left₀ (norm_nonneg _) (hb y) 2)
    exact mul_le_mul hηb (pow_le_pow_left₀ (norm_nonneg _) (hDb y) 2) (sq_nonneg _) (sq_nonneg N)
  · intro y hy
    dsimp only [Pi.mul_apply]
    rw [image_eq_zero_of_notMem_tsupport hy,zero_pow (by norm_num : 2≠0),zero_mul]

theorem LinearCMCEquation.caccioppoli {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {p B : Plane → Plane} (hp : Continuous p) (hpb : ∀ y,‖p y‖≤1)
    (hB : Continuous B) {M : ℝ} (hBb : ∀ y,‖B y‖≤M) {R r : ℝ}
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R)) (hr : 0 < r)
    (hw : LinearCMCEquation g p B (Metric.ball 0 R)) {a : Plane} (ha : r+‖a‖≤R)
    {η : Plane → ℝ} (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η)
    (hs : tsupport η⊆Metric.ball 0 r) :
    (∫ y,η y^2*‖gradient g (y+a)-gradient g y‖^2) ≤
      4096*(∫ y,(g (y+a)-g y)^2*‖fderiv ℝ η y‖^2)+
      256*(∫ y,η y^2*‖B (y+a)-B y-(cmcJacobian (p (y+a))-cmcJacobian (p y)) (gradient g y)‖^2) := by
  let w : Plane → ℝ := fun y ↦ g (y+a)-g y
  let F : Plane → Plane := fun y ↦ (cmcJacobian (p (y+a)) (gradient g (y+a))-B (y+a))-
    (cmcJacobian (p y) (gradient g y)-B y)
  let D : Plane → Plane := fun y ↦ B (y+a)-B y-(cmcJacobian (p (y+a))-cmcJacobian (p y)) (gradient g y)
  let ψ : Plane → ℝ := fun y ↦ η y^2*w y
  have hwc := translated_difference_contDiffOn hgc ha
  have hψ : ContDiff ℝ 1 ψ := local_C1_cutoff_product Metric.isOpen_ball hη hwc hs
  have hψs : tsupport ψ⊆tsupport η := energyTest_tsupport
  have hψc : HasCompactSupport ψ := hc.of_isClosed_subset isClosed_closure hψs
  have heq : (∫ y,fderiv ℝ ψ y (F y))=0 := hw.difference_test hg hp hpb hB hBb hr ha hψ hψc (hψs.trans hs)
  have hgB (y : Plane) : ‖gradient g y‖≤(K:ℝ) := by
    rw [plane_gradient_norm]; exact norm_fderiv_le_of_lipschitz ℝ hg
  have hFm₀ := linear_cmc_flux_measurable g hp hB
  have hFm : Measurable F := (hFm₀.comp (measurable_id.add_const a)).sub hFm₀
  have hFb (y : Plane) : ‖F y‖≤2*(2*(K:ℝ)+M) := (norm_sub_le _ _).trans
    (by linarith [linear_cmc_flux_bound hg hpb hBb (y+a),linear_cmc_flux_bound hg hpb hBb y])
  have hFi := integrable_differential_apply_of_bounded hFm hFb hψ hψc
  have hAm := (cmcJacobian_contDiff.continuous.comp hp).measurable
  have hDm : Measurable D := ((hB.measurable.comp (measurable_id.add_const a)).sub hB.measurable).sub
    (measurable_plane_clm_apply ((hAm.comp (measurable_id.add_const a)).sub hAm) (measurable_plane_gradient g))
  have hDb (y : Plane) : ‖D y‖≤2*M+4*(K:ℝ) := by
    dsimp only [D]
    rw [sub_apply]
    refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (by linarith [hBb (y+a),hBb y])) ?_)
    exact (norm_sub_le _ _).trans (by
      linarith [cmcJacobian_norm_le (hpb (y+a)) (gradient g y), cmcJacobian_norm_le (hpb y) (gradient g y), hgB y])
  obtain ⟨hAi,hBi⟩ := cmc_cutoff_energies_integrable hg hη hc a
  have hDi := compact_weighted_energy_integrable hη.continuous hc hDm hDb
  have hFe (y : Plane) : F y=cmcJacobian (p (y+a)) (gradient g (y+a)-gradient g y)-D y := by
    dsimp only [F,D]
    rw [map_sub,sub_apply]
    abel
  have hpoint (y : Plane) :
      (1/16)*(η y^2*‖gradient g (y+a)-gradient g y‖^2)-
        256*((g (y+a)-g y)^2*‖fderiv ℝ η y‖^2)-16*(η y^2*‖D y‖^2) ≤ fderiv ℝ ψ y (F y) := by
    by_cases hy : y∈tsupport η
    · have hdη := hη.differentiable (by simp) y
      have hdw := ((hwc y (hs hy)).contDiffAt (Metric.isOpen_ball.mem_nhds (hs hy))).differentiableAt (by simp)
      have hd : fderiv ℝ ψ y (F y) =
          η y^2*⟪gradient g (y+a)-gradient g y,F y⟫+2*η y*w y*fderiv ℝ η y (F y) := by
        change fderiv ℝ (fun z ↦ (η^2) z*(g (z+a)-g z)) y (F y)=_
        rw [fderiv_fun_mul (hdη.pow 2) hdw,fderiv_pow 2 hdη]
        change (η y^2 • fderiv ℝ (fun z ↦ g (z+a)-g z) y + (g (y+a)-g y) •
          ((2 • η y^(2-1)) • fderiv ℝ η y)) (F y)=_
        simp only [add_apply,smul_apply,smul_eq_mul,Nat.reduceSub,pow_one,two_smul]
        rw [translated_difference_fderiv hgc ha (hs hy)]
        ring
      rw [hd,hFe]
      convert cmc_linear_energy_absorption (hpb (y+a)) (gradient g (y+a)-gradient g y) (D y)
        (η y) (w y) (fderiv ℝ η y) using 1; dsimp only [w]; ring
    · rw [image_eq_zero_of_notMem_tsupport hy,fderiv_of_notMem_tsupport ℝ hy,
        fderiv_of_notMem_tsupport ℝ (fun h ↦ hy (hψs h)),zero_apply,norm_zero]
      norm_num
  have hInt := integral_mono (((hAi.const_mul (1/16)).sub (hBi.const_mul 256)).sub (hDi.const_mul 16)) hFi hpoint
  simp only [Pi.sub_apply] at hInt
  have hAB : Integrable (fun y ↦ (1/16)*(η y^2*‖gradient g (y+a)-gradient g y‖^2)-
      256*((g (y+a)-g y)^2*‖fderiv ℝ η y‖^2)) := (hAi.const_mul (1/16)).sub (hBi.const_mul 256)
  rw [integral_sub hAB (hDi.const_mul 16),
    integral_sub (hAi.const_mul (1/16)) (hBi.const_mul 256),integral_const_mul,
    integral_const_mul,integral_const_mul,heq] at hInt
  change _ ≤ 4096*(∫ y,(g (y+a)-g y)^2*‖fderiv ℝ η y‖^2)+256*(∫ y,η y^2*‖D y‖^2)
  linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma compact_derivative_square_integrable {η : Plane → ℝ}
    (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) :
    Integrable (fun y ↦ ‖fderiv ℝ η y‖^2) := by
  have hd : Continuous (fderiv ℝ η) := hη.continuous_fderiv (by simp)
  have hdc : HasCompactSupport (fderiv ℝ η) := hc.fderiv ℝ
  have hsc : HasCompactSupport (fun y ↦ ‖fderiv ℝ η y‖^2) := by
    apply hdc.of_isClosed_subset isClosed_closure
    apply closure_mono
    intro y hy
    contrapose! hy
    simp only [Function.mem_support,not_not] at hy ⊢
    simp [hy]
  exact (hd.norm.pow 2).integrable_of_hasCompactSupport hsc

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma linear_cmc_difference_source_bound {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {p B : Plane → Plane} {LA LB : ℝ≥0}
    (hA : LipschitzWith LA (fun y ↦ cmcJacobian (p y))) (hB : LipschitzWith LB B)
    (y a : Plane) :
    ‖B (y+a)-B y-(cmcJacobian (p (y+a))-cmcJacobian (p y)) (gradient g y)‖≤
      ((LB:ℝ)+(LA:ℝ)*(K:ℝ))*‖a‖ := by
  have hBA : ‖B (y+a)-B y‖≤(LB:ℝ)*‖a‖ := by
    simpa only [dist_eq_norm,add_sub_cancel_left] using hB.dist_le_mul (y+a) y
  have hAA : ‖cmcJacobian (p (y+a))-cmcJacobian (p y)‖≤(LA:ℝ)*‖a‖ := by
    simpa only [dist_eq_norm,add_sub_cancel_left] using hA.dist_le_mul (y+a) y
  have hgB : ‖gradient g y‖≤(K:ℝ) := by
    rw [plane_gradient_norm]; exact norm_fderiv_le_of_lipschitz ℝ hg
  have hop := (ContinuousLinearMap.le_opNorm (cmcJacobian (p (y+a))-cmcJacobian (p y)) (gradient g y)).trans
    (mul_le_mul hAA hgB (norm_nonneg _) (by positivity))
  exact (norm_sub_le _ _).trans (by nlinarith)

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

theorem LinearCMCEquation.local_gradient_energy {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {p B : Plane → Plane} (hp : Continuous p) (hpb : ∀ y,‖p y‖≤1)
    {LA LB : ℝ≥0} (hA : LipschitzWith LA (fun y ↦ cmcJacobian (p y))) (hB : LipschitzWith LB B)
    {M : ℝ} (hBb : ∀ y,‖B y‖≤M) {R r s : ℝ}
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R)) (hs : 0 < s) (hsr : s < r)
    (hw : LinearCMCEquation g p B (Metric.ball 0 R)) :
    ∃ C : ℝ,0≤C ∧ ∀ a : Plane,r+‖a‖≤R →
      (∫ y in Metric.ball 0 s,‖gradient g (y+a)-gradient g y‖^2)≤C*‖a‖^2 := by
  let b : ContDiffBump (0 : Plane) := ⟨s,(s+r)/2,hs,by linarith⟩
  have hbs : tsupport b⊆Metric.ball 0 r := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  have hi := compact_derivative_square_integrable (b.contDiff (n := 1)) b.hasCompactSupport
  have hb2 : Integrable (fun y ↦ b y^2) := by
    have hbc : Continuous (fun y : Plane ↦ b y * b y) := b.continuous.mul b.continuous
    have hbsq : HasCompactSupport (fun y : Plane ↦ b y * b y) := b.hasCompactSupport.mul_right
    have hi : Integrable (fun y : Plane ↦ b y * b y) (volume : Measure Plane) := hbc.integrable_of_hasCompactSupport hbsq
    exact hi.congr (Eventually.of_forall fun y ↦ by ring)
  let D : ℝ := (LB:ℝ)+(LA:ℝ)*(K:ℝ)
  let C : ℝ := 4096*(K:ℝ)^2*(∫ y,‖fderiv ℝ b y‖^2)+256*D^2*(∫ y,b y^2)
  have hC : 0≤C := by
    dsimp only [C]
    exact add_nonneg (mul_nonneg (by positivity) (integral_nonneg fun _ ↦ sq_nonneg _))
      (mul_nonneg (by positivity) (integral_nonneg fun _ ↦ sq_nonneg _))
  refine ⟨C,hC,fun a ha ↦ ?_⟩
  obtain ⟨hAi,hBi⟩ := cmc_cutoff_energies_integrable hg (b.contDiff (n := 1)) b.hasCompactSupport a
  have hbound : (∫ y,(g (y+a)-g y)^2*‖fderiv ℝ b y‖^2)≤
      ((K:ℝ)*‖a‖)^2*(∫ y,‖fderiv ℝ b y‖^2) := by
    rw [← integral_const_mul]
    apply integral_mono hBi (hi.const_mul _)
    intro y
    have hh : (g (y+a)-g y)^2≤((K:ℝ)*‖a‖)^2 := by
      simpa only [Real.norm_eq_abs,sq_abs] using
        pow_le_pow_left₀ (norm_nonneg _) (height_difference_norm_le hg y a) 2
    nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg ‖fderiv ℝ b y‖)]
  have hsource : (∫ y,b y^2*‖B (y+a)-B y-
      (cmcJacobian (p (y+a))-cmcJacobian (p y)) (gradient g y)‖^2)≤
      (D*‖a‖)^2*(∫ y,b y^2) := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ by positivity) (hb2.const_mul _)
    exact Eventually.of_forall fun y ↦ by
      have hh := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
        (linear_cmc_difference_source_bound hg hA hB y a) 2) (sq_nonneg (b y))
      dsimp only [D]
      nlinarith
  calc
    (∫ y in Metric.ball 0 s,‖gradient g (y+a)-gradient g y‖^2) =
        ∫ y in Metric.ball 0 s,b y^2*‖gradient g (y+a)-gradient g y‖^2 := by
      apply setIntegral_congr_fun measurableSet_ball
      intro y hy
      dsimp only
      rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)]
      simp
    _ ≤ ∫ y,b y^2*‖gradient g (y+a)-gradient g y‖^2 :=
      setIntegral_le_integral hAi (ae_of_all _ fun _ ↦ by positivity)
    _ ≤ 4096*(∫ y,(g (y+a)-g y)^2*‖fderiv ℝ b y‖^2)+256*(∫ y,b y^2*‖B (y+a)-B y-
        (cmcJacobian (p (y+a))-cmcJacobian (p y)) (gradient g y)‖^2) :=
      hw.caccioppoli hg hp hpb hB.continuous hBb hgc (by linarith) ha b.contDiff b.hasCompactSupport hbs
    _ ≤ 4096*(((K:ℝ)*‖a‖)^2*(∫ y,‖fderiv ℝ b y‖^2))+256*((D*‖a‖)^2*(∫ y,b y^2)) := by linarith
    _ = C*‖a‖^2 := by dsimp only [C]; ring

end CubicTorus

end
end

section

noncomputable section
open Filter Set
open scoped Topology RealInnerProductSpace
namespace CubicTorus
universe uHilbert

theorem hilbert_bounded_weak_subsequence {E : Type uHilbert}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] (f : ℕ → E) {M : ℝ}
    (hb : ∀ i, ‖f i‖≤M) :
    ∃ (u : E) (φ : ℕ → ℕ), ‖u‖≤M ∧ StrictMono φ ∧
      ∀ v : E, Tendsto (fun i ↦ ⟪f (φ i),v⟫) atTop (𝓝 ⟪u,v⟫) := by
  let F : ℕ → WeakDual ℝ E := fun i ↦ StrongDual.toWeakDual ((InnerProductSpace.toDual ℝ E) (f i))
  have hm (i : ℕ) : F i∈WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ E) M := by
    simp only [mem_preimage,Metric.mem_closedBall,dist_zero_right]
    change ‖(InnerProductSpace.toDual ℝ E) (f i)‖≤M
    rw [(InnerProductSpace.toDual ℝ E).norm_map]
    exact hb i
  obtain ⟨L,hL,φ,hφ,hlim⟩ := (WeakDual.isSeqCompact_closedBall ℝ E (0 : StrongDual ℝ E) M) hm
  let u : E := (InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual L)
  refine ⟨u,φ,?_,hφ,fun v ↦ ?_⟩
  · change ‖(InnerProductSpace.toDual ℝ E).symm _‖≤M
    rw [(InnerProductSpace.toDual ℝ E).symm.norm_map]
    simpa only [mem_preimage,Metric.mem_closedBall,dist_zero_right] using hL
  · have hh := ((WeakDual.eval_continuous v).tendsto L).comp hlim
    simpa only [F,Function.comp_def,StrongDual.toWeakDual_apply,InnerProductSpace.toDual_apply_apply,
      u,InnerProductSpace.toDual_symm_apply,WeakDual.toStrongDual_apply] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_difference_quotient_pairing {f ψ : Plane → ℝ}
    (hf : Continuous f) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (t : ℝ) (v : Plane) :
    (∫ y, (t⁻¹*(f (y+t • v)-f y))*ψ y)=
      ∫ y, (t⁻¹*(ψ (y+t • (-v))-ψ y))*f y := by
  have h₁ : Integrable (fun y ↦ f (y+t • v)*ψ y) :=
    ((hf.comp (continuous_id.add continuous_const)).mul hψ).integrable_of_hasCompactSupport hc.mul_left
  have h₂ : Integrable (fun y ↦ f y*ψ y) :=
    (hf.mul hψ).integrable_of_hasCompactSupport hc.mul_left
  have h₃ : Integrable (fun y ↦ f y*ψ (y+t • (-v))) :=
    (hf.mul (hψ.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      (hc.comp_homeomorph (Homeomorph.addRight (t • (-v)))).mul_left
  have he : (∫ y, f (y+t • v)*ψ y)=(∫ y, f y*ψ (y+t • (-v))) := by
    rw [← integral_add_right_eq_self _ (t • (-v))]
    simp
  simp_rw [mul_assoc,← mul_comm (f _),sub_mul,mul_sub]
  rw [integral_sub (h₁.const_mul _) (h₂.const_mul _),
    integral_sub (h₃.const_mul _) (h₂.const_mul _),integral_const_mul,integral_const_mul,
    integral_const_mul,he]

theorem continuous_difference_quotient_test_limit {f ψ : Plane → ℝ}
    (hf : Continuous f) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (v : Plane) :
    Tendsto (fun t : ℝ ↦ ∫ y, (t⁻¹*(f (y+t • v)-f y))*ψ y) (𝓝[>] 0)
      (𝓝 (-(∫ y, f y*fderiv ℝ ψ y v))) := by
  obtain ⟨L,hL⟩ := hψ.lipschitzWith_of_hasCompactSupport hc (by simp)
  have hh := LipschitzWith.integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul'
    (μ := (volume : Measure Plane)) hL hc hf (-v)
  have he : (∫ y, lineDeriv ℝ ψ y (-v)*f y)= -(∫ y, f y*fderiv ℝ ψ y v) := by
    simp_rw [(hψ.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv,
      map_neg,neg_mul,integral_neg,mul_comm _ (f _)]
  rw [he] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext t
  exact continuous_difference_quotient_pairing hf hψ.continuous hc t v

end CubicTorus

end
end

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

lemma C1_gradient_continuousOn {g : Plane → ℝ} {U : Set Plane}
    (hg : ContDiffOn ℝ 1 g U) (hU : IsOpen U) : ContinuousOn (gradient g) U :=
  (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp_continuousOn
    (hg.continuousOn_fderiv_of_isOpen hU le_rfl)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma differenceStep_mem {δ : ℝ} (hδ : 0<δ) (i : ℕ) : differenceStep δ i∈Ioc 0 δ := by
  have hn : (1:ℝ)≤(i:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) i]
  constructor
  · dsimp only [differenceStep]; positivity
  · dsimp only [differenceStep]
    exact mul_le_of_le_one_right hδ.le (by rw [div_le_one (by linarith : (0:ℝ)<(i:ℝ)+1)]; exact hn)

lemma differenceStep_tendsto {δ : ℝ} (hδ : 0<δ) : Tendsto (differenceStep δ) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_,Eventually.of_forall (fun i ↦ (differenceStep_mem hδ i).1)⟩
  change Tendsto (fun i : ℕ ↦ δ*(1/((i:ℝ)+1))) atTop (𝓝 0)
  simpa only [mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ

lemma L2_vector_norm_sq_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u : Lp Plane 2 μ) : ‖u‖^2=∫ x, ‖u x‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem vector_L2_difference_subsequence {f : Plane → Plane}
    (hf : Continuous f) {M : ℝ} (hb : ∀ y, ‖f y‖≤M)
    {r δ C : ℝ} (hδ : 0<δ) (hC : 0≤C) (v : Plane)
    (he : ∀ t∈Ioc 0 δ, (∫ y in Metric.ball 0 r, ‖f (y+t • v)-f y‖^2)≤C*t^2) :
    ∃ (u : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r))) (φ : ℕ → ℕ),
      ‖u‖≤Real.sqrt C ∧ StrictMono φ ∧
      ∀ V : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r)),
        Tendsto (fun i ↦ ⟪(vectorDifference_memLp hf hb r (differenceStep δ (φ i)) v).toLp
          (vectorDifference f v (differenceStep δ (φ i))),V⟫) atTop (𝓝 ⟪u,V⟫) := by
  let μ : Measure Plane := volume.restrict (Metric.ball 0 r)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let : Fact ((2 : ℝ≥0∞)≠⊤) := ⟨by norm_num⟩
  let Q : ℕ → Lp Plane 2 μ := fun i ↦ (vectorDifference_memLp hf hb r (differenceStep δ i) v).toLp
    (vectorDifference f v (differenceStep δ i))
  have hQ (i : ℕ) : ‖Q i‖≤Real.sqrt C := by
    have heq : ‖Q i‖^2=(differenceStep δ i)⁻¹^2*
        (∫ y in Metric.ball 0 r, ‖f (y+differenceStep δ i • v)-f y‖^2) := by
      rw [L2_vector_norm_sq_integral]
      calc
        _ = ∫ y, ‖vectorDifference f v (differenceStep δ i) y‖^2 ∂μ := integral_congr_ae
          ((vectorDifference_memLp hf hb r (differenceStep δ i) v).coeFn_toLp.mono (fun y hy ↦ by rw [hy]))
        _ = _ := by simp only [vectorDifference,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,integral_const_mul,μ]
    have hh := mul_le_mul_of_nonneg_left (he _ (differenceStep_mem hδ i)) (sq_nonneg (differenceStep δ i)⁻¹)
    have htne := (differenceStep_mem hδ i).1.ne'
    have hsq := Real.sq_sqrt hC
    have hre : (differenceStep δ i)⁻¹^2*(C*(differenceStep δ i)^2)=C := by field_simp
    rw [hre,← heq] at hh
    nlinarith [norm_nonneg (Q i),Real.sqrt_nonneg C]
  exact hilbert_bounded_weak_subsequence Q hQ

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

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem LinearCMCEquation.gradient_difference_data {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {p B : Plane → Plane} (hp : Continuous p) (hpb : ∀ y,‖p y‖≤1)
    {LA LB : ℝ≥0} (hA : LipschitzWith LA (fun y ↦ cmcJacobian (p y))) (hB : LipschitzWith LB B)
    {M R : ℝ} (hBb : ∀ y,‖B y‖≤M) (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hw : LinearCMCEquation g p B (Metric.ball 0 R)) :
    ∃ (G : Plane → Plane) (C : ℝ), Continuous G ∧ (∀ y, ‖G y‖≤(K:ℝ)) ∧ 0≤C ∧
      (∀ y, ‖y‖≤R/2 → G y=gradient g y) ∧
      ∀ v : Plane, ‖v‖≤1 → ∀ t∈Ioc 0 (R/4),
        (∫ y in Metric.ball 0 (R/4), ‖G (y+t • v)-G y‖^2)≤C*t^2 := by
  let b : ContDiffBump (0 : Plane) := ⟨R/2,3*R/4,by linarith,by linarith⟩
  have hbs : tsupport b⊆Metric.ball 0 R := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  let G : Plane → Plane := fun y ↦ b y • gradient g y
  have hGc : Continuous G := continuous_local_vector_cutoff Metric.isOpen_ball
    (C1_gradient_continuousOn hgc Metric.isOpen_ball) b.continuous hbs
  have hgrad (y : Plane) : ‖gradient g y‖≤(K:ℝ) := by
    rw [plane_gradient_norm]; exact norm_fderiv_le_of_lipschitz ℝ hg
  have hGb (y : Plane) : ‖G y‖≤(K:ℝ) := by
    dsimp only [G]
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg b.nonneg]
    exact (mul_le_mul_of_nonneg_left (hgrad y) b.nonneg).trans
      (mul_le_of_le_one_left K.coe_nonneg b.le_one)
  have hGeq {y : Plane} (hy : ‖y‖≤R/2) : G y=gradient g y := by
    dsimp only [G]
    rw [b.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right] using hy),one_smul]
  obtain ⟨C,hC,henergy⟩ := hw.local_gradient_energy hg hp hpb hA hB hBb hgc
    (show 0<R/4 by linarith) (show R/4<R/2 by linarith)
  refine ⟨G,C,hGc,hGb,hC,fun _ hy ↦ hGeq hy,fun v hv t ht ↦ ?_⟩
  have ha : ‖t • v‖≤t := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht.1]
    exact mul_le_of_le_one_right ht.1.le hv
  calc
    _ = ∫ y in Metric.ball 0 (R/4), ‖gradient g (y+t • v)-gradient g y‖^2 := by
      apply setIntegral_congr_fun measurableSet_ball
      intro y hy
      have hy' : ‖y‖<R/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hy
      dsimp only
      rw [hGeq ((norm_add_le y (t • v)).trans (by linarith [ht.2])),hGeq (by linarith)]
    _ ≤ C*‖t • v‖^2 := henergy (t • v) (by linarith [ht.2])
    _ ≤ C*t^2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ha 2) hC

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma lipschitz_vector_quotient_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Plane → E} {K : ℝ≥0} (hf : LipschitzWith K f) {t : ℝ} (ht : t≠0) (y v : Plane) :
    ‖t⁻¹ • (f (y+t • v)-f y)‖≤(K:ℝ)*‖v‖ := by
  have hh : ‖f (y+t • v)-f y‖≤(K:ℝ)*(|t| *‖v‖) := by
    simpa only [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs] using hf.dist_le_mul (y+t • v) y
  rw [norm_smul,Real.norm_eq_abs,abs_inv]
  calc
    _ ≤ |t|⁻¹*((K:ℝ)*(|t| *‖v‖)) := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (abs_nonneg _))
    _ = _ := by field_simp

lemma differentiable_vector_quotient_limit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Plane → E} {y : Plane} (hf : DifferentiableAt ℝ f y) (v : Plane)
    {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝[>] 0)) :
    Tendsto (fun i ↦ (t i)⁻¹ • (f (y+t i • v)-f y)) atTop (𝓝 (fderiv ℝ f y v)) :=
  (hf.hasFDerivAt.hasLineDerivAt v).tendsto_slope_zero_right.comp ht

lemma linear_source_difference_limit {f : Plane → Plane} (hf : Continuous f)
    {M : ℝ} (hb : ∀ y,‖f y‖≤M) {A : Plane → Plane →L[ℝ] Plane} {B : Plane → Plane}
    {LA LB : ℝ≥0} (hA : LipschitzWith LA A) (hB : LipschitzWith LB B)
    (hAd : Differentiable ℝ A) (hBd : Differentiable ℝ B)
    {r : ℝ} {t : ℕ → ℝ} (ht : ∀ i,0<t i) (htlim : Tendsto t atTop (𝓝[>] 0))
    (v : Plane) {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    Tendsto (fun i ↦ ∫ y in Metric.ball 0 r,fderiv ℝ ψ y
      (((t i)⁻¹ • (A (y+t i • v)-A y)) (f (y+t i • v))-(t i)⁻¹ • (B (y+t i • v)-B y))) atTop
      (𝓝 (∫ y in Metric.ball 0 r,fderiv ℝ ψ y (fderiv ℝ A y v (f y)-fderiv ℝ B y v))) := by
  let μ : Measure Plane := volume.restrict (Metric.ball 0 r)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  obtain ⟨L,hL⟩ := hψ.lipschitzWith_of_hasCompactSupport hc (by simp)
  apply tendsto_integral_of_dominated_convergence (fun _ ↦ (L:ℝ)*((LA:ℝ)*‖v‖*M+(LB:ℝ)*‖v‖))
  · intro i
    apply Continuous.aestronglyMeasurable
    have hcA : Continuous (fun y : Plane ↦ (t i)⁻¹ • (A (y+t i • v)-A y)) :=
      ((hA.continuous.comp (continuous_id.add continuous_const)).sub hA.continuous).const_smul ((t i)⁻¹ : ℝ)
    have hcB : Continuous (fun y : Plane ↦ (t i)⁻¹ • (B (y+t i • v)-B y)) :=
      ((hB.continuous.comp (continuous_id.add continuous_const)).sub hB.continuous).const_smul ((t i)⁻¹ : ℝ)
    exact (hψ.continuous_fderiv (by simp)).clm_apply
      ((hcA.clm_apply (hf.comp (continuous_id.add continuous_const))).sub hcB)
  · exact integrable_const _
  · intro i
    exact Eventually.of_forall fun y ↦ by
      have h₁ := (ContinuousLinearMap.le_opNorm ((t i)⁻¹ • (A (y+t i • v)-A y)) (f (y+t i • v))).trans
        (mul_le_mul (lipschitz_vector_quotient_bound hA (ht i).ne' y v) (hb _) (norm_nonneg _) (by positivity))
      have h₂ := lipschitz_vector_quotient_bound hB (ht i).ne' y v
      exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul
        (norm_fderiv_le_of_lipschitz ℝ hL) ((norm_sub_le _ _).trans (add_le_add h₁ h₂)) (norm_nonneg _) L.coe_nonneg)
  · exact Eventually.of_forall fun y ↦ by
      have hy : Tendsto (fun i ↦ y+t i • v) atTop (𝓝 y) := by
        simpa only [zero_smul,add_zero] using
          (tendsto_const_nhds (x := y)).add ((tendsto_nhds_of_tendsto_nhdsWithin htlim).smul (tendsto_const_nhds (x := v)))
      apply (fderiv ℝ ψ y).continuous.tendsto _ |>.comp
      have heval : Continuous (fun z : (Plane →L[ℝ] Plane) × Plane ↦ z.1 z.2) :=
        continuous_fst.clm_apply continuous_snd
      exact ((heval.tendsto _).comp ((differentiable_vector_quotient_limit (hAd y) v htlim).prodMk_nhds
        (hf.continuousAt.tendsto.comp hy))).sub (differentiable_vector_quotient_limit (hBd y) v htlim)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem vector_weak_quotient_derivative {f : Plane → Plane} (hf : Continuous f)
    {r : ℝ} {t : ℕ → ℝ} (htlim : Tendsto t atTop (𝓝[>] 0)) (v w : Plane)
    {Q : ℕ → Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r))}
    {u : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r))}
    (hQ : ∀ i, (Q i : Plane → Plane)=ᵐ[volume.restrict (Metric.ball (0 : Plane) r)] vectorDifference f v (t i))
    (hw : ∀ V : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r)),
      Tendsto (fun i ↦ ⟪Q i,V⟫) atTop (𝓝 ⟪u,V⟫))
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆Metric.ball 0 r) :
    (∫ y in Metric.ball 0 r, ⟪u y,w⟫*ψ y)= -(∫ y, ⟪f y,w⟫*fderiv ℝ ψ y v) := by
  let μ : Measure Plane := volume.restrict (Metric.ball 0 r)
  let W : Plane → Plane := fun y ↦ ψ y • w
  have hWc : Continuous W := hψ.continuous.smul continuous_const
  have hWs : HasCompactSupport W := hc.smul_right
  have hWm : MemLp W 2 μ := hWc.memLp_of_hasCompactSupport hWs
  let V : Lp Plane 2 μ := hWm.toLp W
  have hp (i : ℕ) : ⟪Q i,V⟫=(∫ y, ((t i)⁻¹*(⟪f (y+t i • v),w⟫-⟪f y,w⟫))*ψ y) := by
    rw [L2.inner_def,integral_mul_eq_restrict_of_tsupport measurableSet_ball _ ψ hs]
    apply integral_congr_ae
    filter_upwards [hQ i,hWm.coeFn_toLp] with y hy hy'
    rw [hy,hy']
    simp only [W,vectorDifference,inner_smul_right,inner_smul_left,inner_sub_left,RCLike.conj_to_real]
    ring
  have hup : ⟪u,V⟫=(∫ y in Metric.ball 0 r, ⟪u y,w⟫*ψ y) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hWm.coeFn_toLp] with y hy
    rw [hy]
    simp only [W,inner_smul_right]
    ring
  have hlim₁ := hw V
  simp_rw [hp,hup] at hlim₁
  have hlim₂ := (continuous_difference_quotient_test_limit (hf.inner (continuous_const (y := w))) hψ hc v).comp htlim
  exact tendsto_nhds_unique hlim₁ hlim₂

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma weak_linear_cmc_pairing {f : Plane → Plane} {p : Plane → Plane}
    (hp : Continuous p) (hpb : ∀ y,‖p y‖≤1) {r : ℝ} {t : ℕ → ℝ} (v : Plane)
    {Q : ℕ → Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r))}
    {u : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r))}
    (hQ : ∀ i,(Q i : Plane → Plane)=ᵐ[volume.restrict (Metric.ball (0 : Plane) r)] vectorDifference f v (t i))
    (hw : ∀ V : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r)),
      Tendsto (fun i ↦ ⟪Q i,V⟫) atTop (𝓝 ⟪u,V⟫))
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    Tendsto (fun i ↦ ∫ y in Metric.ball 0 r,fderiv ℝ ψ y (cmcJacobian (p y) (vectorDifference f v (t i) y))) atTop
      (𝓝 (∫ y in Metric.ball 0 r,fderiv ℝ ψ y (cmcJacobian (p y) (u y)))) := by
  let μ : Measure Plane := volume.restrict (Metric.ball 0 r)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  obtain ⟨L,hL⟩ := hψ.lipschitzWith_of_hasCompactSupport hc (by simp)
  have hgrad (y : Plane) : ‖gradient ψ y‖≤(L:ℝ) := by
    rw [plane_gradient_norm]; exact norm_fderiv_le_of_lipschitz ℝ hL
  let W : Plane → Plane := fun y ↦ cmcJacobian (p y) (gradient ψ y)
  have hWcont : Continuous W := (cmcJacobian_contDiff.continuous.comp hp).clm_apply
    ((InnerProductSpace.toDual ℝ Plane).symm.continuous.comp (hψ.continuous_fderiv (by simp)))
  have hWb (y : Plane) : ‖W y‖≤2*(L:ℝ) :=
    (cmcJacobian_norm_le (hpb y) _).trans (by gcongr; exact hgrad y)
  have hW : MemLp W 2 μ := MemLp.of_bound hWcont.aestronglyMeasurable (C := 2*(L:ℝ)) (Eventually.of_forall hWb)
  let V : Lp Plane 2 μ := hW.toLp W
  have hid (y z : Plane) : ⟪z,W y⟫=fderiv ℝ ψ y (cmcJacobian (p y) z) := by
    dsimp only [W]
    rw [cmcJacobian_symmetric,real_inner_comm,inner_gradient_left]
  have hpair (i : ℕ) : ⟪Q i,V⟫=(∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (vectorDifference f v (t i) y)) ∂μ) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hQ i,hW.coeFn_toLp] with y hy hz
    rw [hy,hz,hid]
  have hup : ⟪u,V⟫=(∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (u y)) ∂μ) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hW.coeFn_toLp] with y hy
    rw [hy,hid]
  have hh := hw V
  simpa only [hpair,hup,μ] using hh

lemma Lp.cmc_differential_integrable {p : Plane → Plane}
    (hp : Continuous p) (hpb : ∀ y,‖p y‖≤1) (r : ℝ)
    (u : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r)))
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun y ↦ fderiv ℝ ψ y (cmcJacobian (p y) (u y)))
      (volume.restrict (Metric.ball (0 : Plane) r)) := by
  let μ : Measure Plane := volume.restrict (Metric.ball 0 r)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  obtain ⟨L,hL⟩ := hψ.lipschitzWith_of_hasCompactSupport hc (by simp)
  let W : Plane → Plane := fun y ↦ cmcJacobian (p y) (gradient ψ y)
  have hWc : Continuous W := (cmcJacobian_contDiff.continuous.comp hp).clm_apply
    ((InnerProductSpace.toDual ℝ Plane).symm.continuous.comp (hψ.continuous_fderiv (by simp)))
  have hWb (y : Plane) : ‖W y‖≤2*(L:ℝ) := by
    have hg : ‖gradient ψ y‖≤(L:ℝ) := by
      rw [plane_gradient_norm]; exact norm_fderiv_le_of_lipschitz ℝ hL
    exact (cmcJacobian_norm_le (hpb y) _).trans (by linarith)
  have hW : MemLp W 2 μ := MemLp.of_bound hWc.aestronglyMeasurable (C := 2*(L:ℝ)) (Eventually.of_forall hWb)
  apply (L2.integrable_inner (𝕜 := ℝ) u (hW.toLp W)).congr
  filter_upwards [hW.coeFn_toLp] with y hy
  rw [hy]
  dsimp only [W]
  rw [cmcJacobian_symmetric,real_inner_comm,inner_gradient_left]

theorem weak_L2_linear_cmc_chain {f : Plane → Plane} (hf : Continuous f)
    {M : ℝ} (hb : ∀ y,‖f y‖≤M) {p B : Plane → Plane} (hp : Continuous p) (hpb : ∀ y,‖p y‖≤1)
    {LA LB : ℝ≥0} (hA : LipschitzWith LA (fun y ↦ cmcJacobian (p y))) (hB : LipschitzWith LB B)
    (hAd : Differentiable ℝ (fun y ↦ cmcJacobian (p y))) (hBd : Differentiable ℝ B)
    {r : ℝ} {t : ℕ → ℝ} (ht : ∀ i,0<t i) (htlim : Tendsto t atTop (𝓝[>] 0))
    (v : Plane) {Q : ℕ → Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r))}
    {u : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r))}
    (hQ : ∀ i,(Q i : Plane → Plane)=ᵐ[volume.restrict (Metric.ball (0 : Plane) r)] vectorDifference f v (t i))
    (hw : ∀ V : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) r)),
      Tendsto (fun i ↦ ⟪Q i,V⟫) atTop (𝓝 ⟪u,V⟫))
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    Tendsto (fun i ↦ ∫ y in Metric.ball 0 r,fderiv ℝ ψ y ((t i)⁻¹ •
      ((cmcJacobian (p (y+t i • v)) (f (y+t i • v))-B (y+t i • v))-
        (cmcJacobian (p y) (f y)-B y)))) atTop
      (𝓝 ((∫ y in Metric.ball 0 r,fderiv ℝ ψ y (cmcJacobian (p y) (u y)))+
        (∫ y in Metric.ball 0 r,fderiv ℝ ψ y
          (fderiv ℝ (fun z ↦ cmcJacobian (p z)) y v (f y)-fderiv ℝ B y v)))) := by
  have h₁ := weak_linear_cmc_pairing hp hpb v hQ hw hψ hc
  have h₂ := linear_source_difference_limit hf hb hA hB hAd hBd ht htlim v hψ hc (r := r)
  convert h₁.add h₂ using 1
  all_goals try with_reducible_and_instances rfl
  funext i
  let A : Plane → Plane →L[ℝ] Plane := fun y ↦ cmcJacobian (p y)
  have hD : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv (by simp)
  have hAi : Continuous (fun y : Plane ↦ A y (vectorDifference f v (t i) y)) :=
    hA.continuous.clm_apply (((hf.comp (continuous_id.add continuous_const)).sub hf).const_smul ((t i)⁻¹ : ℝ))
  have hSi : Continuous (fun y : Plane ↦ ((t i)⁻¹ • (A (y+t i • v)-A y)) (f (y+t i • v))-
      (t i)⁻¹ • (B (y+t i • v)-B y)) := by
    have hcA : Continuous (fun y : Plane ↦ (t i)⁻¹ • (A (y+t i • v)-A y)) :=
      ((hA.continuous.comp (continuous_id.add continuous_const)).sub hA.continuous).const_smul ((t i)⁻¹ : ℝ)
    have hcB : Continuous (fun y : Plane ↦ (t i)⁻¹ • (B (y+t i • v)-B y)) :=
      ((hB.continuous.comp (continuous_id.add continuous_const)).sub hB.continuous).const_smul ((t i)⁻¹ : ℝ)
    exact (hcA.clm_apply (hf.comp (continuous_id.add continuous_const))).sub hcB
  have hi₁ := (hD.clm_apply hAi).continuousOn.integrableOn_compact (μ := (volume : Measure Plane)) (isCompact_closedBall (0 : Plane) r)
    |>.mono_set Metric.ball_subset_closedBall
  have hi₂ := (hD.clm_apply hSi).continuousOn.integrableOn_compact (μ := (volume : Measure Plane)) (isCompact_closedBall (0 : Plane) r)
    |>.mono_set Metric.ball_subset_closedBall
  rw [← integral_add hi₁ hi₂]
  apply setIntegral_congr_fun measurableSet_ball
  intro y _hy
  dsimp only [A,vectorDifference]
  simp only [map_sub,map_smul,smul_eq_mul,sub_apply,smul_apply]
  ring

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

lemma differential_integral_restrict {ψ : Plane → ℝ} {S : Set Plane}
    (hs : tsupport ψ⊆S) (F : Plane → Plane) :
    (∫ y in S, fderiv ℝ ψ y (F y))=(∫ y, fderiv ℝ ψ y (F y)) := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro y hy
  rw [fderiv_of_notMem_tsupport ℝ (fun hy' ↦ hy (hs hy')),zero_apply]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem LinearCMCEquation.weak_derivative {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {p B : Plane → Plane} (hp : Continuous p) (hpb : ∀ y,‖p y‖≤1)
    {LA LB : ℝ≥0} (hA : LipschitzWith LA (fun y ↦ cmcJacobian (p y))) (hB : LipschitzWith LB B)
    (hAc : ContDiff ℝ 1 (fun y ↦ cmcJacobian (p y))) (hBc : ContDiff ℝ 1 B)
    {M R : ℝ} (hBb : ∀ y,‖B y‖≤M) (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hw : LinearCMCEquation g p B (Metric.ball 0 R)) (v : Plane) (hv : ‖v‖≤1) :
    ∃ u : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) (R/4))),
      (∀ (w : Plane) (ψ : Plane → ℝ), ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        tsupport ψ⊆Metric.ball 0 (R/4) →
        (∫ y in Metric.ball 0 (R/4), ⟪u y,w⟫*ψ y)=
          -(∫ y, ⟪gradient g y,w⟫*fderiv ℝ ψ y v)) ∧
      (∀ ψ : Plane → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
        tsupport ψ⊆Metric.ball 0 (R/4) →
        (∫ y in Metric.ball 0 (R/4), fderiv ℝ ψ y (cmcJacobian (p y) (u y)-
          (fderiv ℝ B y v-fderiv ℝ (fun z ↦ cmcJacobian (p z)) y v (gradient g y))))=0) := by
  obtain ⟨G,C,hGc,hGb,hC,hGeq,henergy⟩ := hw.gradient_difference_data hg hp hpb hA hB hBb hR hgc
  have hδ : 0<R/4 := by linarith
  obtain ⟨u,φ,_hu,hφ,hwk⟩ := vector_L2_difference_subsequence hGc hGb hδ hC v (henergy v hv)
  let t : ℕ → ℝ := fun i ↦ differenceStep (R/4) (φ i)
  let Q : ℕ → Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) (R/4))) := fun i ↦
    (vectorDifference_memLp hGc hGb (R/4) (t i) v).toLp (vectorDifference G v (t i))
  have ht (i : ℕ) : t i∈Ioc 0 (R/4) := differenceStep_mem hδ (φ i)
  have htlim : Tendsto t atTop (𝓝[>] 0) := (differenceStep_tendsto hδ).comp hφ.tendsto_atTop
  have hQ (i : ℕ) : (Q i : Plane → Plane)=ᵐ[volume.restrict (Metric.ball (0 : Plane) (R/4))]
      vectorDifference G v (t i) := (vectorDifference_memLp hGc hGb (R/4) (t i) v).coeFn_toLp
  have hweak : ∀ V : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) (R/4))),
      Tendsto (fun i ↦ ⟪Q i,V⟫) atTop (𝓝 ⟪u,V⟫) := hwk
  have hty (i : ℕ) : ‖t i • v‖≤t i := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (ht i).1]
    exact mul_le_of_le_one_right (ht i).1.le hv
  have hGy (y : Plane) (hy : y∈Metric.ball (0 : Plane) (R/4)) : G y=gradient g y := by
    apply hGeq
    have hh : ‖y‖<R/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hy
    linarith
  have hGyt (i : ℕ) (y : Plane) (hy : y∈Metric.ball (0 : Plane) (R/4)) :
      G (y+t i • v)=gradient g (y+t i • v) := by
    apply hGeq
    have hh : ‖y‖<R/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hy
    exact (norm_add_le _ _).trans (by linarith [hty i,(ht i).2])
  refine ⟨u,?_,?_⟩
  · intro w ψ hψ hc hs
    rw [vector_weak_quotient_derivative hGc htlim v w hQ hweak hψ hc hs]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y∈tsupport ψ
    · rw [hGy y (hs hy)]
    · rw [fderiv_of_notMem_tsupport ℝ hy,zero_apply,mul_zero,mul_zero]
  · intro ψ hψ hc hs
    have hlim := weak_L2_linear_cmc_chain hGc hGb hp hpb hA hB
      (hAc.differentiable (by simp)) (hBc.differentiable (by simp))
      (fun i ↦ (ht i).1) htlim v hQ hweak hψ hc
    have hzero (i : ℕ) : (∫ y in Metric.ball 0 (R/4),
        fderiv ℝ ψ y ((t i)⁻¹ • ((cmcJacobian (p (y+t i • v)) (G (y+t i • v))-B (y+t i • v))-
          (cmcJacobian (p y) (G y)-B y))))=0 := by
      calc
        _ = ∫ y in Metric.ball 0 (R/4), fderiv ℝ ψ y ((t i)⁻¹ •
            ((cmcJacobian (p (y+t i • v)) (gradient g (y+t i • v))-B (y+t i • v))-
              (cmcJacobian (p y) (gradient g y)-B y))) := by
          apply setIntegral_congr_fun measurableSet_ball
          intro y hy
          dsimp only
          rw [hGy y hy,hGyt i y hy]
        _ = ∫ y, fderiv ℝ ψ y ((t i)⁻¹ •
            ((cmcJacobian (p (y+t i • v)) (gradient g (y+t i • v))-B (y+t i • v))-
              (cmcJacobian (p y) (gradient g y)-B y))) := differential_integral_restrict hs _
        _ = (t i)⁻¹*(∫ y, fderiv ℝ ψ y
            ((cmcJacobian (p (y+t i • v)) (gradient g (y+t i • v))-B (y+t i • v))-
              (cmcJacobian (p y) (gradient g y)-B y))) := by
          simp only [map_smul,smul_eq_mul,integral_const_mul]
        _ = 0 := by
          rw [hw.difference_test hg hp hpb hB.continuous hBb hδ
            (by linarith [hty i,(ht i).2]) hψ hc hs,mul_zero]
    have he : (∫ y in Metric.ball 0 (R/4), fderiv ℝ ψ y (cmcJacobian (p y) (u y)))+
        (∫ y in Metric.ball 0 (R/4),fderiv ℝ ψ y
          (fderiv ℝ (fun z ↦ cmcJacobian (p z)) y v (G y)-fderiv ℝ B y v))=0 :=
      tendsto_nhds_unique hlim (by simp only [hzero]; exact tendsto_const_nhds)
    have hAi := Lp.cmc_differential_integrable hp hpb (R/4) u hψ hc
    have hSc : Continuous (fun y ↦ fderiv ℝ ψ y
        (fderiv ℝ (fun z ↦ cmcJacobian (p z)) y v (G y)-fderiv ℝ B y v)) :=
      (hψ.continuous_fderiv (by simp)).clm_apply
        ((((hAc.continuous_fderiv (by simp)).clm_apply continuous_const).clm_apply hGc).sub
          ((hBc.continuous_fderiv (by simp)).clm_apply continuous_const))
    have hSi := hSc.continuousOn.integrableOn_compact (μ := (volume : Measure Plane))
      (isCompact_closedBall (0 : Plane) (R/4)) |>.mono_set Metric.ball_subset_closedBall
    rw [← integral_add hAi hSi] at he
    rw [← he]
    apply setIntegral_congr_fun measurableSet_ball
    intro y hy
    dsimp only
    rw [hGy y hy]
    simp only [map_sub]
    ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_local_scalar_product {f η : Plane → ℝ} {S : Set Plane}
    (hS : IsOpen S) (hf : ContinuousOn f S) (hη : Continuous η)
    (hs : tsupport η⊆S) : Continuous (fun y ↦ f y*η y) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y∈tsupport η
  · exact ((hf y (hs hy)).continuousAt (hS.mem_nhds (hs hy))).mul hη.continuousAt
  · apply (continuousAt_const (y := (0:ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp [hz]

lemma C1_local_integration_by_parts {g ψ : Plane → ℝ} {S : Set Plane}
    (hS : IsOpen S) (hg : Continuous g) (hgc : ContDiffOn ℝ 1 g S)
    (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆S) (v : Plane) :
    (∫ y, fderiv ℝ g y v*ψ y)= -(∫ y,g y*fderiv ℝ ψ y v) := by
  have hdf : ContinuousOn (fun y ↦ fderiv ℝ g y v) S :=
    (hgc.continuousOn_fderiv_of_isOpen hS (by simp)).clm_apply continuousOn_const
  have hi₁ : Integrable (fun y ↦ fderiv ℝ g y v*ψ y) :=
    (continuous_local_scalar_product hS hdf hψ.continuous hs).integrable_of_hasCompactSupport hc.mul_left
  have hi₂ : Integrable (fun y ↦ g y*fderiv ℝ ψ y v) :=
    (hg.mul ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ v).mul_left
  have hi₃ : Integrable (fun y ↦ g y*ψ y) :=
    (hg.mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi₁ hi₂ hi₃
    (fun y hy ↦ ((hgc y (hs hy)).contDiffAt (hS.mem_nhds (hs hy))).differentiableAt (by simp))
    (fun _ _ ↦ (hψ.differentiable (by simp)).differentiableAt)
  simpa only [neg_neg] using congrArg Neg.neg hh.symm

lemma C1_mixed_test_identity {g ψ : Plane → ℝ} {S : Set Plane}
    (hS : IsOpen S) (hg : Continuous g) (hgc : ContDiffOn ℝ 1 g S)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆S)
    (v w : Plane) :
    (∫ y, ⟪gradient g y,w⟫*fderiv ℝ ψ y v)=
      (∫ y, ⟪gradient g y,v⟫*fderiv ℝ ψ y w) := by
  have hv : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ fderiv ℝ ψ y v) :=
    (hψ.fderiv_right (by simp)).clm_apply contDiff_const
  have hw : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ fderiv ℝ ψ y w) :=
    (hψ.fderiv_right (by simp)).clm_apply contDiff_const
  simp only [inner_gradient_left]
  rw [C1_local_integration_by_parts hS hg hgc (hv.of_le (by simp))
    (hc.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset (f := ψ) ℝ v).trans hs) w,
    C1_local_integration_by_parts hS hg hgc (hw.of_le (by simp))
    (hc.fderiv_apply ℝ w) ((tsupport_fderiv_apply_subset (f := ψ) ℝ w).trans hs) v]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y
  congr 1
  rw [fderiv_fderiv_apply hψ,fderiv_fderiv_apply hψ]
  exact (hψ.contDiffAt.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)) w v

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma indicator_inner_test_integral {S : Set Plane} (hS : MeasurableSet S)
    (U : Plane → Plane) (v : Plane) (ψ : Plane → ℝ) :
    (∫ y,⟪S.indicator U y,v⟫*ψ y)=(∫ y in S,⟪U y,v⟫*ψ y) := by
  rw [← integral_indicator hS]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : y∈S <;> simp [hy]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem LinearCMCEquation.scalar_derivative {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {p B : Plane → Plane} (hp : Continuous p) (hpb : ∀ y,‖p y‖≤1)
    {LA LB : ℝ≥0} (hA : LipschitzWith LA (fun y ↦ cmcJacobian (p y))) (hB : LipschitzWith LB B)
    (hAc : ContDiff ℝ 1 (fun y ↦ cmcJacobian (p y))) (hBc : ContDiff ℝ 1 B)
    {M R : ℝ} (hBb : ∀ y,‖B y‖≤M) (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hw : LinearCMCEquation g p B (Metric.ball 0 R)) (v : Plane) (hv : ‖v‖≤1) :
    ∃ (u : Lp ℝ 2 (volume : Measure Plane)) (U : Lp Plane 2 (volume : Measure Plane)),
      (u : Plane → ℝ)=ᵐ[volume.restrict (Metric.ball 0 (R/4))]
        (fun y ↦ fderiv ℝ g y v) ∧
      PlaneWeakGradient (Metric.ball 0 (R/4)) u U ∧
      (∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ⊆Metric.ball 0 (R/4) →
        (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (U y)-
          (fderiv ℝ B y v-fderiv ℝ (fun z ↦ cmcJacobian (p z)) y v (gradient g y))))=0) := by
  let S : Set Plane := Metric.ball 0 (R/4)
  obtain ⟨F,hF,hlin⟩ := hw.weak_derivative hg hp hpb hA hB hAc hBc hBb hR hgc v hv
  have hFmem : MemLp (S.indicator (F : Plane → Plane)) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr (Lp.memLp F)
  let U := hFmem.toLp (S.indicator (F : Plane → Plane))
  let b : ContDiffBump (0 : Plane) := ⟨R/4,R/2,by linarith,by linarith⟩
  let f : Plane → ℝ := fun y ↦ fderiv ℝ g y v*b y
  have hbs : tsupport b⊆Metric.ball 0 R := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  have hfc : Continuous f := continuous_local_scalar_product Metric.isOpen_ball
    ((hgc.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply continuousOn_const)
    b.continuous hbs
  have hfs : HasCompactSupport f := b.hasCompactSupport.mul_left
  have hfmem : MemLp f 2 volume := hfc.memLp_of_hasCompactSupport hfs
  let u := hfmem.toLp f
  have hfe (y : Plane) (hy : y∈S) : f y=fderiv ℝ g y v := by
    dsimp only [f]
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy),mul_one]
  refine ⟨u,U,?_,?_,?_⟩
  · filter_upwards [ae_restrict_of_ae hfmem.coeFn_toLp,ae_restrict_mem (measurableSet_ball : MeasurableSet S)] with y hy hs
    exact hy.trans (hfe y hs)
  · intro w ψ hψ hc hs
    have hψs : tsupport ψ⊆Metric.ball 0 R := hs.trans (Metric.ball_subset_ball (by linarith))
    calc
      _ = ∫ y,⟪S.indicator (F : Plane → Plane) y,w⟫*ψ y := by
        apply integral_congr_ae
        filter_upwards [hFmem.coeFn_toLp] with y hy
        rw [hy]
      _ = ∫ y in S,⟪F y,w⟫*ψ y := indicator_inner_test_integral measurableSet_ball _ _ _
      _ = -(∫ y,⟪gradient g y,w⟫*fderiv ℝ ψ y v) := hF w ψ (hψ.of_le (by simp)) hc hs
      _ = -(∫ y,⟪gradient g y,v⟫*fderiv ℝ ψ y w) := by
        rw [C1_mixed_test_identity Metric.isOpen_ball hg.continuous hgc hψ hc hψs v w]
      _ = -(∫ y,u y*fderiv ℝ ψ y w) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hfmem.coeFn_toLp] with y hy
        rw [hy,inner_gradient_left]
        by_cases hyS : y∈S
        · rw [hfe y hyS]
        · rw [fderiv_of_notMem_tsupport ℝ (fun h ↦ hyS (hs h)),zero_apply,mul_zero,mul_zero]
  · intro ψ hψ hc hs
    calc
      _ = ∫ y in S,fderiv ℝ ψ y (cmcJacobian (p y) (U y)-
          (fderiv ℝ B y v-fderiv ℝ (fun z ↦ cmcJacobian (p z)) y v (gradient g y))) :=
        (differential_integral_restrict hs _).symm
      _ = ∫ y in S,fderiv ℝ ψ y (cmcJacobian (p y) (F y)-
          (fderiv ℝ B y v-fderiv ℝ (fun z ↦ cmcJacobian (p z)) y v (gradient g y))) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae hFmem.coeFn_toLp,
          ae_restrict_mem (measurableSet_ball : MeasurableSet S)] with y hy hyS
        rw [hy,Set.indicator_of_mem hyS]
      _ = 0 := hlin ψ (hψ.of_le (by simp)) hc hs

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

lemma cmcJacobian_uniform_lipschitz : ∃ L : ℝ,0≤L ∧ ∀ p q : Plane,
    ‖p‖≤1 → ‖q‖≤1 → ‖cmcJacobian p-cmcJacobian q‖≤L*‖p-q‖ := by
  obtain ⟨L,hL⟩ := cmcJacobian_contDiff.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall (0 : Plane) (1 : ℝ)) (isCompact_closedBall (0 : Plane) (1 : ℝ))
  refine ⟨L,L.coe_nonneg,fun p q hp hq ↦ ?_⟩
  exact hL.norm_sub_le (by simpa using hp) (by simpa using hq)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_gradient_dist (g : Plane → ℝ) (x y : Plane) :
    dist (gradient g x) (gradient g y)=dist (fderiv ℝ g x) (fderiv ℝ g y) := by
  exact (InnerProductSpace.toDual ℝ Plane).symm.isometry.dist_eq _ _

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma C1_weak_gradient {f : Plane → ℝ} (hf : ContDiff ℝ 1 f)
    (S : Set Plane) : PlaneWeakGradient S f (gradient f) := by
  intro v ψ hψ hc _hs
  have hi₁ : Integrable (fun y ↦ fderiv ℝ f y v*ψ y) :=
    (((hf.continuous_fderiv (by simp)).clm_apply continuous_const).mul hψ.continuous).integrable_of_hasCompactSupport
      hc.mul_left
  have hi₂ : Integrable (fun y ↦ f y*fderiv ℝ ψ y v) :=
    (hf.continuous.mul ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ v).mul_left
  have hi₃ : Integrable (fun y ↦ f y*ψ y) :=
    (hf.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi₁ hi₂ hi₃
    (fun _ _ ↦ (hf.differentiable (by simp)).differentiableAt)
    (fun _ _ ↦ (hψ.differentiable (by simp)).differentiableAt)
  simpa only [inner_gradient_left,neg_neg] using congrArg Neg.neg hh.symm

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

lemma PlaneWeakGradient.unique {S : Set Plane} (hS : IsOpen S)
    {u : Plane → ℝ} {G H : Plane → Plane}
    (hG : LocallyIntegrable G volume) (hH : LocallyIntegrable H volume)
    (huG : PlaneWeakGradient S u G) (huH : PlaneWeakGradient S u H) :
    G=ᵐ[volume.restrict S] H := by
  have hz := hS.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hG.sub hH).locallyIntegrableOn S) (fun ψ hψ hc hs ↦ ?_)
  · change ∀ᵐ y ∂volume.restrict S, G y = H y
    rw [ae_restrict_iff' hS.measurableSet]
    filter_upwards [hz] with y hy hys
    exact sub_eq_zero.mp (hy hys)
  · have hiG := hG.integrable_smul_left_of_hasCompactSupport hψ.continuous hc
    have hiH := hH.integrable_smul_left_of_hasCompactSupport hψ.continuous hc
    simp only [Pi.sub_apply,smul_sub,integral_sub hiG hiH]
    apply sub_eq_zero.mpr
    apply ext_inner_left ℝ
    intro v
    rw [← integral_inner hiG v,← integral_inner hiH v]
    simp only [inner_smul_right]
    simp_rw [real_inner_comm (G _) v,real_inner_comm (H _) v]
    simpa only [mul_comm] using (huG v ψ hψ hc hs).trans (huH v ψ hψ hc hs).symm

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

lemma linear_cmc_source_holder {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g)
    {p B : Plane → Plane} {LA : ℝ≥0} (hA : LipschitzWith LA (fun y ↦ cmcJacobian (p y)))
    {R α DA DB Dg : ℝ} (hDA : 0≤DA) (hDB : 0≤DB) (hDg : 0≤Dg)
    (hAd : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      dist (fderiv ℝ (fun z ↦ cmcJacobian (p z)) x) (fderiv ℝ (fun z ↦ cmcJacobian (p z)) y)≤DA*(dist x y)^α)
    (hBd : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      dist (fderiv ℝ B x) (fderiv ℝ B y)≤DB*(dist x y)^α)
    (hgd : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      dist (fderiv ℝ g x) (fderiv ℝ g y)≤Dg*(dist x y)^α)
    {v : Plane} (hv : ‖v‖≤1) {x y : Plane} (hx : x∈Metric.ball (0 : Plane) R)
    (hy : y∈Metric.ball (0 : Plane) R) :
    ‖(fderiv ℝ B x v-fderiv ℝ (fun z ↦ cmcJacobian (p z)) x v (gradient g x))-
      (fderiv ℝ B y v-fderiv ℝ (fun z ↦ cmcJacobian (p z)) y v (gradient g y))‖≤
        (DB+DA*(K:ℝ)+(LA:ℝ)*Dg)*(dist x y)^α := by
  let A := fun z ↦ cmcJacobian (p z)
  have hb' : ‖fderiv ℝ B x v-fderiv ℝ B y v‖≤DB*(dist x y)^α := by
    calc
      _ = ‖(fderiv ℝ B x-fderiv ℝ B y) v‖ := rfl
      _ ≤ ‖fderiv ℝ B x-fderiv ℝ B y‖*‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (DB*(dist x y)^α)*1 := mul_le_mul (by simpa only [dist_eq_norm] using hBd x hx y hy) hv
        (norm_nonneg _) (mul_nonneg hDB (Real.rpow_nonneg (dist_nonneg) _))
      _ = _ := mul_one _
  have hAd' : ‖fderiv ℝ A x-fderiv ℝ A y‖≤DA*(dist x y)^α := by
    have hh := hAd x hx y hy
    rw [dist_eq_norm (fderiv ℝ (fun z ↦ cmcJacobian (p z)) x : Plane →L[ℝ] Plane →L[ℝ] Plane)
      (fderiv ℝ (fun z ↦ cmcJacobian (p z)) y : Plane →L[ℝ] Plane →L[ℝ] Plane)] at hh
    exact hh
  have ha' : ‖fderiv ℝ A x v-fderiv ℝ A y v‖≤DA*(dist x y)^α := by
    calc
      _ = ‖(fderiv ℝ A x-fderiv ℝ A y) v‖ := rfl
      _ ≤ ‖fderiv ℝ A x-fderiv ℝ A y‖*‖v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (DA*(dist x y)^α)*1 := mul_le_mul hAd' hv
        (norm_nonneg _) (mul_nonneg hDA (Real.rpow_nonneg (dist_nonneg) _))
      _ = _ := mul_one _
  have hag : ‖fderiv ℝ A y v‖≤(LA:ℝ) :=
    ((fderiv ℝ A y).le_opNorm v).trans
      ((mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hA) hv (norm_nonneg _) LA.coe_nonneg).trans_eq (mul_one _))
  have hgx : ‖gradient g x‖≤(K:ℝ) := by
    rw [plane_gradient_norm]; exact norm_fderiv_le_of_lipschitz ℝ hg
  have hgd' : ‖gradient g x-gradient g y‖≤Dg*(dist x y)^α := by
    rw [← dist_eq_norm,plane_gradient_dist]; exact hgd x hx y hy
  have hEq : fderiv ℝ A x v (gradient g x)-fderiv ℝ A y v (gradient g y)=
      (fderiv ℝ A x v-fderiv ℝ A y v) (gradient g x)+fderiv ℝ A y v (gradient g x-gradient g y) := by
    simp only [sub_apply,map_sub]; abel
  have he : ‖fderiv ℝ A x v (gradient g x)-fderiv ℝ A y v (gradient g y)‖≤
      (DA*(K:ℝ)+(LA:ℝ)*Dg)*(dist x y)^α := by
    rw [hEq]
    calc
      _ ≤ ‖(fderiv ℝ A x v-fderiv ℝ A y v) (gradient g x)‖+
          ‖fderiv ℝ A y v (gradient g x-gradient g y)‖ := norm_add_le _ _
      _ ≤ (DA*(dist x y)^α)*(K:ℝ)+(LA:ℝ)*(Dg*(dist x y)^α) := add_le_add
        (((fderiv ℝ A x v-fderiv ℝ A y v).le_opNorm _).trans
          (mul_le_mul ha' hgx (norm_nonneg _) (mul_nonneg hDA (Real.rpow_nonneg dist_nonneg _))))
        (((fderiv ℝ A y v).le_opNorm _).trans
          (by simpa only [mul_comm] using
            mul_le_mul hgd' hag (norm_nonneg _) (mul_nonneg hDg (Real.rpow_nonneg dist_nonneg _))))
      _ = _ := by ring
  calc
    _ = ‖(fderiv ℝ B x v-fderiv ℝ B y v)-
        (fderiv ℝ A x v (gradient g x)-fderiv ℝ A y v (gradient g y))‖ := by
      congr 1; dsimp only [A]; abel
    _ ≤ ‖fderiv ℝ B x v-fderiv ℝ B y v‖+
        ‖fderiv ℝ A x v (gradient g x)-fderiv ℝ A y v (gradient g y)‖ := norm_sub_le _ _
    _ ≤ DB*(dist x y)^α+(DA*(K:ℝ)+(LA:ℝ)*Dg)*(dist x y)^α := add_le_add hb' he
    _ = _ := by ring

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

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem LinearCMCEquation.directional_holder_C1 {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {p B : Plane → Plane} (hp : Continuous p) (hpb : ∀ y,‖p y‖≤1)
    {LA LB : ℝ≥0} (hA : LipschitzWith LA (fun y ↦ cmcJacobian (p y))) (hB : LipschitzWith LB B)
    (hAc : ContDiff ℝ 1 (fun y ↦ cmcJacobian (p y))) (hBc : ContDiff ℝ 1 B)
    {M R α DA DB Dg D₀ : ℝ} (hBb : ∀ y,‖B y‖≤M) (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hw : LinearCMCEquation g p B (Metric.ball 0 R)) (hα : 0<α) (hα1 : α≤1)
    (hDA : 0≤DA) (hDB : 0≤DB) (hDg : 0≤Dg) (hD₀ : 0≤D₀)
    (hAHolder : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D₀*(dist x y)^α)
    (hAd : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      dist (fderiv ℝ (fun z ↦ cmcJacobian (p z)) x) (fderiv ℝ (fun z ↦ cmcJacobian (p z)) y)≤DA*(dist x y)^α)
    (hBd : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      dist (fderiv ℝ B x) (fderiv ℝ B y)≤DB*(dist x y)^α)
    (hgd : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      dist (fderiv ℝ g x) (fderiv ℝ g y)≤Dg*(dist x y)^α)
    (v : Plane) (hv : ‖v‖≤1) :
    ∃ s L β : ℝ,0 < s ∧ s≤R ∧ 0≤L ∧ 0<β ∧ β≤1 ∧
      ContDiffOn ℝ 1 (fun y ↦ fderiv ℝ g y v) (Metric.ball 0 s) ∧
      ∀ x∈Metric.ball (0 : Plane) s,∀ y∈Metric.ball (0 : Plane) s,
        dist (fderiv ℝ (fun z ↦ fderiv ℝ g z v) x) (fderiv ℝ (fun z ↦ fderiv ℝ g z v) y)≤L*(dist x y)^β := by
  obtain ⟨G,C,hGc,hGb,hC,hGe,henergy⟩ := hw.gradient_difference_data hg hp hpb hA hB hBb hR hgc
  obtain ⟨u,U,hue,hug,hlin⟩ := hw.scalar_derivative hg hp hpb hA hB hAc hBc hBb hR hgc v hv
  let S : Plane → Plane := fun y ↦ fderiv ℝ B y v-fderiv ℝ (fun z ↦ cmcJacobian (p z)) y v (G y)
  have hSc : Continuous S := ((hBc.continuous_fderiv (by simp)).clm_apply continuous_const).sub
    (((hAc.continuous_fderiv (by simp)).clm_apply continuous_const).clm_apply hGc)
  have hsub : Metric.ball (0 : Plane) (R/4)⊆Metric.ball 0 R := Metric.ball_subset_ball (by linarith)
  have hGe' (y : Plane) (hy : y∈Metric.ball (0 : Plane) (R/4)) : G y=gradient g y := by
    apply hGe
    have hy' : ‖y‖<R/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hy
    linarith
  have hSH : ∀ x∈Metric.ball (0 : Plane) (R/4),∀ y∈Metric.ball (0 : Plane) (R/4),
      ‖S x-S y‖≤(DB+DA*(K:ℝ)+(LA:ℝ)*Dg)*(dist x y)^α := by
    intro x hx y hy
    dsimp only [S]
    rw [hGe' x hx,hGe' y hy]
    exact linear_cmc_source_holder hg hA hDA hDB hDg hAd hBd hgd hv (hsub hx) (hsub hy)
  have hd : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 (R/4) → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (U y)-S y))=0 := by
    intro ψ hψ hc hs
    rw [← hlin ψ hψ hc hs]
    apply integral_congr_ae
    exact Eventually.of_forall fun y ↦ by
      dsimp only [S]
      by_cases hy : y∈Metric.ball (0 : Plane) (R/4)
      · rw [hGe' y hy]
      · rw [fderiv_of_notMem_tsupport ℝ (fun hy' ↦ hy (hs hy'))]; rfl
  obtain ⟨U',s,L,β,hs,hsR,hL,hβ,hβ1,hUc,hUe,hUh⟩ :=
    forced_cmc_linearized_holder_gradient hp hpb (by linarith : 0<R/4) hα hα1 hD₀
      (fun x hx y hy ↦ hAHolder x (hsub hx) y (hsub hy)) hSc
      (by positivity : 0≤DB+DA*(K:ℝ)+(LA:ℝ)*Dg) hSH u U hug hd
  have hsub' : Metric.ball (0 : Plane) s⊆Metric.ball 0 (R/4) := Metric.ball_subset_ball (by linarith)
  have hw' : PlaneWeakGradient (Metric.ball 0 s) (fun y ↦ fderiv ℝ g y v) U' :=
    (hug.mono hsub').local_congr measurableSet_ball
      (ae_restrict_of_ae_restrict_of_subset hsub' hue.symm) hUe
  have hfc : ContinuousOn (fun y ↦ fderiv ℝ g y v) (Metric.ball 0 s) :=
    ((hgc.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by simp)).clm_apply continuousOn_const).mono (hsub'.trans hsub)
  exact ⟨s/4,L,β,by positivity,by linarith,hL,hβ,hβ1,hw'.holder_C1 hs hfc hUc hUh⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
namespace CubicTorus

lemma LinearCMCEquation.mono {g : Plane → ℝ} {p B : Plane → Plane} {U W : Set Plane}
    (hw : LinearCMCEquation g p B U) (hW : W⊆U) : LinearCMCEquation g p B W :=
  fun ψ hψ hc hs ↦ hw ψ hψ hc (hs.trans hW)

lemma LinearCMCEquation.congr {g g' : Plane → ℝ} {p p' B B' : Plane → Plane} {U : Set Plane}
    (hU : IsOpen U) (hw : LinearCMCEquation g p B U)
    (hg : EqOn g' g U) (hp : EqOn p' p U) (hB : EqOn B' B U) : LinearCMCEquation g' p' B' U := by
  intro ψ hψ hc hs
  rw [← hw ψ hψ hc hs]
  apply integral_congr_ae
  exact Eventually.of_forall fun y ↦ by
    dsimp only
    by_cases hy : y∈U
    · have he : g'=ᶠ[𝓝 y]g := by
        filter_upwards [hU.mem_nhds hy] with z hz
        exact hg hz
      have hG : gradient g' y=gradient g y := congrArg
        (fun L : Plane →L[ℝ] ℝ ↦ (InnerProductSpace.toDual ℝ Plane).symm L) he.fderiv_eq
      rw [hG,hp hy,hB hy]
    · rw [fderiv_of_notMem_tsupport ℝ (fun h ↦ hy (hs h))]; rfl

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma HolderNear.continuousAt [NormedSpace ℝ E] [NormedSpace ℝ F]
    {f : E → F} {x : E} (hf : HolderNear f x) : ContinuousAt f x := by
  obtain ⟨r,α,C,hr,hα,hα1,hC,hH⟩ := hf
  rw [ContinuousAt,tendsto_iff_dist_tendsto_zero]
  have hd : Tendsto (fun y : E ↦ dist y x) (𝓝 x) (𝓝 0) := by
    simpa only [id_eq,dist_self] using ((continuous_id : Continuous (fun y : E ↦ y)).dist (continuous_const (y := x))).tendsto x
  have hlim : Tendsto (fun y : E ↦ C*(dist y x)^α) (𝓝 x) (𝓝 0) := by
    simpa only [Real.zero_rpow hα.ne',mul_zero] using (hd.rpow_const (Or.inr hα.le)).const_mul C
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) ?_ hlim
  filter_upwards [Metric.ball_mem_nhds x hr] with y hy
  exact hH y hy x (Metric.mem_ball_self hr)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma HolderNear.eventually [NormedSpace ℝ E] [NormedSpace ℝ F]
    {f : E → F} {x : E} (hf : HolderNear f x) : ∀ᶠ y in 𝓝 x,HolderNear f y := by
  obtain ⟨r,α,C,hr,hα,hα1,hC,hH⟩ := hf
  filter_upwards [Metric.ball_mem_nhds x (by linarith : 0 < r/2)] with y hy
  have hsub : Metric.ball y (r/2)⊆Metric.ball x r := by
    intro z hz
    have hz' := Metric.mem_ball.mp hz
    have hy' := Metric.mem_ball.mp hy
    have ht := dist_triangle z y x
    exact Metric.mem_ball.mpr (by linarith)
  exact ⟨r/2,α,C,by linarith,hα,hα1,hC,fun z hz w hw ↦ hH z (hsub hz) w (hsub hw)⟩

lemma HolderNear.contDiffAt_zero {f : E → F} {x : E} (hf : HolderNear f x) : ContDiffAt ℝ 0 f x := by
  obtain ⟨s,hS,hsc,hs⟩ := eventually_nhds_iff.mp hf.eventually
  exact _root_.contDiffAt_zero.mpr ⟨s,hsc.mem_nhds hs,fun y hy ↦ (hS y hy).continuousAt.continuousWithinAt⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma HolderNear.congr [NormedSpace ℝ E] [NormedSpace ℝ F]
    {f g : E → F} {x : E} (hf : HolderNear f x) (he : f=ᶠ[𝓝 x]g) : HolderNear g x := by
  obtain ⟨r,α,C,hr,hα,hα1,hC,hH⟩ := hf
  obtain ⟨s,hs,hsE⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨min r s,α,C,lt_min hr hs,hα,hα1,hC,?_⟩
  intro y hy z hz
  have hyR := (Metric.ball_subset_ball (min_le_left r s)) hy
  have hzR := (Metric.ball_subset_ball (min_le_left r s)) hz
  rw [← hsE ((Metric.ball_subset_ball (min_le_right r s)) hy),
    ← hsE ((Metric.ball_subset_ball (min_le_right r s)) hz)]
  exact hH y hyR z hzR

lemma ContDiffAt.holderNear {f : E → F} {x : E} (hf : ContDiffAt ℝ 1 f x) : HolderNear f x := by
  obtain ⟨C,S,hS,hLip⟩ := hf.exists_lipschitzOnWith
  obtain ⟨r,hr,hrS⟩ := Metric.mem_nhds_iff.mp hS
  refine ⟨r,1,C,hr,by norm_num,le_rfl,C.coe_nonneg,?_⟩
  intro y hy z hz
  simpa only [Real.rpow_one] using hLip.dist_le_mul y (hrS hy) z (hrS hz)

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G] in
lemma HolderNear.prodMk [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]
    {f : E → F} {g : E → G} {x : E}
    (hf : HolderNear f x) (hg : HolderNear g x) : HolderNear (fun y ↦ (f y,g y)) x := by
  obtain ⟨r,α,C,hr,hα,hα1,hC,hH⟩ := hf
  obtain ⟨s,β,D,hs,hβ,hβ1,hD,hJ⟩ := hg
  let ρ := min (min r s) (1/2)
  have hρ : 0<ρ := lt_min (lt_min hr hs) (by norm_num)
  have hρr : ρ ≤ r := (min_le_left _ _).trans (min_le_left _ _)
  have hρs : ρ≤ s := (min_le_left _ _).trans (min_le_right _ _)
  have hρα : ρ≤1/2 := min_le_right _ _
  refine ⟨ρ,min α β,C+D,hρ,lt_min hα hβ,(min_le_left _ _).trans hα1,add_nonneg hC hD,?_⟩
  intro y hy z hz
  have hd : dist y z≤1 := by
    have hy' := Metric.mem_ball.mp hy
    have hz' := Metric.mem_ball.mp hz
    have ht := dist_triangle_right y z x
    linarith
  have hhα : (dist y z)^α≤(dist y z)^(min α β) :=
    Real.rpow_le_rpow_of_exponent_ge' dist_nonneg hd (le_min hα.le hβ.le) (min_le_left _ _)
  have hhβ : (dist y z)^β≤(dist y z)^(min α β) :=
    Real.rpow_le_rpow_of_exponent_ge' dist_nonneg hd (le_min hα.le hβ.le) (min_le_right _ _)
  rw [Prod.dist_eq]
  apply max_le
  · exact ((hH y ((Metric.ball_subset_ball hρr) hy) z ((Metric.ball_subset_ball hρr) hz)).trans
      (mul_le_mul_of_nonneg_left hhα hC)).trans
        (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg dist_nonneg _))
  · exact ((hJ y ((Metric.ball_subset_ball hρs) hy) z ((Metric.ball_subset_ball hρs) hz)).trans
      (mul_le_mul_of_nonneg_left hhβ hD)).trans
        (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg dist_nonneg _))

lemma ContDiffAt.comp_holderNear {f : E → F} {g : F → G} {x : E}
    (hg : ContDiffAt ℝ 1 g (f x)) (hf : HolderNear f x) : HolderNear (g ∘ f) x := by
  obtain ⟨K,S,hS,hLip⟩ := hg.exists_lipschitzOnWith
  have hfcont := hf.continuousAt
  obtain ⟨r,α,C,hr,hα,hα1,hC,hH⟩ := hf
  obtain ⟨s,hs,hsS⟩ := Metric.mem_nhds_iff.mp (hfcont hS)
  refine ⟨min r s,α,(K:ℝ)*C,lt_min hr hs,hα,hα1,mul_nonneg K.coe_nonneg hC,?_⟩
  intro y hy z hz
  calc
    _ ≤ (K:ℝ)*dist (f y) (f z) := hLip.dist_le_mul (f y)
      (hsS ((Metric.ball_subset_ball (min_le_right r s)) hy)) (f z)
      (hsS ((Metric.ball_subset_ball (min_le_right r s)) hz))
    _ ≤ (K:ℝ)*(C*(dist y z)^α) := mul_le_mul_of_nonneg_left
      (hH y ((Metric.ball_subset_ball (min_le_left r s)) hy)
        z ((Metric.ball_subset_ball (min_le_left r s)) hz)) K.coe_nonneg
    _ = _ := by ring

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus

variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma HolderJet.congr {n : ℕ} {f g : E → F} {x : E} (hf : HolderJet n f x)
    (he : f=ᶠ[𝓝 x]g) : HolderJet n g x := by
  induction n generalizing F with
  | zero => exact hf.congr he
  | succ n ih =>
    exact ⟨hf.1.congr_of_eventuallyEq he.symm,ih hf.2 he.fderiv⟩

lemma HolderJet.holderNear {n : ℕ} {f : E → F} {x : E} (hf : HolderJet n f x) : HolderNear f x := by
  cases n with
  | zero => exact hf
  | succ n => exact ContDiffAt.holderNear hf.1

lemma HolderJet.pred {n : ℕ} {f : E → F} {x : E} (hf : HolderJet (n+1) f x) : HolderJet n f x := by
  induction n generalizing F with
  | zero => exact ContDiffAt.holderNear hf.1
  | succ n ih => exact ⟨hf.1,ih hf.2⟩

lemma HolderJet.of_le {n m : ℕ} {f : E → F} {x : E} (hf : HolderJet n f x) (hm : m≤n) : HolderJet m f x := by
  induction n with
  | zero => simpa only [Nat.le_zero.mp hm] using hf
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hm with he|he
    · simpa only [he] using hf
    · exact ih hf.pred (Nat.le_of_lt_succ he)

lemma HolderJet.contDiffAt {n : ℕ} {f : E → F} {x : E} (hf : HolderJet n f x) : ContDiffAt ℝ n f x := by
  induction n generalizing F with
  | zero => exact HolderNear.contDiffAt_zero hf
  | succ n ih =>
    apply contDiffAt_succ_iff_hasFDerivAt.mpr
    refine ⟨fderiv ℝ f,?_,ih hf.2⟩
    have hdiff : ∀ᶠ y in 𝓝 x,DifferentiableAt ℝ f y :=
      (hf.1.eventually (by simp)).mono fun _ hy ↦ hy.differentiableAt_one
    exact ⟨{y|DifferentiableAt ℝ f y},hdiff,fun y hy ↦ hy.hasFDerivAt⟩

lemma ContDiffAt.holderJet {n : ℕ} {f : E → F} {x : E} (hf : ContDiffAt ℝ (n+1) f x) : HolderJet n f x := by
  induction n generalizing F with
  | zero => exact ContDiffAt.holderNear hf
  | succ n ih =>
    refine ⟨hf.of_le (by norm_cast; omega),?_⟩
    exact ih (hf.fderiv_right (by norm_cast))

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus
variable {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma HolderJet.eventually {n : ℕ} {f : E → F} {x : E} (hf : HolderJet n f x) :
    ∀ᶠ y in 𝓝 x,HolderJet n f y := by
  induction n generalizing F with
  | zero => exact HolderNear.eventually hf
  | succ n ih => exact (hf.1.eventually (by simp)).and (ih hf.2)

lemma HolderJet.clm_comp {n : ℕ} {f : E → F} {x : E} (hf : HolderJet n f x)
    (L : F →L[ℝ] G) : HolderJet n (L ∘ f) x := by
  induction n generalizing F G with
  | zero => exact ContDiffAt.comp_holderNear L.contDiff.contDiffAt hf
  | succ n ih =>
    refine ⟨L.contDiff.contDiffAt.comp x hf.1,?_⟩
    apply (ih hf.2 (ContinuousLinearMap.compL ℝ E F G L)).congr
    filter_upwards [hf.1.eventually (by simp)] with y hy
    exact ((L.hasFDerivAt).comp y hy.differentiableAt_one.hasFDerivAt).fderiv.symm

lemma HolderJet.prodMk {n : ℕ} {f : E → F} {g : E → G} {x : E}
    (hf : HolderJet n f x) (hg : HolderJet n g x) : HolderJet n (fun y ↦ (f y,g y)) x := by
  induction n generalizing F G with
  | zero => exact HolderNear.prodMk hf hg
  | succ n ih =>
    refine ⟨hf.1.prodMk hg.1,?_⟩
    have hh := (ih hf.2 hg.2).clm_comp
      (ContinuousLinearMap.prodₗᵢ ℝ (E := E) (F := F) (G := G)).toContinuousLinearEquiv.toContinuousLinearMap
    apply hh.congr
    filter_upwards [hf.1.eventually (by simp),hg.1.eventually (by simp)] with y hy hz
    exact (hy.differentiableAt_one.fderiv_prodMk hz.differentiableAt_one).symm

lemma HolderJet.smooth_comp {n : ℕ} {f : E → F} {g : F → G} {x : E}
    (hf : HolderJet n f x) (hg : ContDiff ℝ (⊤ : ℕ∞) g) : HolderJet n (g ∘ f) x := by
  induction n generalizing E F G with
  | zero => exact ContDiffAt.comp_holderNear (hg.of_le (by simp)).contDiffAt hf
  | succ n ih =>
    refine ⟨(hg.of_le (by simp)).contDiffAt.comp x hf.1,?_⟩
    have hDg : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ g) := hg.fderiv_right (by simp)
    have hpair := (ih hf.pred hDg).prodMk hf.2
    have hcomp : ContDiff ℝ (⊤ : ℕ∞)
        (fun p : (F →L[ℝ] G)×(E →L[ℝ] F) ↦ p.1.comp p.2) := contDiff_fst.clm_comp contDiff_snd
    apply (ih hpair hcomp).congr
    filter_upwards [hf.1.eventually (by simp)] with y hy
    exact (fderiv_comp y (hg.differentiable (by simp) (f y)) hy.differentiableAt_one).symm

lemma HolderJet.const {n : ℕ} {x : E} (c : F) : HolderJet n (fun _ : E ↦ c) x :=
  ContDiffAt.holderJet contDiffAt_const

lemma HolderJet.sub {n : ℕ} {f g : E → F} {x : E}
    (hf : HolderJet n f x) (hg : HolderJet n g x) : HolderJet n (fun y ↦ f y-g y) x :=
  (hf.prodMk hg).smooth_comp (contDiff_fst.sub contDiff_snd)

lemma HolderJet.clm_apply {n : ℕ} {f : E → F →L[ℝ] G} {g : E → F} {x : E}
    (hf : HolderJet n f x) (hg : HolderJet n g x) : HolderJet n (fun y ↦ f y (g y)) x :=
  (hf.prodMk hg).smooth_comp (contDiff_fst.clm_apply contDiff_snd)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_decompose (v : Plane) : v=v 0 • EuclideanSpace.single 0 (1 : ℝ)+
    v 1 • EuclideanSpace.single 1 (1 : ℝ) := by
  ext i
  fin_cases i <;> simp

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace CubicTorus
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma HolderJet.plane_clm {n : ℕ} {A : E → Plane →L[ℝ] F} {x : E}
    (h₀ : HolderJet n (fun y ↦ A y (EuclideanSpace.single 0 1)) x)
    (h₁ : HolderJet n (fun y ↦ A y (EuclideanSpace.single 1 1)) x) : HolderJet n A x := by
  let e₀ : Plane →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ Plane) (EuclideanSpace.single 0 1)
  let e₁ : Plane →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ Plane) (EuclideanSpace.single 1 1)
  let T : F×F → Plane →L[ℝ] F := fun q ↦ e₀.smulRight q.1+e₁.smulRight q.2
  have hT : ContDiff ℝ (⊤ : ℕ∞) T :=
    (contDiff_const.smulRight contDiff_fst).add (contDiff_const.smulRight contDiff_snd)
  apply ((h₀.prodMk h₁).smooth_comp hT).congr
  exact Eventually.of_forall fun y ↦ by
    apply ContinuousLinearMap.ext
    intro v
    change e₀ v • A y (EuclideanSpace.single 0 1)+e₁ v • A y (EuclideanSpace.single 1 1)=A y v
    have he₀ : e₀ v=v 0 := by simp [e₀,EuclideanSpace.inner_single_left]
    have he₁ : e₁ v=v 1 := by simp [e₁,EuclideanSpace.inner_single_left]
    rw [he₀,he₁]
    conv_rhs => rw [plane_decompose v]
    simp

lemma HolderJet.directional {n : ℕ} {f : Plane → ℝ} {x : Plane}
    (hf : HolderJet (n+1) f x) (v : Plane) : HolderJet n (fun y ↦ fderiv ℝ f y v) x :=
  hf.2.clm_apply (HolderJet.const v)

lemma HolderJet.of_directionals {n : ℕ} {f : Plane → ℝ} {x : Plane}
    (hf : ContDiffAt ℝ 1 f x)
    (h₀ : HolderJet n (fun y ↦ fderiv ℝ f y (EuclideanSpace.single 0 1)) x)
    (h₁ : HolderJet n (fun y ↦ fderiv ℝ f y (EuclideanSpace.single 1 1)) x) : HolderJet (n+1) f x :=
  ⟨hf,HolderJet.plane_clm h₀ h₁⟩

lemma HolderJet.gradient {n : ℕ} {f : Plane → ℝ} {x : Plane}
    (hf : HolderJet (n+1) f x) : HolderJet n (gradient f) x :=
  hf.2.clm_comp (InnerProductSpace.toDual ℝ Plane).symm.toContinuousLinearEquiv.toContinuousLinearMap

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_LinearCMCEquationNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus
variable {E F G H I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup I] [NormedSpace ℝ I]

lemma HolderNear.common_four {f : E → F} {g : E → G} {h : E → H} {i : E → I} {x : E}
    (hf : HolderNear f x) (hg : HolderNear g x) (hh : HolderNear h x) (hi : HolderNear i x) :
    ∃ r α C : ℝ,0 < r ∧ 0<α ∧ α≤1 ∧ 0≤C ∧
      ∀ y∈Metric.ball x r,∀ z∈Metric.ball x r,
        dist (f y) (f z)≤C*(dist y z)^α ∧ dist (g y) (g z)≤C*(dist y z)^α ∧
        dist (h y) (h z)≤C*(dist y z)^α ∧ dist (i y) (i z)≤C*(dist y z)^α := by
  obtain ⟨r,α,C,hr,hα,hα1,hC,hH⟩ := hf.prodMk (hg.prodMk (hh.prodMk hi))
  refine ⟨r,α,C,hr,hα,hα1,hC,?_⟩
  intro y hy z hz
  simpa only [Prod.dist_eq,max_le_iff] using hH y hy z hz

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem LinearCMCEquation.holderJet_two {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {p B : Plane → Plane} (hp : Continuous p) (hpb : ∀ y,‖p y‖≤1)
    {LA LB : ℝ≥0} (hA : LipschitzWith LA (fun y ↦ cmcJacobian (p y))) (hB : LipschitzWith LB B)
    (hAc : ContDiff ℝ 1 (fun y ↦ cmcJacobian (p y))) (hBc : ContDiff ℝ 1 B)
    {M R : ℝ} (hBb : ∀ y,‖B y‖≤M) (hR : 0<R)
    (hgc : ContDiffOn ℝ 1 g (Metric.ball 0 R))
    (hw : LinearCMCEquation g p B (Metric.ball 0 R))
    (hAJ : HolderJet 1 (fun y ↦ cmcJacobian (p y)) 0)
    (hBJ : HolderJet 1 B 0) (hgJ : HolderJet 1 g 0) : HolderJet 2 g 0 := by
  obtain ⟨r,α,C,hr,hα,hα1,hC,hcommon⟩ :=
    HolderNear.common_four hAJ.holderNear (HolderJet.holderNear hAJ.2)
      (HolderJet.holderNear hBJ.2) (HolderJet.holderNear hgJ.2)
  let s := min r R
  have hs : 0 < s := lt_min hr hR
  have hsr : s ≤ r := min_le_left _ _
  have hsR : s≤R := min_le_right _ _
  have hcommon' (x : Plane) (hx : x∈Metric.ball (0 : Plane) s)
      (y : Plane) (hy : y∈Metric.ball (0 : Plane) s) :=
    hcommon x ((Metric.ball_subset_ball hsr) hx) y ((Metric.ball_subset_ball hsr) hy)
  have hd (v : Plane) (hv : ‖v‖≤1) : HolderJet 1 (fun y ↦ fderiv ℝ g y v) 0 := by
    obtain ⟨t,L,β,ht,_,hL,hβ,hβ1,hc,hh⟩ :=
      (hw.mono (Metric.ball_subset_ball hsR)).directional_holder_C1 hg hp hpb hA hB hAc hBc hBb hs
        (hgc.mono (Metric.ball_subset_ball hsR)) hα hα1 hC hC hC hC
        (fun x hx y hy ↦ by simpa only [dist_eq_norm] using (hcommon' x hx y hy).1)
        (fun x hx y hy ↦ (hcommon' x hx y hy).2.1)
        (fun x hx y hy ↦ (hcommon' x hx y hy).2.2.1)
        (fun x hx y hy ↦ (hcommon' x hx y hy).2.2.2) v hv
    exact ⟨(hc 0 (Metric.mem_ball_self ht)).contDiffAt (Metric.ball_mem_nhds 0 ht),
      t,β,L,ht,hβ,hβ1,hL,hh⟩
  exact HolderJet.of_directionals hgJ.1
    (hd (EuclideanSpace.single 0 1) (by simp)) (hd (EuclideanSpace.single 1 1) (by simp))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma contDiff_local_vector_cutoff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Plane → F} {η : Plane → ℝ} {S : Set Plane} {n : WithTop ℕ∞}
    (hS : IsOpen S) (hf : ContDiffOn ℝ n f S) (hη : ContDiff ℝ n η)
    (hs : tsupport η⊆S) : ContDiff ℝ n (fun y ↦ η y • f y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y∈tsupport η
  · exact hη.contDiffAt.smul ((hf y (hs hy)).contDiffAt (hS.mem_nhds (hs hy)))
  · apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp [hz]

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology NNReal
namespace CubicTorus
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma compact_C1_lipschitz {f : E → F} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ∃ K : ℝ≥0,LipschitzWith K f := by
  obtain ⟨C,hC⟩ := (hc.fderiv ℝ).exists_bound_of_continuous (hf.continuous_fderiv (by simp))
  refine ⟨Real.toNNReal C,lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable (by simp)) fun x ↦ ?_⟩
  apply NNReal.coe_le_coe.mp
  exact (hC x).trans (Real.le_coe_toNNReal C)

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology NNReal
namespace CubicTorus

lemma HolderJet.extension {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} {f : Plane → F} (hf : HolderJet (n+1) f 0) :
    ∃ (f' : Plane → F) (K : ℝ≥0) (M : ℝ),
      ContDiff ℝ (n+1) f' ∧ HasCompactSupport f' ∧ LipschitzWith K f' ∧
      (∀ y,‖f' y‖≤M) ∧ (∀ y,‖f' y‖≤‖f y‖) ∧
      f'=ᶠ[𝓝 0]f ∧ HolderJet (n+1) f' 0 := by
  obtain ⟨r,hr,hjets⟩ := Metric.mem_nhds_iff.mp hf.eventually
  have hfc : ContDiffOn ℝ (n+1) f (Metric.ball 0 r) := fun y hy ↦
    (hjets hy).contDiffAt.contDiffWithinAt
  let b : ContDiffBump (0 : Plane) := ⟨r/2,3*r/4,by linarith,by linarith⟩
  have hbs : tsupport b⊆Metric.ball 0 r := by
    rw [b.tsupport_eq]
    exact Metric.closedBall_subset_ball (by dsimp [b]; linarith)
  let f' : Plane → F := fun y ↦ b y • f y
  have hc : ContDiff ℝ (n+1) f' := contDiff_local_vector_cutoff Metric.isOpen_ball hfc b.contDiff hbs
  have hcs : HasCompactSupport f' := b.hasCompactSupport.smul_right
  obtain ⟨K,hK⟩ := compact_C1_lipschitz (hc.of_le (by norm_cast; omega)) hcs
  obtain ⟨M,hM⟩ := hcs.exists_bound_of_continuous hc.continuous
  have he : f'=ᶠ[𝓝 0]f := by
    filter_upwards [Metric.ball_mem_nhds (0 : Plane) (by linarith : 0 < r/2)] with y hy
    dsimp only [f']
    rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hy),one_smul]
  refine ⟨f',K,M,hc,hcs,hK,hM,?_,he,hf.congr he.symm⟩
  intro y
  dsimp only [f']
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg b.nonneg]
  exact mul_le_of_le_one_left (norm_nonneg _) b.le_one

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma LinearCMCEquationNear.congr {g g' : Plane → ℝ} {p p' B B' : Plane → Plane}
    (hw : LinearCMCEquationNear g p B)
    (hg : g'=ᶠ[𝓝 0]g) (hp : p'=ᶠ[𝓝 0]p) (hB : B'=ᶠ[𝓝 0]B) : LinearCMCEquationNear g' p' B' := by
  obtain ⟨R,hR,hw⟩ := hw
  obtain ⟨r,hr,he⟩ := Metric.mem_nhds_iff.mp (hg.and (hp.and hB))
  refine ⟨min r R,lt_min hr hR,?_⟩
  have hsub : Metric.ball (0 : Plane) (min r R)⊆Metric.ball 0 r := Metric.ball_subset_ball (min_le_left _ _)
  exact (hw.mono (Metric.ball_subset_ball (min_le_right _ _))).congr Metric.isOpen_ball
    (fun _ hy ↦ (he (hsub hy)).1) (fun _ hy ↦ (he (hsub hy)).2.1) (fun _ hy ↦ (he (hsub hy)).2.2)

lemma cmc_symbol_lipschitz {p : Plane → Plane} {K : ℝ≥0}
    (hp : LipschitzWith K p) (hpb : ∀ y,‖p y‖≤1) :
    ∃ L : ℝ≥0,LipschitzWith L (fun y ↦ cmcJacobian (p y)) := by
  obtain ⟨L,hL,hLip⟩ := cmcJacobian_uniform_lipschitz
  let L' : ℝ≥0 := ⟨L*(K:ℝ),mul_nonneg hL K.coe_nonneg⟩
  refine ⟨L',?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    _ ≤ L*dist (p x) (p y) := by simpa only [dist_eq_norm] using hLip (p x) (p y) (hpb x) (hpb y)
    _ ≤ L*((K:ℝ)*dist x y) := mul_le_mul_of_nonneg_left (hp.dist_le_mul x y) hL
    _ = _ := by change L*((K:ℝ)*dist x y)=L*(K:ℝ)*dist x y; ring

theorem LinearCMCEquationNear.holderJet_two {g : Plane → ℝ} {p B : Plane → Plane}
    (hw : LinearCMCEquationNear g p B) (hpb : ∀ y,‖p y‖≤1)
    (hgJ : HolderJet 1 g 0) (hpJ : HolderJet 1 p 0) (hBJ : HolderJet 1 B 0) : HolderJet 2 g 0 := by
  obtain ⟨g',K,Mg,hgc,_,hg,_,_,hge,hgJ'⟩ := hgJ.extension
  obtain ⟨p',Kp,Mp,hpc,_,hp,_,hpbd,hpe,hpJ'⟩ := hpJ.extension
  obtain ⟨B',KB,MB,hBc,_,hB,hBb,_,hBe,hBJ'⟩ := hBJ.extension
  have hpb' (y : Plane) : ‖p' y‖≤1 := (hpbd y).trans (hpb y)
  obtain ⟨LA,hA⟩ := cmc_symbol_lipschitz hp hpb'
  have hAc : ContDiff ℝ 1 (fun y ↦ cmcJacobian (p' y)) :=
    (cmcJacobian_contDiff.of_le (by simp)).comp hpc
  obtain ⟨R,hR,hw'⟩ := hw.congr hge hpe hBe
  have hh := hw'.holderJet_two hg hpc.continuous hpb' hA hB hAc hBc hBb hR hgc.contDiffOn
    (hpJ'.smooth_comp cmcJacobian_contDiff) hBJ' hgJ'
  exact hh.congr hge

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem LinearCMCEquation.classical_derivative {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {p B : Plane → Plane} (hp : Continuous p) (hpb : ∀ y,‖p y‖≤1)
    {LA LB : ℝ≥0} (hA : LipschitzWith LA (fun y ↦ cmcJacobian (p y))) (hB : LipschitzWith LB B)
    (hAc : ContDiff ℝ 1 (fun y ↦ cmcJacobian (p y))) (hBc : ContDiff ℝ 1 B)
    {M R : ℝ} (hBb : ∀ y,‖B y‖≤M) (hR : 0<R) (hgc : ContDiff ℝ 2 g)
    (hw : LinearCMCEquation g p B (Metric.ball 0 R)) (v : Plane) (hv : ‖v‖≤1) :
    LinearCMCEquation (fun y ↦ fderiv ℝ g y v) p
      (fun y ↦ fderiv ℝ B y v-fderiv ℝ (fun z ↦ cmcJacobian (p z)) y v (gradient g y))
      (Metric.ball 0 (R/4)) := by
  obtain ⟨u,U,hue,hug,hlin⟩ := hw.scalar_derivative hg hp hpb hA hB hAc hBc hBb hR
    (hgc.of_le (by norm_num)).contDiffOn v hv
  let d : Plane → ℝ := fun y ↦ fderiv ℝ g y v
  have hdc : ContDiff ℝ 1 d := (hgc.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hgradc : Continuous (gradient d) :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp (hdc.continuous_fderiv (by simp))
  have hdu : PlaneWeakGradient (Metric.ball 0 (R/4)) d U :=
    hug.local_congr measurableSet_ball hue.symm (EventuallyEq.rfl)
  have hUeq := PlaneWeakGradient.unique Metric.isOpen_ball
    ((Lp.memLp U).locallyIntegrable (by norm_num)) hgradc.locallyIntegrable hdu (C1_weak_gradient hdc _)
  intro ψ hψ hc hs
  rw [← hlin ψ hψ hc hs]
  apply integral_congr_ae
  have he := (ae_restrict_iff' measurableSet_ball).mp hUeq
  filter_upwards [he] with y hy
  by_cases hys : y∈Metric.ball (0 : Plane) (R/4)
  · rw [hy hys]
  · rw [fderiv_of_notMem_tsupport ℝ (fun h ↦ hys (hs h))]; rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem LinearCMCEquationNear.derivative {g : Plane → ℝ} {p B : Plane → Plane}
    (hw : LinearCMCEquationNear g p B) (hpb : ∀ y,‖p y‖≤1)
    (hgJ : HolderJet 2 g 0) (hpJ : HolderJet 1 p 0) (hBJ : HolderJet 1 B 0)
    (v : Plane) (hv : ‖v‖≤1) :
    LinearCMCEquationNear (fun y ↦ fderiv ℝ g y v) p (linearCMCSource g p B v) := by
  obtain ⟨g',K,Mg,hgc,_,hg,_,_,hge,_⟩ := hgJ.extension
  obtain ⟨p',Kp,Mp,hpc,_,hp,_,hpbd,hpe,_⟩ := hpJ.extension
  obtain ⟨B',KB,MB,hBc,_,hB,hBb,_,hBe,_⟩ := hBJ.extension
  have hpb' (y : Plane) : ‖p' y‖≤1 := (hpbd y).trans (hpb y)
  obtain ⟨LA,hA⟩ := cmc_symbol_lipschitz hp hpb'
  have hAc : ContDiff ℝ 1 (fun y ↦ cmcJacobian (p' y)) :=
    (cmcJacobian_contDiff.of_le (by simp)).comp hpc
  obtain ⟨R,hR,hw'⟩ := hw.congr hge hpe hBe
  have hd' : LinearCMCEquationNear (fun y ↦ fderiv ℝ g' y v) p' (linearCMCSource g' p' B' v) :=
    ⟨R/4,by linarith,hw'.classical_derivative hg hpc.continuous hpb' hA hB hAc hBc hBb hR hgc v hv⟩
  have hde : (fun y ↦ fderiv ℝ g' y v)=ᶠ[𝓝 0](fun y ↦ fderiv ℝ g y v) :=
    hge.fderiv.mono fun _ hy ↦ congrArg (fun L : Plane →L[ℝ] ℝ ↦ L v) hy
  have hAe : (fun y ↦ cmcJacobian (p' y))=ᶠ[𝓝 0](fun y ↦ cmcJacobian (p y)) :=
    hpe.mono fun _ hy ↦ congrArg cmcJacobian hy
  have hSe : linearCMCSource g' p' B' v=ᶠ[𝓝 0]linearCMCSource g p B v := by
    filter_upwards [hBe.fderiv (𝕜 := ℝ),hAe.fderiv (𝕜 := ℝ),hge.fderiv (𝕜 := ℝ)] with y hBy hAy hgy
    have hG : gradient g' y=gradient g y := congrArg
      (fun L : Plane →L[ℝ] ℝ ↦ (InnerProductSpace.toDual ℝ Plane).symm L) hgy
    simp only [linearCMCSource,hBy,hAy,hG]
  exact hd'.congr hde.symm hpe.symm hSe.symm

lemma HolderJet.linearSource {n : ℕ} {g : Plane → ℝ} {p B : Plane → Plane}
    (hg : HolderJet (n+1) g 0) (hp : HolderJet (n+1) p 0) (hB : HolderJet (n+1) B 0)
    (v : Plane) : HolderJet n (linearCMCSource g p B v) 0 := by
  have hA := hp.smooth_comp cmcJacobian_contDiff
  exact (hB.2.clm_apply (HolderJet.const v)).sub
    ((hA.2.clm_apply (HolderJet.const v)).clm_apply hg.gradient)

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace
namespace CubicTorus

theorem LinearCMCEquationNear.schauder {n : ℕ} {g : Plane → ℝ} {p B : Plane → Plane}
    (hw : LinearCMCEquationNear g p B) (hpb : ∀ y,‖p y‖≤1)
    (hg : HolderJet 1 g 0) (hp : HolderJet (n+1) p 0) (hB : HolderJet (n+1) B 0) :
    HolderJet (n+2) g 0 := by
  induction n generalizing g B with
  | zero => exact hw.holderJet_two hpb hg hp hB
  | succ n ih =>
    have hg' : HolderJet (n+2) g 0 := ih hw hg hp.pred hB.pred
    have hd (v : Plane) (hv : ‖v‖≤1) : HolderJet (n+2) (fun y ↦ fderiv ℝ g y v) 0 := by
      have hgd : HolderJet 1 (fun y ↦ fderiv ℝ g y v) 0 := (hg'.directional v).of_le (by omega)
      have hp1 : HolderJet 1 p 0 := hp.of_le (by omega)
      have hB1 : HolderJet 1 B 0 := hB.of_le (by omega)
      have hw' := hw.derivative hpb (hg'.of_le (by omega)) hp1 hB1 v hv
      exact ih hw' hgd hp.pred (hg'.linearSource hp hB v)
    exact HolderJet.of_directionals hg.1
      (hd (EuclideanSpace.single 0 1) (by simp)) (hd (EuclideanSpace.single 1 1) (by simp))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeDivergence_continuous {F : Plane → Plane} (hF : ContDiff ℝ 1 F) :
    Continuous (planeDivergence F) := by
  have hd := hF.continuous_fderiv (by simp)
  exact ((EuclideanSpace.proj 0 : Plane →L[ℝ] ℝ).continuous.comp
    (hd.clm_apply continuous_const)).add
    ((EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ).continuous.comp
    (hd.clm_apply continuous_const))

lemma plane_component_fderiv {F : Plane → Plane} (hF : ContDiff ℝ 1 F)
    (i : Fin 2) (y v : Plane) :
    fderiv ℝ (fun z ↦ F z i) y v=(fderiv ℝ F y v) i := by
  have hh := (EuclideanSpace.proj i : Plane →L[ℝ] ℝ).hasFDerivAt.comp y
    ((hF.differentiable (by simp) y).hasFDerivAt)
  have he := hh.fderiv
  change fderiv ℝ (fun z ↦ F z i) y=_ at he
  rw [he]
  rfl

lemma plane_divergence_integration_by_parts {F : Plane → Plane} (hF : ContDiff ℝ 1 F)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∫ y,planeDivergence F y*ψ y)= -(∫ y,fderiv ℝ ψ y (F y)) := by
  have hcomp (i : Fin 2) : ContDiff ℝ 1 (fun y ↦ F y i) :=
    (EuclideanSpace.proj i : Plane →L[ℝ] ℝ).contDiff.comp hF
  have hi (i : Fin 2) : Integrable (fun y ↦ (fderiv ℝ F y (EuclideanSpace.single i 1)) i*ψ y) :=
    (((EuclideanSpace.proj i : Plane →L[ℝ] ℝ).continuous.comp
      ((hF.continuous_fderiv (by simp)).clm_apply continuous_const)).mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hj (i : Fin 2) : Integrable (fun y ↦ F y i*fderiv ℝ ψ y (EuclideanSpace.single i 1)) :=
    ((hcomp i).continuous.mul ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ _).mul_left
  have hpart (i : Fin 2) := C1_local_integration_by_parts isOpen_univ (hcomp i).continuous
    (hcomp i).contDiffOn hψ hc (subset_univ _) (EuclideanSpace.single i 1)
  simp_rw [plane_component_fderiv hF] at hpart
  have he (y : Plane) : fderiv ℝ ψ y (F y)=
      F y 0*fderiv ℝ ψ y (EuclideanSpace.single 0 1)+
      F y 1*fderiv ℝ ψ y (EuclideanSpace.single 1 1) := by
    conv_lhs => rw [plane_decompose (F y)]
    simp
  simp_rw [planeDivergence,add_mul,he]
  rw [integral_add (hi 0) (hi 1),hpart 0,hpart 1,integral_add (hj 0) (hj 1)]
  ring

lemma classical_divergence_of_weak {F : Plane → Plane} (hF : ContDiff ℝ 1 F)
    {S : Set Plane} (hS : IsOpen S) {H : ℝ}
    (hw : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ⊆S →
      (∫ y,fderiv ℝ ψ y (F y))=H*(∫ y,ψ y)) :
    ∀ y∈S,planeDivergence F y= -H := by
  have hd := (planeDivergence_continuous hF).add (continuous_const (y := H))
  have hae := hS.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (hd.locallyIntegrable.locallyIntegrableOn S) (fun ψ hψ hc hs ↦ ?_)
  · have hae' : (fun y ↦ planeDivergence F y+H)=ᵐ[volume.restrict S] (fun _ ↦ (0:ℝ)) := by
      change ∀ᵐ y ∂volume.restrict S,planeDivergence F y+H=0
      rw [ae_restrict_iff' hS.measurableSet]
      exact hae
    have he := MeasureTheory.Measure.eqOn_open_of_ae_eq hae' hS hd.continuousOn continuousOn_const
    intro y hy
    exact eq_neg_of_add_eq_zero_left (he hy)
  · have hi : Integrable (fun y ↦ planeDivergence F y*ψ y) volume := ((planeDivergence_continuous hF).mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
    have hj : Integrable (fun y ↦ H*ψ y) volume := (hψ.continuous.integrable_of_hasCompactSupport hc).const_mul H
    simp only [smul_eq_mul,Pi.add_apply,mul_add]
    simp_rw [mul_comm (ψ _) (planeDivergence F _),mul_comm (ψ _) H]
    rw [integral_add hi hj,plane_divergence_integration_by_parts hF (hψ.of_le (by simp)) hc,
      hw ψ hψ hc hs,integral_const_mul]
    ring

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_TorusC2CMCAt
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

lemma plane_gradient_mul {f g : Plane → ℝ} {x : Plane}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    gradient (fun y ↦ f y*g y) x=f x • gradient g x+g x • gradient f x := by
  apply ext_inner_left ℝ
  intro v
  simp only [inner_gradient_right,inner_add_right,real_inner_smul_right,
    fderiv_fun_mul hf hg,add_apply,smul_apply,smul_eq_mul,starRingEnd_apply,star_trivial]

lemma plane_gradient_contDiff {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (gradient f) :=
  (InnerProductSpace.toDual ℝ Plane).symm.toContinuousLinearEquiv.contDiff.comp
    (hf.fderiv_right (by simp))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_inner_components (u v : Plane) : ⟪u,v⟫=u 0*v 0+u 1*v 1 := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,star_trivial]
  ring

lemma plane_gradient_component (f : Plane → ℝ) (y : Plane) (i : Fin 2) :
    gradient f y i=fderiv ℝ f y (EuclideanSpace.single i 1) := by
  rw [← inner_gradient_left, EuclideanSpace.inner_single_right]
  simp

lemma planeDivergence_add {F G : Plane → Plane} {y : Plane}
    (hF : DifferentiableAt ℝ F y) (hG : DifferentiableAt ℝ G y) :
    planeDivergence (fun z ↦ F z+G z) y=planeDivergence F y+planeDivergence G y := by
  simp only [planeDivergence,fderiv_fun_add hF hG,add_apply,PiLp.add_apply]
  ring

lemma planeDivergence_smul {a : Plane → ℝ} {F : Plane → Plane} {y : Plane}
    (ha : DifferentiableAt ℝ a y) (hF : DifferentiableAt ℝ F y) :
    planeDivergence (fun z ↦ a z • F z) y=
      a y*planeDivergence F y+⟪gradient a y,F y⟫ := by
  rw [plane_inner_components]
  simp only [plane_gradient_component,planeDivergence,fderiv_fun_smul ha hF,
    add_apply,smul_apply,ContinuousLinearMap.smulRight_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  ring

lemma plane_gradient_weight {p : Plane → Plane} (hp : ContDiff ℝ (⊤ : ℕ∞) p) (y : Plane) :
    gradient (fun z ↦ cmcWeight (p z)) y=
      (cmcWeight (p y))⁻¹ •
        (p y 0 • gradient (fun z ↦ p z 0) y+p y 1 • gradient (fun z ↦ p z 1) y) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left]
  have he := ((cmcWeight_hasFDerivAt (p y)).comp y
    ((hp.differentiable (by simp) y).hasFDerivAt)).fderiv
  change fderiv ℝ (fun z ↦ cmcWeight (p z)) y=_ at he
  rw [he]
  simp only [ContinuousLinearMap.comp_apply,smul_apply,innerSL_apply_apply,
    smul_eq_mul,inner_add_left,real_inner_smul_left,inner_gradient_left,
    plane_component_fderiv (hp.of_le (by simp)),plane_inner_components]

lemma plane_gradient_div {a b : Plane → ℝ} {y : Plane}
    (ha : DifferentiableAt ℝ a y) (hb : DifferentiableAt ℝ b y) (hby : b y≠0) :
    gradient (fun z ↦ a z/b z) y=
      (b y)⁻¹ • gradient a y-(a y/(b y)^2) • gradient b y := by
  apply ext_inner_right ℝ
  intro v
  have hi := (hasDerivAt_inv hby).comp_hasFDerivAt y hb.hasFDerivAt
  have hd := (ha.hasFDerivAt.mul hi).fderiv
  change fderiv ℝ (fun z ↦ a z*(b z)⁻¹) y=_ at hd
  simp only [div_eq_mul_inv,inner_gradient_left,inner_sub_left,real_inner_smul_left,hd,
    add_apply,smul_apply,smul_eq_mul,Function.comp_def]
  field_simp
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_hessian_direction {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (y v : Plane) : fderiv ℝ (gradient g) y v=
      gradient (fun z ↦ fderiv ℝ g z v) y := by
  ext i
  rw [← plane_component_fderiv ((plane_gradient_contDiff hg).of_le (by simp))]
  simp_rw [plane_gradient_component]
  rw [fderiv_fderiv_apply hg,fderiv_fderiv_apply hg]
  exact (hg.contDiffAt.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)) v _

lemma plane_hessian_symmetric {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (y v w : Plane) : ⟪fderiv ℝ (gradient g) y v,w⟫=⟪v,fderiv ℝ (gradient g) y w⟫ := by
  rw [plane_hessian_direction hg,plane_hessian_direction hg]
  conv_rhs => rw [real_inner_comm]
  rw [inner_gradient_left,inner_gradient_left,fderiv_fderiv_apply hg,fderiv_fderiv_apply hg]
  exact (hg.contDiffAt.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)) w v

lemma plane_shape_trace_identity (p : Plane) (L : Plane →L[ℝ] Plane)
    (hL : ∀ v w : Plane,⟪L v,w⟫=⟪v,L w⟫) :
    (⟪L (EuclideanSpace.single 0 1),cmcJacobian p (L (EuclideanSpace.single 0 1))⟫+
      ⟪L (EuclideanSpace.single 1 1),cmcJacobian p (L (EuclideanSpace.single 1 1))⟫-
      ⟪(cmcWeight p)⁻¹ • L p,cmcJacobian p ((cmcWeight p)⁻¹ • L p)⟫)/cmcWeight p=
      planeTraceSquare ((cmcJacobian p).comp L) := by
  have hc : L (EuclideanSpace.single 0 1) 1=L (EuclideanSpace.single 1 1) 0 := by
    simpa only [EuclideanSpace.inner_single_right,EuclideanSpace.inner_single_left,
      conj_trivial,one_mul] using hL (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
  have he : L p=p 0 • L (EuclideanSpace.single 0 1)+p 1 • L (EuclideanSpace.single 1 1) := by
    conv_lhs => rw [plane_decompose p]
    simp only [map_add,map_smul]
  simp only [planeTraceSquare,ContinuousLinearMap.comp_apply,cmcJacobian_apply,
    inner_sub_right,real_inner_smul_left,real_inner_smul_right,he,inner_add_left,inner_add_right,
    plane_inner_components,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,hc]
  field_simp
  ring

lemma graphSquaredSecondFundamentalForm_formula {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (y : Plane) :
    graphSquaredSecondFundamentalForm g y=
      (⟪gradient (fun z ↦ gradient g z 0) y,cmcJacobian (gradient g y) (gradient (fun z ↦ gradient g z 0) y)⟫+
        ⟪gradient (fun z ↦ gradient g z 1) y,cmcJacobian (gradient g y) (gradient (fun z ↦ gradient g z 1) y)⟫-
        ⟪gradient (fun z ↦ cmcWeight (gradient g z)) y,
          cmcJacobian (gradient g y) (gradient (fun z ↦ cmcWeight (gradient g z)) y)⟫)/cmcWeight (gradient g y) := by
  have hi (i : Fin 2) : gradient (fun z ↦ gradient g z i) y=
      fderiv ℝ (gradient g) y (EuclideanSpace.single i 1) := by
    simp_rw [plane_gradient_component]
    exact (plane_hessian_direction hg y _).symm
  have hq : gradient (fun z ↦ cmcWeight (gradient g z)) y=
      (cmcWeight (gradient g y))⁻¹ • fderiv ℝ (gradient g) y (gradient g y) := by
    rw [plane_gradient_weight (plane_gradient_contDiff hg),hi 0,hi 1]
    congr 1
    conv_rhs => rw [plane_decompose (gradient g y)]
    simp only [map_add,map_smul]
  rw [hi 0,hi 1,hq]
  exact (plane_shape_trace_identity (gradient g y) (fderiv ℝ (gradient g) y)
    (plane_hessian_symmetric hg y)).symm

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_GraphInverseMetric
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

lemma LinearCMCEquation.classical_zero {g f : Plane → ℝ} {U : Set Plane}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hU : IsOpen U)
    (hw : LinearCMCEquation f (gradient g) (fun _ ↦ 0) U) :
    ∀ y∈U,planeDivergence (fun z ↦ cmcJacobian (gradient g z) (gradient f z)) y=0 := by
  have hF : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ cmcJacobian (gradient g z) (gradient f z)) :=
    (cmcJacobian_contDiff.comp (plane_gradient_contDiff hg)).clm_apply (plane_gradient_contDiff hf)
  have ht := classical_divergence_of_weak (H := 0) (hF.of_le (by simp)) hU
    (fun ψ hψ hc hs ↦ by simpa only [sub_zero,zero_mul] using hw ψ hψ hc hs)
  simpa only [neg_zero] using ht

theorem plane_weight_harmonic_potential {p : Plane → Plane}
    (hp : ContDiff ℝ (⊤ : ℕ∞) p) {A : Plane → Plane →L[ℝ] Plane}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (y : Plane)
    (hz : ∀ i : Fin 2,planeDivergence (fun z ↦ A z (gradient (fun w ↦ p w i) z)) y=0) :
    planeDivergence (fun z ↦ A z (gradient (fun w ↦ cmcWeight (p w)) z)) y=
      (⟪gradient (fun w ↦ p w 0) y,A y (gradient (fun w ↦ p w 0) y)⟫+
        ⟪gradient (fun w ↦ p w 1) y,A y (gradient (fun w ↦ p w 1) y)⟫-
        ⟪gradient (fun w ↦ cmcWeight (p w)) y,A y (gradient (fun w ↦ cmcWeight (p w)) y)⟫)/
        cmcWeight (p y) := by
  let q : Plane → ℝ := fun z ↦ cmcWeight (p z)
  let u : Fin 2 → Plane → ℝ := fun i z ↦ p z i
  let F : Fin 2 → Plane → Plane := fun i z ↦ A z (gradient (u i) z)
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := cmcWeight_contDiff.comp hp
  have hu (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (u i) :=
    (EuclideanSpace.proj i : Plane →L[ℝ] ℝ).contDiff.comp hp
  have hF (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (F i) := hA.clm_apply (plane_gradient_contDiff (hu i))
  have hquot (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ u i z/q z) :=
    (hu i).div hq (fun z ↦ (cmcWeight_pos _).ne')
  have hprod (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (fun z ↦ (u i z/q z) • F i z) :=
    (hquot i).smul (hF i)
  have hfield : (fun z ↦ A z (gradient q z))=
      (fun z ↦ (u 0 z/q z) • F 0 z+(u 1 z/q z) • F 1 z) := by
    funext z
    rw [plane_gradient_weight hp]
    simp only [F,u,q,map_smul,map_add,smul_add,smul_smul,div_eq_mul_inv]
    congr 1 <;> congr 1 <;> ring
  change planeDivergence (fun z ↦ A z (gradient q z)) y=_
  rw [hfield,planeDivergence_add
    ((hprod 0).differentiable (by simp) y)
    ((hprod 1).differentiable (by simp) y),
    planeDivergence_smul ((hquot 0).differentiable (by simp) y) ((hF 0).differentiable (by simp) y),
    planeDivergence_smul ((hquot 1).differentiable (by simp) y) ((hF 1).differentiable (by simp) y)]
  have hz' (i : Fin 2) : planeDivergence (F i) y=0 := hz i
  rw [hz' 0,hz' 1,mul_zero,mul_zero,zero_add,zero_add,
    plane_gradient_div ((hu 0).differentiable (by simp) y) (hq.differentiable (by simp) y) (cmcWeight_pos _).ne',
    plane_gradient_div ((hu 1).differentiable (by simp) y) (hq.differentiable (by simp) y) (cmcWeight_pos _).ne']
  have he := congrArg (fun v : Plane ↦ ⟪gradient q y,A y v⟫) (plane_gradient_weight hp y)
  change ⟪gradient q y,A y (gradient q y)⟫=_ at he
  simp only [map_smul,map_add,inner_smul_right,inner_add_right] at he
  change _=(⟪gradient (u 0) y,F 0 y⟫+⟪gradient (u 1) y,F 1 y⟫-
    ⟪gradient q y,A y (gradient q y)⟫)/q y
  rw [he]
  simp only [inner_sub_left,real_inner_smul_left]
  dsimp only [F,u,q]
  field_simp [(cmcWeight_pos (p y)).ne']
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cmc_graph_curvature_potential {g : Plane → ℝ} {U : Set Plane}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hU : IsOpen U)
    (hw : ∀ i : Fin 2,LinearCMCEquation
      (fun y ↦ fderiv ℝ g y (EuclideanSpace.single i 1)) (gradient g) (fun _ ↦ 0) U)
    {y : Plane} (hy : y∈U) :
    planeDivergence (fun z ↦ cmcJacobian (gradient g z)
      (gradient (fun w ↦ cmcWeight (gradient g w)) z)) y=
        graphSquaredSecondFundamentalForm g y := by
  rw [graphSquaredSecondFundamentalForm_formula hg]
  apply plane_weight_harmonic_potential (plane_gradient_contDiff hg)
    (cmcJacobian_contDiff.comp (plane_gradient_contDiff hg))
  intro i
  simp_rw [plane_gradient_component]
  exact (hw i).classical_zero hg
    ((hg.fderiv_right (by simp)).clm_apply contDiff_const) hU y hy

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphInverseMetric_slope (p q : Plane) (c : ℝ) :
    graphInverseMetric p (q+c • p)=q+
      ((c-⟪p,q⟫)/(cmcWeight p)^2) • p := by
  rw [graphInverseMetric,smul_apply,cmcJacobian_apply]
  simp only [inner_add_right,inner_smul_right,real_inner_self_eq_norm_sq,smul_sub,smul_smul,
    mul_inv_cancel₀ (cmcWeight_pos p).ne',one_smul]
  have he : c-cmcWeight p*(((cmcWeight p)^3)⁻¹*(⟪p,q⟫+c*‖p‖^2))=
      (c-⟪p,q⟫)/(cmcWeight p)^2 := by
    field_simp [(cmcWeight_pos p).ne']
    nlinarith [congrArg (fun r : ℝ ↦ c*r) (cmcWeight_sq p)]
  rw [add_sub_assoc,← sub_smul,he]

lemma graph_metric_projection {n : Cover} (hn : ‖n‖=1) (p : Plane) (v : Cover) :
    normalPlaneEmbedding n (graphInverseMetric p (normalPlaneCoordinates n v+⟪n,v⟫ • p))+
      ⟪p,graphInverseMetric p (normalPlaneCoordinates n v+⟪n,v⟫ • p)⟫ • n=
        v-⟪graphSlopeNormal n p,v⟫ • graphSlopeNormal n p := by
  have he : normalPlaneEmbedding n=(normalPlaneLinearIsometry n).toContinuousLinearMap := rfl
  have hi : ⟪graphSlopeNormal n p,v⟫=(cmcWeight p)⁻¹*(⟪n,v⟫-⟪p,normalPlaneCoordinates n v⟫) := by
    rw [graphSlopeNormal_weight hn,real_inner_smul_left,inner_sub_left,
      normalPlaneEmbedding_inner_coordinates hn]
  have hc : ⟪p,normalPlaneCoordinates n v⟫+
      ((⟪n,v⟫-⟪p,normalPlaneCoordinates n v⟫)/(cmcWeight p)^2)*‖p‖^2=
        ⟪n,v⟫-(⟪n,v⟫-⟪p,normalPlaneCoordinates n v⟫)/(cmcWeight p)^2 := by
    field_simp [(cmcWeight_pos p).ne']
    nlinarith [congrArg (fun r : ℝ ↦ (⟪n,v⟫-⟪p,normalPlaneCoordinates n v⟫)*r) (cmcWeight_sq p)]
  rw [graphInverseMetric_slope,inner_add_right,inner_smul_right,real_inner_self_eq_norm_sq,hc,
    he,map_add,map_smul,hi,graphSlopeNormal_weight hn]
  have hr := normalPlaneCoordinates_reconstruct hn v
  change (normalPlaneLinearIsometry n).toContinuousLinearMap (normalPlaneCoordinates n v)+⟪n,v⟫ • n=v at hr
  conv_rhs => lhs; rw [← hr]

  have hq : (cmcWeight p)⁻¹*(⟪n,v⟫-⟪p,normalPlaneCoordinates n v⟫)*(cmcWeight p)⁻¹=
      (⟪n,v⟫-⟪p,normalPlaneCoordinates n v⟫)/(cmcWeight p)^2 := by
    field_simp
  simp only [smul_smul,smul_sub,hq,sub_smul,he]
  module

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SurfaceGraphBundleMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma lpPullbackLE_ae {α β F : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ν : Measure α} {μ : Measure β} {f : α → β}
    (hf : Measurable f) (hle : Measure.map f ν ≤ μ) (u : Lp F 2 μ) :
    lpPullbackLE hf hle u =ᵐ[ν] u ∘ f := by
  have hmp : MeasurePreserving f ν (Measure.map f ν) := ⟨hf,rfl⟩
  have hr := Lp.coeFn_LpToLpOfMeasureLeSMul (c := 1)
    (by simp : (1 : ℝ≥0∞) ≠ ∞) (by simpa using hle) u
  exact (Lp.coeFn_compMeasurePreserving _ hmp).trans (hmp.quasiMeasurePreserving.ae_eq_comp hr)

lemma lpPullbackLE_congr_ae {α β F : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ν : Measure α} {μ : Measure β} {f : α → β}
    (hf : Measurable f) (hle : Measure.map f ν ≤ μ) {u v : β → F}
    (huv : u =ᵐ[μ] v) : u ∘ f =ᵐ[ν] v ∘ f := by
  exact (show Measure.QuasiMeasurePreserving f ν μ from
    ⟨hf,Measure.absolutelyContinuous_of_le hle⟩).ae_eq_comp huv

lemma graphAreaVector_norm_ge_one {n : Cover} (hn : ‖n‖ = 1)
    (g : Plane → ℝ) (y : Plane) : 1 ≤ ‖graphAreaVector n g y‖ := by
  have hs := graphAreaVector_norm_sq hn g y
  nlinarith [norm_nonneg (graphAreaVector n g y), sq_nonneg ‖gradient g y‖]

lemma graph_chart_measure_le {μ : Measure NormalBundle}
    (a : Cover) {n : Cover} (hn : ‖n‖ = 1) {g : Plane → ℝ}
    (hg : Continuous g) {φ : Cover → ℝ} (hφ : ∀ x, φ x ∈ Icc 0 1)
    (hm : μ.withDensity (fun z => ENNReal.ofReal (φ z.1)) =
      Measure.map (actualNormalGraphChart a hn g)
        (volume.withDensity (fun y => ENNReal.ofReal
          (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖))))
    {S : Set Plane} (hS : MeasurableSet S)
    (hunit : ∀ y ∈ S, φ (a+normalGraph n g y)=1) :
    Measure.map (actualNormalGraphChart a hn g) (volume.restrict S) ≤ μ := by
  have hd : volume.restrict S ≤ volume.withDensity (fun y => ENNReal.ofReal
      (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖)) := by
    rw [← withDensity_indicator_one hS]
    apply withDensity_mono
    filter_upwards [] with y
    by_cases hy : y∈S
    · simp only [Set.indicator_of_mem hy, Pi.one_apply, hunit y hy, one_mul]
      simpa using ENNReal.ofReal_le_ofReal (graphAreaVector_norm_ge_one hn g y)
    · simp [hy]
  have hcut : μ.withDensity (fun z => ENNReal.ofReal (φ z.1)) ≤ μ := by
    conv_rhs => rw [← withDensity_one (μ := μ)]
    apply withDensity_mono
    exact ae_of_all _ (fun z => by simpa using ENNReal.ofReal_le_ofReal (hφ z.1).2)
  exact ((Measure.map_mono hd (actualNormalGraphChart_measurable a hn hg)).trans_eq hm.symm).trans hcut

lemma graphCovector_apply (n : Cover) (g : Plane → ℝ) (y : Plane) (v : Cover) :
    graphCovector n g y v = normalPlaneCoordinates n v + ⟪n,v⟫ • gradient g y := rfl

lemma graphCovectorLp_ae {ν : Measure Plane} {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) (u : Lp Cover 2 ν) :
    graphCovectorLp hn hg u =ᵐ[ν] fun y => graphCovector n g y (u y) := by
  have ha := (graphCovector_memLp (ν := ν) hn hg).coeFn_toLp
  have hb := (ContinuousLinearMap.id ℝ (Cover →L[ℝ] Plane)).coeFn_holder
    ((graphCovector_memLp (ν := ν) hn hg).toLp (graphCovector n g)) u (r := 2)
  filter_upwards [ha,hb] with y ha hb
  change (graphCovectorLp hn hg u) y = _ at hb
  simpa only [ContinuousLinearMap.id_apply,ha] using hb

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphCovector_duality {n : Cover} (hn : ‖n‖=1) (g : Plane → ℝ)
    (y v : Plane) (w : Cover) :
    ⟪graphCovector n g y w,v⟫ =
      ⟪w,normalPlaneEmbedding n v+⟪gradient g y,v⟫ • n⟫ := by
  rw [graphCovector_apply,inner_add_left,real_inner_smul_left,
    inner_add_right,inner_smul_right]
  have he : ⟪normalPlaneCoordinates n w,v⟫=⟪w,normalPlaneEmbedding n v⟫ := by
    calc
      _ = ⟪v,normalPlaneCoordinates n w⟫ := real_inner_comm _ _
      _ = ⟪normalPlaneEmbedding n v,w⟫ := (normalPlaneEmbedding_inner_coordinates hn v w).symm
      _ = _ := real_inner_comm _ _
  rw [he]
  have hi : ⟪n,w⟫=⟪w,n⟫ := real_inner_comm _ _
  rw [hi]
  ring

lemma graphCovector_normal_zero {n : Cover} (hn : ‖n‖=1)
    (g : Plane → ℝ) (y : Plane) :
    graphCovector n g y (graphSlopeNormal n (gradient g y))=0 := by
  rw [graphSlopeNormal_weight hn,map_smul,map_sub,graphCovector_apply,
    graphCovector_apply,normalPlaneCoordinates_normal hn,
    normalPlaneCoordinates_embedding,real_inner_self_eq_norm_sq,hn,one_pow,
    normalPlaneEmbedding_inner hn,one_smul,zero_smul,zero_add,add_zero,sub_self,smul_zero]

lemma gradient_graph_trace (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {g : Plane → ℝ} {y : Plane} (hg : DifferentiableAt ℝ g y)
    {f : Cover → ℝ} (hf : DifferentiableAt ℝ f (a+normalGraph n g y)) :
    gradient (fun z => f (a+normalGraph n g z)) y =
      graphCovector n g y (gradient f (a+normalGraph n g y)) := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left,graphCovector_duality hn]
  have hc := hf.hasFDerivAt.comp y ((normalGraph_hasFDerivAt hg).const_add a)
  change (fderiv ℝ (f ∘ fun x => a+normalGraph n g x) y) v = _
  rw [hc.fderiv,ContinuousLinearMap.comp_apply,← inner_gradient_left]
  congr 1
  simp only [add_apply,ContinuousLinearMap.smulRight_apply,
    inner_gradient_left]
  rfl

lemma actualNormalGraphChart_position (a : Cover) {n : Cover} (hn : ‖n‖=1)
    (g : Plane → ℝ) {y : Plane}
    (hy : ∀ i, (a+normalGraph n g y) i ∈ Icc 0 1) :
    ((actualNormalGraphChart a hn g y).1 : Cover)=a+normalGraph n g y := by
  change ((clampCell (a+normalGraph n g y)) : Cover)=_
  ext i
  change max 0 (min 1 ((a+normalGraph n g y) i))=(a+normalGraph n g y) i
  rw [min_eq_right (hy i).2,max_eq_right (hy i).1]

lemma actualNormalGraphChart_normal (a : Cover) {n : Cover} (hn : ‖n‖=1)
    (g : Plane → ℝ) (y : Plane) :
    ((actualNormalGraphChart a hn g y).2 : Cover)=graphSlopeNormal n (gradient g y) :=
  graphUnitNormalExtension_graph a hn g g y

lemma smoothScalarGradient_graph_covector (a : Cover) {n : Cover} (hn : ‖n‖=1)
    (f : smoothPeriodicScalars) {g : Plane → ℝ} {y : Plane}
    (hgy : DifferentiableAt ℝ g y)
    (hy : ∀ i, (a+normalGraph n g y) i ∈ Icc 0 1) :
    graphCovector n g y (smoothScalarGradient f (actualNormalGraphChart a hn g y))=
      gradient (fun z => f.val (a+normalGraph n g z)) y := by
  change graphCovector n g y (gradient f.val (actualNormalGraphChart a hn g y).1-
    ⟪((actualNormalGraphChart a hn g y).2 : Cover),gradient f.val (actualNormalGraphChart a hn g y).1⟫ •
      ((actualNormalGraphChart a hn g y).2 : Cover))=_
  rw [actualNormalGraphChart_position a hn g hy,actualNormalGraphChart_normal,
    map_sub,map_smul,graphCovector_normal_zero hn,smul_zero,sub_zero]
  exact (gradient_graph_trace a hn hgy (f.property.1.differentiable (by simp) _)).symm

lemma PlaneWeakGradientOn.congr {S : Set Plane} {u u' : Plane → ℝ}
    {G G' : Plane → Plane} (h : PlaneWeakGradientOn S u G)
    (hu : u'=ᵐ[volume.restrict S] u) (hG : G'=ᵐ[volume.restrict S] G) :
    PlaneWeakGradientOn S u' G' := by
  intro v ψ hψ hc hs
  have hleft : (∫ y in S, ⟪G' y,v⟫*ψ y)=(∫ y in S, ⟪G y,v⟫*ψ y) :=
    integral_congr_ae (hG.mono (fun _ he => by dsimp only; rw [he]))
  have hright : (∫ y in S, u' y*fderiv ℝ ψ y v)=(∫ y in S, u y*fderiv ℝ ψ y v) :=
    integral_congr_ae (hu.mono (fun _ he => by dsimp only; rw [he]))
  rw [hleft,hright]
  exact h v ψ hψ hc hs

lemma C1_weak_gradient_on {S : Set Plane} (hS : IsOpen S)
    {f : Plane → ℝ} (hf : Continuous f) (hfc : ContDiffOn ℝ 1 f S) :
    PlaneWeakGradientOn S f (gradient f) := by
  intro v ψ hψ hc hs
  have hi₁ : (∫ y in S, ⟪gradient f y,v⟫*ψ y)=(∫ y, ⟪gradient f y,v⟫*ψ y) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hs h)),mul_zero]
  have hi₂ : (∫ y in S, f y*fderiv ℝ ψ y v)=(∫ y, f y*fderiv ℝ ψ y v) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport
      (fun h => hy (hs ((tsupport_fderiv_apply_subset (f := ψ) ℝ v) h))),mul_zero]
  rw [hi₁,hi₂]
  simpa only [inner_gradient_left] using C1_local_integration_by_parts hS hf hfc
    (hψ.of_le (by simp)) hc hs v

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma L2_pair_scalar_measure {ν : Measure Plane} {u : Lp ℝ 2 ν} {φ : Plane → ℝ}
    (hφ : MemLp φ 2 ν) : ⟪u,hφ.toLp φ⟫=(∫ y,u y*φ y ∂ν) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hφ.coeFn_toLp] with y hy
  simp only [hy,RCLike.inner_apply,conj_trivial]
  ring

lemma L2_pair_vector_measure {ν : Measure Plane} {G : Lp Plane 2 ν}
    {f : Plane → Plane} (hf : MemLp f 2 ν) :
    ⟪G,hf.toLp f⟫=(∫ y,⟪G y,f y⟫ ∂ν) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with y hy
  rw [hy]

lemma PlaneWeakGradientOn.L2_limit {S : Set Plane}
    {u : ℕ → Lp ℝ 2 (volume.restrict S)}
    {G : ℕ → Lp Plane 2 (volume.restrict S)}
    {u₀ : Lp ℝ 2 (volume.restrict S)} {G₀ : Lp Plane 2 (volume.restrict S)}
    (hu : Tendsto u atTop (𝓝 u₀)) (hG : Tendsto G atTop (𝓝 G₀))
    (hweak : ∀ i,PlaneWeakGradientOn S (u i) (G i)) :
    PlaneWeakGradientOn S u₀ G₀ := by
  intro v ψ hψ hc hs
  let a : Plane → Plane := fun y => ψ y • v
  have ha : MemLp a 2 (volume.restrict S) :=
    ((hψ.continuous.smul continuous_const).memLp_of_hasCompactSupport
      hc.smul_right (p := 2) (μ := volume)).mono_measure Measure.restrict_le_self
  let A := ha.toLp a
  let b : Plane → ℝ := fun y => fderiv ℝ ψ y v
  have hb : MemLp b 2 (volume.restrict S) :=
    (((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ v) (p := 2) (μ := volume)).mono_measure Measure.restrict_le_self
  let B := hb.toLp b
  have hi (W : Lp Plane 2 (volume.restrict S)) :
      ⟪W,A⟫=(∫ y in S,⟪W y,v⟫*ψ y) := by
    rw [L2_pair_vector_measure ha]
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [a,inner_smul_right]
    ring
  have he (i : ℕ) : ⟪G i,A⟫= -⟪u i,B⟫ := by
    rw [hi,L2_pair_scalar_measure hb]
    exact hweak i v ψ hψ hc hs
  have hleft := hG.inner (𝕜 := ℝ) (tendsto_const_nhds (x := A))
  have hright := (hu.inner (𝕜 := ℝ) (tendsto_const_nhds (x := B))).neg
  have hh := tendsto_nhds_unique (hleft.congr' (Eventually.of_forall he)) hright
  rw [hi,L2_pair_scalar_measure hb] at hh
  exact hh

lemma graph_trace_contDiffOn_C1 (a n : Cover) {g : Plane → ℝ} {S : Set Plane}
    (hg : ContDiffOn ℝ 1 g S) {f : Cover → ℝ} (hf : ContDiff ℝ 1 f) :
    ContDiffOn ℝ 1 (fun y => f (a+normalGraph n g y)) S := by
  have hgraph : ContDiffOn ℝ 1 (fun y => a+normalGraph n g y) S :=
    contDiffOn_const.add ((normalPlaneLinearIsometry n).contDiff.contDiffOn.add
      (hg.smul contDiffOn_const))
  exact hf.comp_contDiffOn hgraph

lemma surfaceSmoothJet_chart_weak_gradient (μ : FiniteMeasure NormalBundle)
    (a : Cover) {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {S : Set Plane} (hS : IsOpen S)
    (hgc : ContDiffOn ℝ 1 g S)
    (hcell : ∀ y ∈ S, ∀ i, (a+normalGraph n g y) i ∈ Icc 0 1)
    (hdom : Measure.map (actualNormalGraphChart a hn g) (volume.restrict S) ≤
      (μ : Measure NormalBundle)) (f : smoothPeriodicScalars) :
    PlaneWeakGradientOn S
      (lpPullbackLE (actualNormalGraphChart_measurable a hn hg.continuous) hdom
        (surfaceSmoothJet μ f).1)
      (graphCovectorLp hn hg
        (lpPullbackLE (actualNormalGraphChart_measurable a hn hg.continuous) hdom
          (surfaceSmoothJet μ f).2)) := by
  let chart := actualNormalGraphChart a hn g
  have hchart : Measurable chart := actualNormalGraphChart_measurable a hn hg.continuous
  have hv := (lpPullbackLE_ae hchart hdom (surfaceSmoothJet μ f).1).trans
    (lpPullbackLE_congr_ae hchart hdom
      ((smoothScalarValue f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)))
  have hw := (lpPullbackLE_ae hchart hdom (surfaceSmoothJet μ f).2).trans
    (lpPullbackLE_congr_ae hchart hdom
      ((smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle)))
  have hv' : lpPullbackLE hchart hdom (surfaceSmoothJet μ f).1 =ᵐ[volume.restrict S]
      (fun y => f.val (a+normalGraph n g y)) := by
    filter_upwards [hv,ae_restrict_mem hS.measurableSet] with y hy hSy
    change (lpPullbackLE hchart hdom (surfaceSmoothJet μ f).1) y = f.val (chart y).1 at hy
    rw [hy]
    change f.val (actualNormalGraphChart a hn g y).1 = _
    rw [actualNormalGraphChart_position a hn g (hcell y hSy)]
  have hw' : graphCovectorLp hn hg (lpPullbackLE hchart hdom (surfaceSmoothJet μ f).2)
      =ᵐ[volume.restrict S] gradient (fun y => f.val (a+normalGraph n g y)) := by
    filter_upwards [graphCovectorLp_ae hn hg
      (lpPullbackLE hchart hdom (surfaceSmoothJet μ f).2),hw,
      ae_restrict_mem hS.measurableSet] with y hmap hy hSy
    change (lpPullbackLE hchart hdom (surfaceSmoothJet μ f).2) y = smoothScalarGradient f (chart y) at hy
    rw [hmap,hy]
    exact smoothScalarGradient_graph_covector a hn f
      (((hgc y hSy).contDiffAt (hS.mem_nhds hSy)).differentiableAt (by simp)) (hcell y hSy)
  exact (C1_weak_gradient_on hS
    (graph_trace_continuous a n hg.continuous f.property.1.continuous)
    (graph_trace_contDiffOn_C1 a n hgc (f.property.1.of_le (by simp)))).congr hv' hw'

theorem surfaceH1_chart_weak_gradient (μ : FiniteMeasure NormalBundle)
    (a : Cover) {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ} {K : ℝ≥0}
    (hg : LipschitzWith K g) {S : Set Plane} (hS : IsOpen S)
    (hgc : ContDiffOn ℝ 1 g S)
    (hcell : ∀ y ∈ S, ∀ i, (a+normalGraph n g y) i ∈ Icc 0 1)
    (hdom : Measure.map (actualNormalGraphChart a hn g) (volume.restrict S) ≤
      (μ : Measure NormalBundle)) {u : SurfaceJet μ} (hu : u∈surfaceH1 μ) :
    PlaneWeakGradientOn S
      (lpPullbackLE (actualNormalGraphChart_measurable a hn hg.continuous) hdom u.1)
      (graphCovectorLp hn hg
        (lpPullbackLE (actualNormalGraphChart_measurable a hn hg.continuous) hdom u.2)) := by
  obtain ⟨w,hw,hl⟩ := mem_closure_iff_seq_limit.mp hu
  let hchart := actualNormalGraphChart_measurable a hn hg.continuous
  apply PlaneWeakGradientOn.L2_limit
    (((lpPullbackLE hchart hdom).continuous.tendsto _).comp ((continuous_fst.tendsto u).comp hl))
    (((graphCovectorLp hn hg).continuous.tendsto _).comp
      (((lpPullbackLE hchart hdom).continuous.tendsto _).comp ((continuous_snd.tendsto u).comp hl)))
  intro i
  obtain ⟨f,hf⟩ := hw i
  simp only [Function.comp_apply]
  rw [← hf]
  exact surfaceSmoothJet_chart_weak_gradient μ a hn hg hS hgc hcell hdom f

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SurfaceH1Tangency
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma smoothScalarGradient_tangent (f : smoothPeriodicScalars) (z : NormalBundle) :
    ⟪(z.2 : Cover),smoothScalarGradient f z⟫=0 := by
  change ⟪(z.2 : Cover),gradient f.val z.1-
    ⟪(z.2 : Cover),gradient f.val z.1⟫ • (z.2 : Cover)⟫=0
  rw [inner_sub_right,inner_smul_right,real_inner_self_eq_norm_sq,z.2.property]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma graphCovector_metric_pairing {n : Cover} (hn : ‖n‖=1)
    (g : Plane → ℝ) (y : Plane) (v w : Cover)
    (hw : ⟪graphSlopeNormal n (gradient g y),w⟫=0) :
    ⟪v,w⟫=cmcWeight (gradient g y)*
      ⟪graphCovector n g y v,cmcJacobian (gradient g y) (graphCovector n g y w)⟫ := by
  have hp := graph_metric_projection hn (gradient g y) w
  change normalPlaneEmbedding n (graphInverseMetric (gradient g y) (graphCovector n g y w))+
    ⟪gradient g y,graphInverseMetric (gradient g y) (graphCovector n g y w)⟫ • n = _ at hp
  rw [hw,zero_smul,sub_zero] at hp
  calc
    ⟪v,w⟫ = ⟪graphCovector n g y v,
        graphInverseMetric (gradient g y) (graphCovector n g y w)⟫ := by
      rw [graphCovector_duality hn,hp]
    _ = _ := by rw [graphInverseMetric,smul_apply,inner_smul_right]

lemma graph_area_integral {μ : Measure NormalBundle} (a : Cover) {n : Cover}
    (hn : ‖n‖=1) {g : Plane → ℝ} (hg : Continuous g)
    {φ : Cover → ℝ} (hφ : Measurable φ) (hφ0 : ∀ x,0≤φ x)
    (hm : μ.withDensity (fun z => ENNReal.ofReal (φ z.1)) =
      Measure.map (actualNormalGraphChart a hn g)
        (volume.withDensity (fun y => ENNReal.ofReal
          (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖))))
    {F : NormalBundle → ℝ} (hF : AEStronglyMeasurable F μ) :
    (∫ z,φ z.1*F z ∂μ)=∫ y,φ (a+normalGraph n g y)*‖graphAreaVector n g y‖*
      F (actualNormalGraphChart a hn g y) := by
  have hf : Measurable (fun z : NormalBundle => ENNReal.ofReal (φ z.1)) :=
    (hφ.comp (measurable_subtype_coe.comp measurable_fst)).ennreal_ofReal
  have hG : Measurable (fun y => ENNReal.ofReal
      (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖)) := by
    have hc : Continuous (fun y => a+normalGraph n g y) :=
      graph_trace_continuous a n hg continuous_id
    have hmgrad : Measurable (gradient g) :=
      (InnerProductSpace.toDual ℝ Plane).symm.continuous.measurable.comp (measurable_fderiv ℝ g)
    have harea : Measurable (fun y => ‖graphAreaVector n g y‖) := by
      exact (measurable_const.sub ((normalPlaneLinearIsometry n).continuous.measurable.comp hmgrad)).norm
    exact ((hφ.comp hc.measurable).mul harea).ennreal_ofReal
  have hFm : AEStronglyMeasurable F (μ.withDensity (fun z => ENNReal.ofReal (φ z.1))) :=
    hF.mono_ac (withDensity_absolutelyContinuous _ _)
  have he := congrArg (fun ν : Measure NormalBundle => ∫ z,F z ∂ν) hm
  rw [integral_map (actualNormalGraphChart_measurable a hn hg).aemeasurable
    (by rwa [← hm])] at he
  rw [integral_withDensity_eq_integral_toReal_smul hf
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)),
    integral_withDensity_eq_integral_toReal_smul hG
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))] at he
  simpa only [ENNReal.toReal_ofReal (hφ0 _),
    ENNReal.toReal_ofReal (mul_nonneg (hφ0 _) (norm_nonneg _)),smul_eq_mul] using he

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma periodicGraphScalar_germ (a n : Cover) {χ : Cover → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hO : tsupport χ ⊆ {x | ∀ i,0<x i ∧ x i<1})
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (x : CompactCell) :
    (periodicGraphScalar a n hχ hc hψ).val =ᶠ[𝓝 (x : Cover)]
      (fun z => χ z*graphHeightExtension a n ψ z) :=
  latticePeriodize_eventuallyEq hc.mul_right
    (tsupport_mul_subset_left.trans hO) (compactCell_coordinates x)

lemma periodicGraphScalar_zero_germ (a n : Cover) {χ : Cover → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hO : tsupport χ ⊆ {x | ∀ i,0<x i ∧ x i<1})
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (x : CompactCell)
    (hx : (x : Cover)∉tsupport χ) :
    (periodicGraphScalar a n hχ hc hψ).val =ᶠ[𝓝 (x : Cover)] (fun _ => 0) := by
  apply (periodicGraphScalar_germ a n hχ hc hO hψ x).trans
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
  simp only [Pi.zero_apply] at hy
  simp only [hy,zero_mul]

lemma periodicGraphScalar_graph_germ (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {χ : Cover → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hO : tsupport χ ⊆ {x | ∀ i,0<x i ∧ x i<1})
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {g : Plane → ℝ} (hg : Continuous g) {S : Set Plane} (hS : IsOpen S)
    (hunit : ∀ y ∈ S,χ (a+normalGraph n g y)=1) (hs : tsupport ψ⊆S)
    {y : Plane} (hy : ∀ i,(a+normalGraph n g y) i∈Icc 0 1) :
    (fun z => (periodicGraphScalar a n hχ hc hψ).val (a+normalGraph n g z))=ᶠ[𝓝 y] ψ := by
  have hpos := actualNormalGraphChart_position a hn g hy
  have he := periodicGraphScalar_germ a n hχ hc hO hψ (actualNormalGraphChart a hn g y).1
  rw [hpos] at he
  have htrace : Continuous (fun z => a+normalGraph n g z) :=
    graph_trace_continuous a n hg continuous_id
  apply (he.comp_tendsto htrace.continuousAt).trans
  have hval (z : Plane) : graphHeightExtension a n ψ (a+normalGraph n g z)=ψ z := by
    rw [graphHeightExtension,add_sub_cancel_left,normalPlaneCoordinates_graph hn]
  by_cases hys : y∈tsupport ψ
  · filter_upwards [hS.mem_nhds (hs hys)] with z hz
    dsimp only [Function.comp_apply]
    rw [hval,hunit z hz,one_mul]
  · filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hys] with z hz
    dsimp only [Function.comp_apply]
    simp only [Pi.zero_apply] at hz
    rw [hval,hz,mul_zero]

lemma periodicGraphScalar_graph_value (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {χ : Cover → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hO : tsupport χ ⊆ {x | ∀ i,0<x i ∧ x i<1})
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {g : Plane → ℝ} (hg : Continuous g) {S : Set Plane} (hS : IsOpen S)
    (hunit : ∀ y ∈ S,χ (a+normalGraph n g y)=1) (hs : tsupport ψ⊆S)
    {y : Plane} (hy : ∀ i,(a+normalGraph n g y) i∈Icc 0 1) :
    smoothScalarValue (periodicGraphScalar a n hχ hc hψ) (actualNormalGraphChart a hn g y)=ψ y := by
  change (periodicGraphScalar a n hχ hc hψ).val (actualNormalGraphChart a hn g y).1=ψ y
  rw [actualNormalGraphChart_position a hn g hy]
  exact (periodicGraphScalar_graph_germ a hn hχ hc hO hψ hg hS hunit hs hy).eq_of_nhds

lemma periodicGraphScalar_graph_covector (a : Cover) {n : Cover} (hn : ‖n‖=1)
    {χ : Cover → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hO : tsupport χ ⊆ {x | ∀ i,0<x i ∧ x i<1})
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {g : Plane → ℝ} (hg : Continuous g) {S : Set Plane} (hS : IsOpen S)
    (hunit : ∀ y ∈ S,χ (a+normalGraph n g y)=1) (hs : tsupport ψ⊆S)
    {y : Plane} (hgy : DifferentiableAt ℝ g y)
    (hy : ∀ i,(a+normalGraph n g y) i∈Icc 0 1) :
    graphCovector n g y (smoothScalarGradient (periodicGraphScalar a n hχ hc hψ)
      (actualNormalGraphChart a hn g y))=gradient ψ y := by
  rw [smoothScalarGradient_graph_covector a hn _ hgy hy]
  have he := (periodicGraphScalar_graph_germ a hn hχ hc hO hψ hg hS hunit hs hy).fderiv_eq (𝕜 := ℝ)
  simp only [gradient,he]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma surfaceJacobiB_smooth_integral (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (u : SurfaceJet μ)
    (f : smoothPeriodicScalars) :
    surfaceJacobiB μ q u (surfaceSmoothJet μ f)=
      ∫ z,⟪u.2 z,smoothScalarGradient f z⟫-q z*u.1 z*smoothScalarValue f z ∂(μ : Measure NormalBundle) := by
  unfold surfaceJacobiB
  rw [L2.inner_def,L2.inner_def,← integral_sub
    (L2.integrable_inner u.2 (surfaceSmoothJet μ f).2)
    (L2.integrable_inner (surfaceMultiplier μ q u.1) (surfaceSmoothJet μ f).1)]
  apply integral_congr_ae
  filter_upwards [(smoothScalarValue f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle),
    (smoothScalarGradient f).coeFn_toLp (p := 2) (𝕜 := ℝ) (μ : Measure NormalBundle),
    Lp.coeFn_lpSMul (r := 2) q u.1] with z hf hg hq
  change (surfaceSmoothJet μ f).1 z=smoothScalarValue f z at hf
  change (surfaceSmoothJet μ f).2 z=smoothScalarGradient f z at hg
  change (surfaceMultiplier μ q u.1) z=_ at hq
  simp only [hf,hg,hq,smul_eq_mul,Pi.mul_apply,
    RCLike.inner_apply,RCLike.conj_to_real]
  ring

lemma periodicGraphScalar_zero_jet (a n : Cover) {χ : Cover → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hO : tsupport χ ⊆ {x | ∀ i,0<x i ∧ x i<1})
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (z : NormalBundle)
    (hz : (z.1 : Cover)∉tsupport χ) :
    smoothScalarValue (periodicGraphScalar a n hχ hc hψ) z=0 ∧
    smoothScalarGradient (periodicGraphScalar a n hχ hc hψ) z=0 := by
  have he := periodicGraphScalar_zero_germ a n hχ hc hO hψ z.1 hz
  refine ⟨he.eq_of_nhds,?_⟩
  have hd := he.fderiv_eq (𝕜 := ℝ)
  change gradient (periodicGraphScalar a n hχ hc hψ).val z.1-
    ⟪(z.2 : Cover),gradient (periodicGraphScalar a n hχ hc hψ).val z.1⟫ • (z.2 : Cover)=0
  simp [gradient,hd]

lemma surfaceJacobiB_periodicGraphScalar_weight (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (u : SurfaceJet μ)
    (a n : Cover) {χ : Cover → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hO : tsupport χ ⊆ {x | ∀ i,0<x i ∧ x i<1})
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {φ : Cover → ℝ} (hunit : ∀ x∈tsupport χ,φ x=1) :
    surfaceJacobiB μ q u (surfaceSmoothJet μ (periodicGraphScalar a n hχ hc hψ))=
      ∫ z,φ z.1*(⟪u.2 z,smoothScalarGradient (periodicGraphScalar a n hχ hc hψ) z⟫-
        q z*u.1 z*smoothScalarValue (periodicGraphScalar a n hχ hc hψ) z) ∂(μ : Measure NormalBundle) := by
  rw [surfaceJacobiB_smooth_integral]
  apply integral_congr_ae
  filter_upwards [] with z
  by_cases hz : (z.1 : Cover)∈tsupport χ
  · rw [hunit _ hz,one_mul]
  · obtain ⟨hv,hg⟩ := periodicGraphScalar_zero_jet a n hχ hc hO hψ z hz
    simp only [hv,hg,inner_zero_right,mul_zero,sub_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem surfaceJacobiB_chart_form (μ : FiniteMeasure NormalBundle)
    (q : Lp ℝ ∞ (μ : Measure NormalBundle)) (u : SurfaceJet μ)
    (a : Cover) {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ} (hg : Continuous g)
    {φ : Cover → ℝ} (hφ : Measurable φ) (hφ0 : ∀ x,0≤φ x)
    (hφO : tsupport φ ⊆ {x | ∀ i,0<x i ∧ x i<1})
    (hm : (μ : Measure NormalBundle).withDensity (fun z => ENNReal.ofReal (φ z.1)) =
      Measure.map (actualNormalGraphChart a hn g)
        (volume.withDensity (fun y => ENNReal.ofReal
          (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖))))
    (hgc : ∀ y,φ (a+normalGraph n g y)≠0 → DifferentiableAt ℝ g y)
    {χ : Cover → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ {x | ∀ i,0<x i ∧ x i<1})
    (hφχ : ∀ x∈tsupport χ,φ x=1)
    {S : Set Plane} (hS : IsOpen S)
    (hunit : ∀ y∈S,χ (a+normalGraph n g y)=1)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hs : tsupport ψ⊆S) :
    surfaceJacobiB μ q u (surfaceSmoothJet μ (periodicGraphScalar a n hχ hc hψ))=
      ∫ y in S,(cmcWeight (gradient g y))^2*
        ⟪graphCovector n g y (u.2 (actualNormalGraphChart a hn g y)),
          cmcJacobian (gradient g y) (gradient ψ y)⟫-
        cmcWeight (gradient g y)*q (actualNormalGraphChart a hn g y)*
          u.1 (actualNormalGraphChart a hn g y)*ψ y := by
  let f := periodicGraphScalar a n hχ hc hψ
  have hF : AEStronglyMeasurable (fun z => ⟪u.2 z,smoothScalarGradient f z⟫-
        q z*u.1 z*smoothScalarValue f z) (μ : Measure NormalBundle) :=
    (Lp.aestronglyMeasurable u.2 |>.inner (smoothScalarGradient f).continuous.aestronglyMeasurable).sub
      (((Lp.aestronglyMeasurable q).mul (Lp.aestronglyMeasurable u.1)).mul
        (smoothScalarValue f).continuous.aestronglyMeasurable)
  rw [surfaceJacobiB_periodicGraphScalar_weight μ q u a n hχ hc hχO hψ hφχ,
    graph_area_integral a hn hg hφ hφ0 hm hF,← integral_indicator hS.measurableSet]
  apply integral_congr_ae
  filter_upwards [] with y
  have hφS {y : Plane} (hy : y∈S) : φ (a+normalGraph n g y)=1 := by
    apply hφχ
    apply subset_tsupport
    rw [Function.mem_support,hunit y hy]
    exact one_ne_zero
  by_cases hyφ : φ (a+normalGraph n g y)=0
  · have hyS : y∉S := by intro hy; have := hφS hy; exact zero_ne_one (hyφ.symm.trans this)
    simp only [hyφ,zero_mul,indicator_of_notMem hyS]
  · have hypos : ∀ i,(a+normalGraph n g y) i∈Icc 0 1 := by
      have hx : a+normalGraph n g y∈tsupport φ := subset_tsupport _ hyφ
      exact fun i => ⟨(hφO hx i).1.le,(hφO hx i).2.le⟩
    have hv := periodicGraphScalar_graph_value a hn hχ hc hχO hψ hg hS hunit hs hypos
    have hgrad := periodicGraphScalar_graph_covector a hn hχ hc hχO hψ hg hS hunit hs
      (hgc y hyφ) hypos
    have ht := smoothScalarGradient_tangent f (actualNormalGraphChart a hn g y)
    rw [actualNormalGraphChart_normal] at ht
    rw [graphCovector_metric_pairing hn g y _ _ ht,hgrad,hv,graphAreaVector_norm_sqrt hn]
    change φ (a+normalGraph n g y)*cmcWeight (gradient g y)*
      (cmcWeight (gradient g y)*⟪_,_⟫-_*_*ψ y)=_
    by_cases hyS : y∈S
    · rw [indicator_of_mem hyS,hφS hyS]
      ring
    · have hyψ : y∉tsupport ψ := fun h => hyS (hs h)
      have hgz : gradient ψ y=0 := by simp [gradient,fderiv_of_notMem_tsupport ℝ hyψ]
      rw [indicator_of_notMem hyS,image_eq_zero_of_notMem_tsupport hyψ,hgz,map_zero,inner_zero_right]
      ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma L2_measure_scalar_test_integrable {ν : Measure Plane} (u : Lp ℝ 2 ν)
    {ψ : Plane → ℝ} (hψ : MemLp ψ 2 ν) : Integrable (fun y => u y*ψ y) ν :=
  (Lp.memLp u).integrable_mul hψ

lemma L2_measure_vector_test_integrable {ν : Measure Plane} (G : Lp Plane 2 ν)
    {F : Plane → Plane} (hF : MemLp F 2 ν) : Integrable (fun y => ⟪G y,F y⟫) ν := by
  apply (L2.integrable_inner (𝕜 := ℝ) G (hF.toLp F)).congr
  filter_upwards [hF.coeFn_toLp] with y hy
  exact congrArg (inner ℝ (G y)) hy

theorem PlaneWeakGradientOn.vector_ibp {S : Set Plane}
    {u : Lp ℝ 2 (volume.restrict S)} {G : Lp Plane 2 (volume.restrict S)}
    (hw : PlaneWeakGradientOn S u G)
    {F : Plane → Plane} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hc : HasCompactSupport F) (hs : tsupport F⊆S) :
    (∫ y in S,⟪G y,F y⟫)= -(∫ y in S,u y*planeDivergence F y) := by
  let e (i : Fin 2) : Plane := EuclideanSpace.single i 1
  let D (i : Fin 2) : Plane → ℝ := fun y => F y i
  have hD (i) : ContDiff ℝ (⊤ : ℕ∞) (D i) :=
    (EuclideanSpace.proj i : Plane →L[ℝ] ℝ).contDiff.comp hF
  have hsD (i) : tsupport (D i)⊆tsupport F := by
    apply closure_mono
    intro y hy
    change F y≠0
    intro hz
    apply hy
    change F y i=0
    rw [hz]
    rfl
  have hcD (i) : HasCompactSupport (D i) := hc.of_isClosed_subset (isClosed_tsupport _) (hsD i)
  have hi (i) : Integrable (fun y => G y i*F y i) (volume.restrict S) := by
    exact ((EuclideanSpace.proj i : Plane →L[ℝ] ℝ).comp_memLp G).integrable_mul
      (((hD i).continuous.memLp_of_hasCompactSupport (p := 2) (hcD i)).mono_measure Measure.restrict_le_self)
  have hj (i) : Integrable (fun y => u y*fderiv ℝ (D i) y (e i)) (volume.restrict S) :=
    L2_measure_scalar_test_integrable u
      ((((hD i).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        ((hcD i).fderiv_apply ℝ (e i)) |>.mono_measure Measure.restrict_le_self)
  have he (i) := hw (e i) (D i) (hD i) (hcD i) ((hsD i).trans hs)
  simp only [e,EuclideanSpace.inner_single_right,conj_trivial,one_mul,D] at he
  have hj' (i) : Integrable (fun y => u y*(fderiv ℝ F y (e i)) i) (volume.restrict S) := by
    simpa only [D,plane_component_fderiv (hF.of_le (by simp))] using hj i
  simp_rw [plane_component_fderiv (hF.of_le (by simp))] at he
  simp_rw [plane_inner_components,planeDivergence,mul_add]
  rw [integral_add (hi 0) (hi 1),integral_add (hj' 0) (hj' 1),he 0,he 1]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeDivergence_hasCompactSupport {F : Plane → Plane}
    (hc : HasCompactSupport F) : HasCompactSupport (planeDivergence F) := by
  apply hc.mono'
  intro y hy
  by_contra hys
  have hz := fderiv_of_notMem_tsupport ℝ hys
  apply hy
  simp [planeDivergence,hz]

theorem PlaneWeakGradientOn.ground_state {S : Set Plane}
    {u : Lp ℝ 2 (volume.restrict S)} {G : Lp Plane 2 (volume.restrict S)}
    (hw : PlaneWeakGradientOn S u G)
    {A : Plane → Plane →L[ℝ] Plane} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hAs : ∀ y v w,⟪v,A y w⟫=⟪w,A y v⟫)
    {q ψ : Plane → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆S) :
    (∫ y in S,(q y)^2*⟪G y,A y (gradient ψ y)⟫-
      q y*planeDivergence (fun z => A z (gradient q z)) y*u y*ψ y)=
    ∫ y in S,⟪q y • G y+u y • gradient q y,
      A y (gradient (fun z => q z*ψ z) y)⟫ := by
  have hgq := plane_gradient_contDiff hq
  have hgψ := plane_gradient_contDiff hψ
  let H : Plane → Plane := fun y => A y (gradient q y)
  let F : Plane → Plane := fun y => (q y*ψ y) • H y
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := hA.clm_apply hgq
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := (hq.mul hψ).smul hH
  have hcF : HasCompactSupport F := hc.mul_left.smul_right
  have hsF : tsupport F⊆S :=
    (tsupport_smul_subset_left _ _).trans (tsupport_mul_subset_right.trans hs)
  have hibp := hw.vector_ibp hF hcF hsF
  have hiF : Integrable (fun y => ⟪G y,F y⟫) (volume.restrict S) :=
    L2_measure_vector_test_integrable G
      ((hF.continuous.memLp_of_hasCompactSupport hcF).mono_measure Measure.restrict_le_self)
  have hiD : Integrable (fun y => u y*planeDivergence F y) (volume.restrict S) :=
    L2_measure_scalar_test_integrable u
      (((planeDivergence_continuous (hF.of_le (by simp))).memLp_of_hasCompactSupport
        (planeDivergence_hasCompactSupport hcF)).mono_measure Measure.restrict_le_self)
  let V : Plane → Plane := fun y => (q y)^2 • A y (gradient ψ y)
  have hV : ContDiff ℝ (⊤ : ℕ∞) V := (hq.pow 2).smul (hA.clm_apply hgψ)
  have hcV : HasCompactSupport V := by
    apply hc.mono'
    intro y hy
    by_contra hys
    have hz : gradient ψ y=0 := by simp [gradient,fderiv_of_notMem_tsupport ℝ hys]
    apply hy
    simp [V,hz]
  have hiV : Integrable (fun y => (q y)^2*⟪G y,A y (gradient ψ y)⟫)
      (volume.restrict S) := by
    simpa only [V,real_inner_smul_right] using L2_measure_vector_test_integrable G
      ((hV.continuous.memLp_of_hasCompactSupport hcV).mono_measure Measure.restrict_le_self)
  have hiP : Integrable (fun y => q y*planeDivergence H y*u y*ψ y)
      (volume.restrict S) := by
    have hi := L2_measure_scalar_test_integrable u
      ((((hq.continuous.mul (planeDivergence_continuous (hH.of_le (by simp)))).mul
        hψ.continuous).memLp_of_hasCompactSupport hc.mul_left).mono_measure
          (ν := volume.restrict S) Measure.restrict_le_self)
    apply hi.congr
    filter_upwards [] with y
    simp only [Pi.mul_apply]
    ring
  have hpoint (y : Plane) :
      ⟪q y • G y+u y • gradient q y,A y (gradient (fun z => q z*ψ z) y)⟫=
      ((q y)^2*⟪G y,A y (gradient ψ y)⟫-q y*planeDivergence H y*u y*ψ y)+
        (⟪G y,F y⟫+u y*planeDivergence F y) := by
    have hdq := hq.differentiable (by simp) y
    have hdψ := hψ.differentiable (by simp) y
    have hdiv : planeDivergence F y=(q y*ψ y)*planeDivergence H y+
        ⟪gradient (fun z => q z*ψ z) y,H y⟫ :=
      planeDivergence_smul (hdq.mul hdψ) (hH.differentiable (by simp) y)
    rw [hdiv,plane_gradient_mul hdq hdψ]
    simp only [F,map_add,map_smul,inner_add_left,inner_add_right,
      real_inner_smul_left,real_inner_smul_right,H]
    rw [hAs y (gradient q y) (gradient ψ y)]
    ring
  simp_rw [hpoint]
  have hsum := integral_add (hiV.sub hiP) (hiF.add hiD)
  have hsum2 := integral_add hiF hiD
  simp only [Pi.add_apply,Pi.sub_apply] at hsum hsum2
  rw [hsum,hsum2,hibp]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma PlaneWeakGradientOn.toWeakGradient {S : Set Plane} {u : Plane → ℝ} {G : Plane → Plane}
    (hw : PlaneWeakGradientOn S u G) : PlaneWeakGradient S u G := by
  intro v ψ hψ hc hs
  have h₁ : (∫ y in S,⟪G y,v⟫*ψ y)=(∫ y,⟪G y,v⟫*ψ y) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hs h)),mul_zero]
  have h₂ : (∫ y in S,u y*fderiv ℝ ψ y v)=(∫ y,u y*fderiv ℝ ψ y v) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hy (hs h))]
    simp
  rw [← h₁,← h₂]
  exact hw v ψ hψ hc hs

lemma L2_measure_direction_test_integrable {S : Set Plane}
    (G : Lp Plane 2 (volume.restrict S)) (v : Plane) {ψ : Plane → ℝ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun y => ⟪G y,v⟫*ψ y) (volume.restrict S) := by
  have htest : MemLp (fun y => ψ y • v) 2 (volume.restrict S) :=
    ((hψ.smul continuous_const).memLp_of_hasCompactSupport hc.smul_right).mono_measure
      Measure.restrict_le_self
  apply (L2_measure_vector_test_integrable G htest).congr
  filter_upwards [] with y
  rw [real_inner_smul_right,mul_comm]

theorem PlaneWeakGradientOn.mul_smooth {S : Set Plane}
    {u : Lp ℝ 2 (volume.restrict S)} {G : Lp Plane 2 (volume.restrict S)}
    (hw : PlaneWeakGradientOn S u G) {q : Plane → ℝ}
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    PlaneWeakGradientOn S (fun y => q y*u y)
      (fun y => q y • G y+u y • gradient q y) := by
  intro v ψ hψ hc hs
  let dq : Plane → ℝ := fun y => fderiv ℝ q y v
  let dψ : Plane → ℝ := fun y => fderiv ℝ ψ y v
  have hdq : Continuous dq := (hq.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdψ : Continuous dψ := (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hi₁ := L2_measure_direction_test_integrable G v (hq.continuous.mul hψ.continuous) hc.mul_left
  simp only [Pi.mul_apply] at hi₁
  have hi₂ : Integrable (fun y => u y*(q y*dψ y)) (volume.restrict S) :=
    L2_measure_scalar_test_integrable u
      (((hq.continuous.mul hdψ).memLp_of_hasCompactSupport
        ((hc.fderiv_apply ℝ v).mul_left)).mono_measure Measure.restrict_le_self)
  have hi₃ : Integrable (fun y => u y*(ψ y*dq y)) (volume.restrict S) :=
    L2_measure_scalar_test_integrable u
      (((hψ.continuous.mul hdq).memLp_of_hasCompactSupport hc.mul_right).mono_measure
        Measure.restrict_le_self)
  have he := hw v (fun y => q y*ψ y) (hq.mul hψ) hc.mul_left
    (tsupport_mul_subset_right.trans hs)
  have he' : (∫ y in S,⟪G y,v⟫*(q y*ψ y))=
      -((∫ y in S,u y*(q y*dψ y))+(∫ y in S,u y*(ψ y*dq y))) := by
    rw [he,← integral_add hi₂ hi₃]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [fderiv_fun_mul (hq.differentiable (by simp) y) (hψ.differentiable (by simp) y),
      add_apply,smul_apply,smul_eq_mul,dq,dψ]
    ring
  have hleft : (∫ y in S,⟪q y • G y+u y • gradient q y,v⟫*ψ y)=
      (∫ y in S,⟪G y,v⟫*(q y*ψ y))+(∫ y in S,u y*(ψ y*dq y)) := by
    rw [← integral_add hi₁ hi₃]
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [inner_add_left,real_inner_smul_left,inner_gradient_left,dq]
    ring
  rw [hleft,he']
  have hright : (∫ y in S,q y*u y*fderiv ℝ ψ y v)=(∫ y in S,u y*(q y*dψ y)) := by
    apply integral_congr_ae
    filter_upwards [] with y
    dsimp only [dψ]
    ring
  rw [hright]
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem PlaneWeakGradientOn.linearize {S : Set Plane}
    {u : Lp ℝ 2 (volume.restrict S)} {G : Lp Plane 2 (volume.restrict S)}
    (hw : PlaneWeakGradientOn S u G)
    {A : Plane → Plane →L[ℝ] Plane} (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hAs : ∀ y v w,⟪v,A y w⟫=⟪w,A y v⟫)
    {q : Plane → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hq0 : ∀ y,q y≠0)
    (hJ : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆S → (∫ y in S,(q y)^2*⟪G y,A y (gradient ψ y)⟫-
        q y*planeDivergence (fun z => A z (gradient q z)) y*u y*ψ y)=0) :
    ∀ η : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η⊆S → (∫ y,fderiv ℝ η y (A y (q y • G y+u y • gradient q y)))=0 := by
  intro η hη hc hs
  let ψ : Plane → ℝ := fun y => η y/q y
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hη.div hq hq0
  have hsψ : tsupport ψ⊆tsupport η := by
    apply closure_mono
    intro y hy
    change η y≠0
    intro hz
    apply hy
    simp [ψ,hz]
  have hcψ : HasCompactSupport ψ := hc.of_isClosed_subset (isClosed_tsupport _) hsψ
  have hefun : (fun z => q z*ψ z)=η := by
    funext z
    exact mul_div_cancel₀ _ (hq0 z)
  have he := hw.ground_state hA hAs hq hψ hcψ (hsψ.trans hs)
  rw [hJ ψ hψ hcψ (hsψ.trans hs),hefun] at he
  have hi : (∫ y in S,⟪q y • G y+u y • gradient q y,A y (gradient η y)⟫)=0 := he.symm
  rw [← hi]
  symm
  calc
    (∫ y in S,⟪q y • G y+u y • gradient q y,A y (gradient η y)⟫)=
        ∫ y in S,fderiv ℝ η y (A y (q y • G y+u y • gradient q y)) := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [hAs,inner_gradient_left]
    _ = _ := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro y hy
      rw [fderiv_of_notMem_tsupport ℝ (fun h => hy (hs h))]
      rfl

theorem weak_cmc_graph_jacobi_linearization {S : Set Plane} (hS : IsOpen S)
    {u : Lp ℝ 2 (volume.restrict S)} {G : Lp Plane 2 (volume.restrict S)}
    (hw : PlaneWeakGradientOn S u G) {g : Plane → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hlin : ∀ i : Fin 2,LinearCMCEquation
      (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) (gradient g) (fun _ => 0) S)
    (hJ : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆S → (∫ y in S,(cmcWeight (gradient g y))^2*
        ⟪G y,cmcJacobian (gradient g y) (gradient ψ y)⟫-
        cmcWeight (gradient g y)*graphSquaredSecondFundamentalForm g y*u y*ψ y)=0) :
    ∀ η : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η → tsupport η⊆S →
      (∫ y,fderiv ℝ η y (cmcJacobian (gradient g y)
        (cmcWeight (gradient g y) • G y+
          u y • gradient (fun z => cmcWeight (gradient g z)) y)))=0 := by
  apply hw.linearize (cmcJacobian_contDiff.comp (plane_gradient_contDiff hg))
    (fun y v w => (cmcJacobian_symmetric (gradient g y) v w).trans (real_inner_comm _ _))
    (cmcWeight_contDiff.comp (plane_gradient_contDiff hg))
    (fun y => (cmcWeight_pos _).ne')
  intro ψ hψ hc hs
  rw [← hJ ψ hψ hc hs]
  apply setIntegral_congr_fun hS.measurableSet
  intro y hy
  dsimp only [Function.comp_def]
  rw [cmc_graph_curvature_potential hg hS hlin hy]

end CubicTorus

end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_SurfaceNormalReverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma restricted_L2_extension {F : Type*} [NormedAddCommGroup F]
    {S : Set Plane} (hS : MeasurableSet S) (u : Lp F 2 (volume.restrict S)) :
    ∃ U : Lp F 2 (volume : Measure Plane),
      (U : Plane → F) =ᵐ[volume.restrict S] (u : Plane → F) := by
  have hm : MemLp (S.indicator (u : Plane → F)) 2 (volume : Measure Plane) :=
    (memLp_indicator_iff_restrict hS).mpr (Lp.memLp u)
  refine ⟨hm.toLp _, ?_⟩
  filter_upwards [ae_restrict_of_ae hm.coeFn_toLp, ae_restrict_mem hS] with y hy hys
  exact hy.trans (indicator_of_mem hys _)

theorem PlaneWeakGradientOn.cmc_classical_near
    {p : Plane → Plane} (hp : Continuous p) (hpb : ∀ y, ‖p y‖ ≤ 1)
    {R α D : ℝ} (hR : 0 < R) (hα : 0 < α) (hα1 : α ≤ 1) (hD : 0 ≤ D)
    (hHolder : ∀ x ∈ Metric.ball (0 : Plane) R, ∀ y ∈ Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x) - cmcJacobian (p y)‖ ≤ D * (dist x y)^α)
    {u : Lp ℝ 2 (volume.restrict (Metric.ball (0 : Plane) R))}
    {G : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) R))}
    (hw : PlaneWeakGradientOn (Metric.ball 0 R) u G)
    (hd : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball 0 R →
        (∫ y, fderiv ℝ ψ y (cmcJacobian (p y) (G y))) = 0)
    {f : Plane → ℝ} (hf : ContinuousOn f (Metric.ball 0 R))
    (hfu : f =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)] (u : Plane → ℝ)) :
    HolderJet 1 f 0 ∧ LinearCMCEquationNear f p (fun _ => 0) := by
  obtain ⟨U,hU⟩ := restricted_L2_extension measurableSet_ball u
  obtain ⟨V,hV⟩ := restricted_L2_extension measurableSet_ball G
  have hUV := hw.toWeakGradient.local_congr measurableSet_ball hU hV
  have hVD : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball 0 R →
        (∫ y, fderiv ℝ ψ y (cmcJacobian (p y) (V y))) = 0 := by
    intro ψ hψ hc hs
    rw [← hd ψ hψ hc hs]
    apply integral_congr_ae
    filter_upwards [(ae_restrict_iff' measurableSet_ball).mp hV] with y hy
    by_cases hys : y ∈ Metric.ball (0 : Plane) R
    · rw [hy hys]
    · rw [fderiv_of_notMem_tsupport ℝ (fun hh => hys (hs hh))]
      rfl
  obtain ⟨H,s,K,β,hs,hsR,hK,hβ,hβ1,hHc,hHe,hHp⟩ :=
    cmc_linearized_holder_gradient hp hpb hR hα hα1 hD hHolder U V hUV hVD
  have hsub : Metric.ball (0 : Plane) s ⊆ Metric.ball 0 R :=
    Metric.ball_subset_ball (by linarith)
  have hfu' : f =ᵐ[volume.restrict (Metric.ball (0 : Plane) s)] (u : Plane → ℝ) :=
    ae_restrict_of_ae_restrict_of_subset hsub hfu
  have hU' : (U : Plane → ℝ) =ᵐ[volume.restrict (Metric.ball (0 : Plane) s)] (u : Plane → ℝ) :=
    ae_restrict_of_ae_restrict_of_subset hsub hU
  have hwf : PlaneWeakGradient (Metric.ball 0 s) f H :=
    (hUV.mono hsub).local_congr measurableSet_ball
      (hfu'.trans hU'.symm) hHe
  obtain ⟨hfc,hfd⟩ := hwf.holder_C1 hs (hf.mono hsub) hHc hHp
  have hdr (y : Plane) (hy : y ∈ Metric.ball (0 : Plane) (s / 4)) :
      gradient f y = H y := by
    have ht := hwf.continuous_hasFDerivAt hs (hf.mono hsub) hHc hy
    simp only [gradient, ht.fderiv, LinearIsometryEquiv.symm_apply_apply]
  refine ⟨⟨hfc.contDiffAt (Metric.ball_mem_nhds _ (by positivity)),
    s / 4, β, K, by positivity, hβ, hβ1, hK, hfd⟩, s / 4, by positivity, ?_⟩
  intro ψ hψ hc ht
  have hss : Metric.ball (0 : Plane) (s/4) ⊆ Metric.ball 0 s :=
    Metric.ball_subset_ball (by linarith)
  rw [← hVD ψ hψ hc (ht.trans (hss.trans hsub))]
  apply integral_congr_ae
  filter_upwards [(ae_restrict_iff' measurableSet_ball).mp hHe] with y hy
  by_cases hys : y ∈ Metric.ball (0 : Plane) (s/4)
  · simp only [hdr y hys, hy (hss hys), sub_zero]
  · rw [fderiv_of_notMem_tsupport ℝ (fun hh => hys (ht hh))]
    rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem PlaneWeakGradientOn.cmc_smoothAt
    {p : Plane → Plane} (hp : Continuous p) (hpb : ∀ y, ‖p y‖ ≤ 1)
    {R α D : ℝ} (hR : 0 < R) (hα : 0 < α) (hα1 : α ≤ 1) (hD : 0 ≤ D)
    (hHolder : ∀ x ∈ Metric.ball (0 : Plane) R, ∀ y ∈ Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x) - cmcJacobian (p y)‖ ≤ D * (dist x y)^α)
    (hpc : ContDiffAt ℝ (⊤ : ℕ∞) p 0)
    {u : Lp ℝ 2 (volume.restrict (Metric.ball (0 : Plane) R))}
    {G : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) R))}
    (hw : PlaneWeakGradientOn (Metric.ball 0 R) u G)
    (hd : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball 0 R →
        (∫ y, fderiv ℝ ψ y (cmcJacobian (p y) (G y))) = 0)
    {f : Plane → ℝ} (hf : ContinuousOn f (Metric.ball 0 R))
    (hfu : f =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)] (u : Plane → ℝ)) :
    ContDiffAt ℝ (⊤ : ℕ∞) f 0 := by
  obtain ⟨hfc,heq⟩ := hw.cmc_classical_near hp hpb hR hα hα1 hD hHolder hd hf hfu
  apply contDiffAt_infty.mpr
  intro n
  have hpJ : HolderJet (n+1) p 0 := ContDiffAt.holderJet (hpc.of_le (by
    exact_mod_cast (show (n+2 : ℕ∞) ≤ ⊤ from le_top)))
  exact (heq.schauder hpb hfc hpJ (HolderJet.const 0)).contDiffAt.of_le (by norm_cast; omega)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuous_memLp_top_ball {F : Type*} [NormedAddCommGroup F]
    {f : Plane → F} (hf : Continuous f) (R : ℝ) :
    MemLp f ∞ (volume.restrict (Metric.ball (0 : Plane) R)) := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Plane) R).exists_bound_of_continuousOn hf.continuousOn
  exact memLp_top_of_bound hf.aestronglyMeasurable C
    ((ae_restrict_mem measurableSet_ball).mono fun y hy => hC y (Metric.ball_subset_closedBall hy))

theorem PlaneWeakGradientOn.weighted_L2 {R : ℝ}
    {u : Lp ℝ 2 (volume.restrict (Metric.ball (0 : Plane) R))}
    {G : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) R))}
    (hw : PlaneWeakGradientOn (Metric.ball 0 R) u G)
    {q : Plane → ℝ} (hq : ContDiff ℝ (⊤ : ℕ∞) q) :
    ∃ (v : Lp ℝ 2 (volume.restrict (Metric.ball (0 : Plane) R)))
      (J : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) R))),
      (v =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)] fun y => q y * u y) ∧
      (J =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)]
        fun y => q y • G y + u y • gradient q y) ∧
      PlaneWeakGradientOn (Metric.ball 0 R) v J := by
  have hqL := continuous_memLp_top_ball hq.continuous R
  have hdL := continuous_memLp_top_ball (plane_gradient_contDiff hq).continuous R
  have hv : MemLp (fun y => q y * u y) 2 (volume.restrict (Metric.ball (0 : Plane) R)) :=
    (Lp.memLp u).mul hqL
  have hJ : MemLp (fun y => q y • G y + u y • gradient q y) 2
      (volume.restrict (Metric.ball (0 : Plane) R)) :=
    ((Lp.memLp G).smul hqL).add (hdL.smul (Lp.memLp u))
  refine ⟨hv.toLp _,hJ.toLp _,hv.coeFn_toLp,hJ.coeFn_toLp,?_⟩
  exact (hw.mul_smooth hq).congr hv.coeFn_toLp hJ.coeFn_toLp

theorem PlaneWeakGradientOn.jacobi_smoothAt
    {p : Plane → Plane} (hp : Continuous p) (hpb : ∀ y, ‖p y‖ ≤ 1)
    {R α D : ℝ} (hR : 0 < R) (hα : 0 < α) (hα1 : α ≤ 1) (hD : 0 ≤ D)
    (hHolder : ∀ x ∈ Metric.ball (0 : Plane) R, ∀ y ∈ Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x) - cmcJacobian (p y)‖ ≤ D * (dist x y)^α)
    (hpc : ContDiffAt ℝ (⊤ : ℕ∞) p 0)
    {g : Plane → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hpe : ∀ y ∈ Metric.ball (0 : Plane) R, p y = gradient g y)
    (hlin : ∀ i : Fin 2, LinearCMCEquation
      (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) (gradient g)
      (fun _ => 0) (Metric.ball 0 R))
    {u : Lp ℝ 2 (volume.restrict (Metric.ball (0 : Plane) R))}
    {G : Lp Plane 2 (volume.restrict (Metric.ball (0 : Plane) R))}
    (hw : PlaneWeakGradientOn (Metric.ball 0 R) u G)
    (hJ : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball 0 R →
      (∫ y in Metric.ball (0 : Plane) R, (cmcWeight (gradient g y))^2 *
        ⟪G y, cmcJacobian (gradient g y) (gradient ψ y)⟫ -
        cmcWeight (gradient g y) * graphSquaredSecondFundamentalForm g y * u y * ψ y) = 0)
    {f : Plane → ℝ} (hf : ContinuousOn f (Metric.ball 0 R))
    (hfu : f =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)] (u : Plane → ℝ)) :
    ContDiffAt ℝ (⊤ : ℕ∞) f 0 := by
  let q : Plane → ℝ := fun y => cmcWeight (gradient g y)
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := cmcWeight_contDiff.comp (plane_gradient_contDiff hg)
  obtain ⟨v,J,hv,hJv,hwJ⟩ := hw.weighted_L2 hq
  have hde := weak_cmc_graph_jacobi_linearization Metric.isOpen_ball hw hg hlin hJ
  have hd : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ Metric.ball 0 R →
        (∫ y, fderiv ℝ ψ y (cmcJacobian (p y) (J y))) = 0 := by
    intro ψ hψ hc hs
    rw [← hde ψ hψ hc hs]
    apply integral_congr_ae
    filter_upwards [(ae_restrict_iff' measurableSet_ball).mp hJv] with y hy
    by_cases hys : y ∈ Metric.ball (0 : Plane) R
    · rw [hy hys, hpe y hys]
    · rw [fderiv_of_notMem_tsupport ℝ (fun hh => hys (hs hh))]
      rfl
  have hvf : (fun y => q y * f y) =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)]
      (v : Plane → ℝ) := by
    filter_upwards [hv,hfu] with y hyv hyf
    rw [hyv,hyf]
  have hsm := hwJ.cmc_smoothAt hp hpb hR hα hα1 hD hHolder hpc hd
    (hq.continuous.continuousOn.mul hf) hvf
  have heq : f = fun y => (q y * f y)/q y := by
    funext y
    rw [mul_div_cancel_left₀ _ (cmcWeight_pos _).ne']
  rw [heq]
  exact hsm.div hq.contDiffAt (cmcWeight_pos _).ne'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem surfaceH1_jacobi_graph_smoothAt_oai
    (μ : FiniteMeasure NormalBundle) (q : Lp ℝ ∞ (μ : Measure NormalBundle))
    {u : SurfaceJet μ} (hu : u∈surfaceH1 μ)
    (hhom : ∀ z∈surfaceH1 μ, surfaceJacobiB μ q u z=0)
    (a : Cover) {n : Cover} (hn : ‖n‖=1) {g : Plane → ℝ} {K : ℝ≥0}
    (hgL : LipschitzWith K g) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {φ : Cover → ℝ} (hφ : Measurable φ) (hφb : ∀ x, φ x∈Icc 0 1)
    (hφO : tsupport φ ⊆ {x | ∀ i, 0<x i ∧ x i<1})
    (hm : (μ : Measure NormalBundle).withDensity (fun z => ENNReal.ofReal (φ z.1)) =
      Measure.map (actualNormalGraphChart a hn g)
        (volume.withDensity (fun y => ENNReal.ofReal
          (φ (a+normalGraph n g y)*‖graphAreaVector n g y‖))))
    {χ : Cover → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hχO : tsupport χ ⊆ {x | ∀ i, 0<x i ∧ x i<1})
    (hφχ : ∀ x∈tsupport χ, φ x=1)
    {R α D : ℝ} (hR : 0<R) (hα : 0<α) (hα1 : α≤1) (hD : 0≤D)
    (hunit : ∀ y∈Metric.ball (0 : Plane) R, χ (a+normalGraph n g y)=1)
    {p : Plane → Plane} (hp : Continuous p) (hpb : ∀ y, ‖p y‖≤1)
    (hpc : ContDiffAt ℝ (⊤ : ℕ∞) p 0)
    (hpe : ∀ y∈Metric.ball (0 : Plane) R, p y=gradient g y)
    (hHolder : ∀ x∈Metric.ball (0 : Plane) R, ∀ y∈Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*(dist x y)^α)
    (hlin : ∀ i : Fin 2, LinearCMCEquation
      (fun y => fderiv ℝ g y (EuclideanSpace.single i 1)) (gradient g)
      (fun _ => 0) (Metric.ball 0 R))
    (hqp : (fun y => q (actualNormalGraphChart a hn g y))
      =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)] graphSquaredSecondFundamentalForm g)
    {f : Plane → ℝ} (hf : ContinuousOn f (Metric.ball 0 R))
    (hfu : f =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)]
      fun y => u.1 (actualNormalGraphChart a hn g y)) :
    ContDiffAt ℝ (⊤ : ℕ∞) f 0 := by
  have hφunit (y : Plane) (hy : y∈Metric.ball (0 : Plane) R) : φ (a+normalGraph n g y)=1 := by
    apply hφχ
    apply subset_tsupport
    rw [Function.mem_support,hunit y hy]
    exact one_ne_zero
  have hd := graph_chart_measure_le a hn hg.continuous hφb hm measurableSet_ball hφunit
  have hcell (y : Plane) (hy : y∈Metric.ball (0 : Plane) R) (i : Fin 3) :
      (a+normalGraph n g y) i∈Icc 0 1 := by
    have hz : a+normalGraph n g y∈tsupport φ := subset_tsupport _ (by
      rw [Function.mem_support,hφunit y hy]; exact one_ne_zero)
    exact ⟨(hφO hz i).1.le,(hφO hz i).2.le⟩
  let hchart := actualNormalGraphChart_measurable a hn hg.continuous
  let v := lpPullbackLE hchart hd u.1
  let w := lpPullbackLE hchart hd u.2
  let G := graphCovectorLp hn hgL w
  have hv := lpPullbackLE_ae hchart hd u.1
  have hG : G =ᵐ[volume.restrict (Metric.ball (0 : Plane) R)]
      fun y => graphCovector n g y (u.2 (actualNormalGraphChart a hn g y)) := by
    filter_upwards [graphCovectorLp_ae hn hgL w,lpPullbackLE_ae hchart hd u.2] with y hy hz
    change G y=graphCovector n g y (w y) at hy
    change w y=u.2 (actualNormalGraphChart a hn g y) at hz
    rw [hy,hz]
  have hw := surfaceH1_chart_weak_gradient μ a hn hgL Metric.isOpen_ball
    (hg.of_le (by simp)).contDiffOn hcell hd hu
  apply hw.jacobi_smoothAt hp hpb hR hα hα1 hD hHolder hpc hg hpe hlin
  · intro ψ hψ hψc hs
    have he := surfaceJacobiB_chart_form μ q u a hn hg.continuous hφ
      (fun x => (hφb x).1) hφO hm (fun y _ => hg.differentiable (by simp) y)
      hχ hc hχO hφχ Metric.isOpen_ball hunit hψ hs
    rw [hhom _ (subset_closure (LinearMap.mem_range_self _ _))] at he
    refine Eq.trans ?_ he.symm
    apply integral_congr_ae
    filter_upwards [hv,hG,hqp] with y hy hz hqz
    change v y=u.1 (actualNormalGraphChart a hn g y) at hy
    rw [hy,hz,hqz]
  · exact hf
  · exact hfu.trans hv.symm

end CubicTorus

end
end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.surfaceH1_jacobi_graph_smoothAt_oai := @OAI.CubicTorus.surfaceH1_jacobi_graph_smoothAt_oai
