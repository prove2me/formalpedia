-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorSmooth_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:45:47.551829+00:00
-- url     : https://prove2.me/submissions/7ea39eb3-fabd-427a-affb-6f1f6a1d931a

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingConvolution
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smoothing operators from the finite-moment kernels. They are
linear on locally integrable inputs, smooth their outputs, and fix constants. -/
noncomputable section
open scoped ContDiff Convolution

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory ContinuousLinearMap
open JetPolynomial (Base)

lemma kernel_smooth (r : ℕ) : ContDiff ℝ ∞ (kernel r) :=
  (Classical.choose_spec (exists_smoothing_kernel r)).1

lemma kernel_compact (r : ℕ) : HasCompactSupport (kernel r) :=
  (Classical.choose_spec (exists_smoothing_kernel r)).2.1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma smooth_smooth (r : ℕ) {s : ℝ} (hs : 0 < s) {f : Base → E}
    (hf : LocallyIntegrable f volume) : ContDiff ℝ ∞ (smooth r s f) :=
  (compact_dilate (kernel_compact r) hs.ne').contDiff_convolution_left (lsmul ℝ ℝ)
    (smooth_dilate (kernel_smooth r) s) hf

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingResidual
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Iterated smoothing residuals give arbitrary finite approximation order. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma residual_smooth {s : ℝ} (hs : 0 < s) (n : ℕ) {f : Base → E}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (residual s n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact ih.sub (smooth_smooth 0 hs ih.continuous.locallyIntegrable)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FiniteOrderSmoother
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A concrete smoother of any prescribed finite approximation order. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma finiteSmooth_eq (n : ℕ) (s : ℝ) (f : Base → E) :
    finiteSmooth n s f = f - residual s n f := by
  induction n with
  | zero => simp [finiteSmooth, residual]
  | succ n ih =>
    unfold finiteSmooth at ih ⊢
    rw [Finset.sum_range_succ, ih]
    funext x
    simp only [Pi.sub_apply, Pi.add_apply, residual]
    abel

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingLinearMaps
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothing commutes with fixed linear constraints on the fiber. -/
noncomputable section
open scoped ContDiff Convolution

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory ContinuousLinearMap
open JetPolynomial (Base)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma smooth_clm (r : ℕ) {s : ℝ} (hs : 0 < s) (L : E →L[ℝ] F)
    {f : Base → E} (hf : LocallyIntegrable f volume) :
    smooth r s (fun x => L (f x)) = fun x => L (smooth r s f x) := by
  funext x
  have hi := (compact_dilate (kernel_compact r) hs.ne').convolutionExists_left
    (lsmul ℝ ℝ) (smooth_dilate (kernel_smooth r) s).continuous hf x
  change (∫ y, dilate (kernel r) s y • L (f (x - y))) =
    L (∫ y, dilate (kernel r) s y • f (x - y))
  simp_rw [← L.map_smul]
  exact L.integral_comp_comm hi

lemma residual_clm (n : ℕ) {s : ℝ} (hs : 0 < s) (L : E →L[ℝ] F)
    {f : Base → E} (hf : ContDiff ℝ ∞ f) :
    residual s n (fun x => L (f x)) = fun x => L (residual s n f x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [residual, ih]
    rw [smooth_clm 0 hs L (residual_smooth hs n hf).continuous.locallyIntegrable]
    ext x
    simp only [Pi.sub_apply, L.map_sub]

lemma finiteSmooth_clm (n : ℕ) {s : ℝ} (hs : 0 < s) (L : E →L[ℝ] F)
    {f : Base → E} (hf : ContDiff ℝ ∞ f) :
    finiteSmooth n s (fun x => L (f x)) = fun x => L (finiteSmooth n s f x) := by
  simp only [finiteSmooth_eq, residual_clm n hs L hf]
  ext x
  simp only [Pi.sub_apply, L.map_sub]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorSmoothingSymmetry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Tensor coordinate maps commute with transposition. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle
open JetPolynomial (Base)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelSpace
local instance symmetryModelComplete : CompleteSpace TensorFiber := inferInstance

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelSpace
lemma tensorComponent_flip (i : A.centers) (u : ∀ p : M, CovariantTwoTensor p)
    {p : M} (hp : p ∈ (chart (i : M)).source) :
    A.bundleComponent A.tensorTriv i (fun p => tensorTranspose (u p)) p =
      (A.bundleComponent A.tensorTriv i u p).flip := by
  have ht : p ∈ (trivializationAt Plane (TangentSpace planeModel) (i : M)).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet, chart_source] using hp
  have hs : p ∈ (trivializationAt ℝ (fun _ : M => ℝ) (i : M)).baseSet := mem_univ p
  unfold bundleComponent
  rw [(A.tensorTriv i).continuousLinearMapAt_apply_of_mem ℝ (A.tensorTriv_domain i hp),
    (A.tensorTriv i).continuousLinearMapAt_apply_of_mem ℝ (A.tensorTriv_domain i hp)]
  unfold tensorTriv
  simp only [hom_trivializationAt_apply]
  ext v w
  simp only [ContinuousLinearMap.flip_apply]
  rw [inCoordinates_apply_eq₂ ht ht hs, inCoordinates_apply_eq₂ ht ht hs]
  rfl

lemma tensorLocalize_flip (i : A.centers) (u : ∀ p : M, CovariantTwoTensor p) :
    A.bundleLocalize A.tensorTriv i (fun p => tensorTranspose (u p)) =
      fun x => (A.bundleLocalize A.tensorTriv i u x).flip := by
  funext x
  by_cases hx : x ∈ (chart (i : M)).target
  · unfold bundleLocalize localize
    rw [indicator_of_mem hx, indicator_of_mem hx,
      A.tensorComponent_flip i u ((chart (i : M)).map_target hx)]
    ext v w
    rfl
  · simp only [bundleLocalize, localize, indicator_of_notMem hx]
    rfl

lemma tensorRestore_flip (i : A.centers) (h : Base → TensorFiber) :
    A.bundleRestore A.tensorTriv i (fun x => (h x).flip) =
      fun p => tensorTranspose (A.bundleRestore A.tensorTriv i h p) := by
  funext p
  by_cases hp : p ∈ (chart (i : M)).source
  · have hd := A.tensorTriv_domain i hp
    have hinj : Function.Injective ((A.tensorTriv i).continuousLinearMapAt ℝ p) := by
      intro v w heq
      have heq' := congrArg ((A.tensorTriv i).symmL ℝ p) heq
      simpa only [(A.tensorTriv i).symmL_continuousLinearMapAt hd] using heq'
    apply hinj
    have hflip := A.tensorComponent_flip i (A.bundleRestore A.tensorTriv i h) hp
    change (A.tensorTriv i).continuousLinearMapAt ℝ p
        (tensorTranspose (A.bundleRestore A.tensorTriv i h p)) =
      ((A.tensorTriv i).continuousLinearMapAt ℝ p (A.bundleRestore A.tensorTriv i h p)).flip at hflip
    have hcoord (f : Base → TensorFiber) :
        (A.tensorTriv i).continuousLinearMapAt ℝ p (A.bundleRestore A.tensorTriv i f p) =
          A.outer i p • f (chart (i : M) p) := by
      change (A.tensorTriv i).continuousLinearMapAt ℝ p
        (A.outer i p • (A.tensorTriv i).symmL ℝ p (f (chart (i : M) p))) = _
      rw [(A.tensorTriv i).continuousLinearMapAt ℝ p |>.map_smul]
      rw [(A.tensorTriv i).continuousLinearMapAt_symmL hd]
    rw [hflip, hcoord, hcoord]
    ext v w
    rfl
  · have ho : A.outer i p = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hh => hp (A.outer_support i hh))
    simp only [bundleRestore, ho, zero_smul]
    rfl

variable [CompactSpace M]

/-- The actual tensor smoother preserves transposition, so it acts on
symmetric tensors without any extra projection. -/
theorem tensorSmooth_flip (r : ℕ) {s : ℝ} (hs : 0 < s)
    {u : ∀ p : M, CovariantTwoTensor p}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p))) :
    A.tensorSmooth r s (fun p => tensorTranspose (u p)) =
      fun p => tensorTranspose (A.tensorSmooth r s u p) := by
  have hflip (i : A.centers) :
      finiteSmooth r s (fun x => (A.bundleLocalize A.tensorTriv i u x).flip) =
        fun x => (finiteSmooth r s (A.bundleLocalize A.tensorTriv i u) x).flip :=
    finiteSmooth_clm r hs
      (ContinuousLinearMap.flipₗᵢ ℝ Plane Plane ℝ).toContinuousLinearEquiv.toContinuousLinearMap
      (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hu)
  funext p
  simp only [tensorSmooth, bundleSmooth, A.tensorLocalize_flip, hflip]
  calc
    _ = ∑ i : A.centers, tensorTranspose
        (A.bundleRestore A.tensorTriv i (finiteSmooth r s (A.bundleLocalize A.tensorTriv i u)) p) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrFun (A.tensorRestore_flip i _) p
    _ = _ := by
      ext v w
      simp only [tensorTranspose_apply, sum_apply]

theorem tensorSmooth_symmetric_oai (r : ℕ) {s : ℝ} (hs : 0 < s)
    {u : ∀ p : M, CovariantTwoTensor p}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p)))
    (hsymm : ∀ p v w, u p v w = u p w v) :
    ∀ p v w, A.tensorSmooth r s u p v w = A.tensorSmooth r s u p w v := by
  have heq : (fun p => tensorTranspose (u p)) = u := by
    funext p
    ext v w
    exact (hsymm p v w).symm
  have h := A.tensorSmooth_flip r hs hu
  rw [heq] at h
  intro p v w
  exact congrArg (fun b : CovariantTwoTensor p => b v w) (congrFun h p)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorSmooth_symmetric_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorSmooth_symmetric_oai.{u_1}
