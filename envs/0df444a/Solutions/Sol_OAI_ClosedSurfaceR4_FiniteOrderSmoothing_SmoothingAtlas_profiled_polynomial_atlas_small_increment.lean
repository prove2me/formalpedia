-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.profiled_polynomial_atlas_small_increment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:45:18.412204+00:00
-- url     : https://prove2.me/submissions/3915e68e-7a02-464c-9eda-648465af65a0

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_charted_family_atlas_quadratic_residual
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_input_polynomial_small_increment_fixed_phase
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_atlas_mean_majorants_fixed_ball

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_WeightedBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.WeightedEstimates

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]



lemma WeightedBound.const_smul {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ}
    {m : ℕ} {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) (a : ℝ) :
    WeightedBound U s m (|a| * C) (fun x => a • f x) := by
  intro j hj x hx
  change s ^ j * ‖iteratedFDerivWithin ℝ j (a • f) U x‖ ≤ _
  rw [iteratedFDerivWithin_const_smul_apply
    ((hf.of_le (m := (j : ℕ∞ω)) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffWithinAt hx)
    hU hx, norm_smul, Real.norm_eq_abs]
  calc
    _ = |a| * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj x hx) (abs_nonneg _)

lemma WeightedBound.neg {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ} {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) :
    WeightedBound U s m C (fun x => -f x) := by
  simpa using hb.const_smul hU hf (-1)

lemma WeightedBound.sub {U : Set E} (hU : UniqueDiffOn ℝ U) {s C D : ℝ} {m : ℕ} {f g : E → F}
    (hs : 0 ≤ s) (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U)
    (hbf : WeightedBound U s m C f) (hbg : WeightedBound U s m D g) :
    WeightedBound U s m (C + D) (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hbf.add hU hs hf hg.neg (hbg.neg hU hg)




lemma WeightedBound.congr {U : Set E} {s C : ℝ} {m : ℕ} {f g : E → F}
    (hf : WeightedBound U s m C f) (he : EqOn g f U) : WeightedBound U s m C g := by
  intro j hj x hx
  rw [iteratedFDerivWithin_congr he hx]
  exact hf j hj x hx

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_FiniteMean
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.FiniteMean
open ClosedSurfaceR4.WeightedEstimates
open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


lemma sizeBound_ge_one {L : ℕ} {C : ℕ → ℝ} {B : ℕ → ℝ → ℝ}
    (hC : ∀ m, 1 ≤ C m) (hB : ∀ m t, 1 ≤ t → 1 ≤ B m t) (j m : ℕ) :
    1 ≤ sizeBound L C B j m := by
  induction j generalizing m with
  | zero => exact hC m
  | succ j ih =>
    dsimp only [sizeBound]
    have h := hB m _ (ih (m + L))
    linarith [hC m]

lemma differenceBound_nonneg {L : ℕ} {C : ℕ → ℝ} {B K : ℕ → ℝ → ℝ}
    (hC : ∀ m, 1 ≤ C m) (hB : ∀ m t, 1 ≤ t → 1 ≤ B m t)
    (hK : ∀ m t, 1 ≤ t → 1 ≤ K m t) (j m : ℕ) :
    0 ≤ differenceBound L C B K j m := by
  induction j generalizing m with
  | zero => exact le_trans zero_le_one (hB m _ (hC _))
  | succ j ih =>
    apply mul_nonneg _ (ih _)
    exact le_trans zero_le_one (hK m _
      ((sizeBound_ge_one hC hB (j + 1) (m + L)).trans (le_max_left _ _)))

lemma finite_upper (f : ℕ → ℝ) (n : ℕ) : ∃ D : ℝ, 1 ≤ D ∧ ∀ j ≤ n, f j ≤ D := by
  induction n with
  | zero =>
    refine ⟨max 1 (f 0), le_max_left _ _, ?_⟩
    intro j hj
    have : j = 0 := by omega
    subst j
    exact le_max_right _ _
  | succ n ih =>
    obtain ⟨D, hD, hb⟩ := ih
    refine ⟨max D (f (n + 1)), hD.trans (le_max_left _ _), ?_⟩
    intro j hj
    by_cases hjn : j ≤ n
    · exact (hb j hjn).trans (le_max_left _ _)
    · have : j = n + 1 := by omega
      subst j
      exact le_max_right _ _

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma trial_difference (H : E → F) (T : ℝ → (E → F) → E → F) (η : ℝ) (j : ℕ) :
    trial H T η (j + 2) - trial H T η (j + 1) =
      -(T η (trial H T η (j + 1)) - T η (trial H T η j)) := by
  funext p
  simp only [trial, Pi.sub_apply, Pi.neg_apply]
  abel

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
lemma trial_residual (H : E → F) (T : ℝ → (E → F) → E → F) (η : ℝ) (j : ℕ) :
    trial H T η j + T η (trial H T η j) - H =
      -(trial H T η (j + 1) - trial H T η j) := by
  funext p
  simp only [trial, Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
  abel





end ClosedSurfaceR4.FiniteMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldFreeIncrement
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local free oscillations as maps on the surface

The finite-mode construction takes place in coordinates. These lemmas
extend its supported output by zero on the surface, preserving smoothness
and support. This is the first globalization step for the small increments.
-/

noncomputable section

namespace ClosedSurfaceR4

open Set Manifold
open scoped ContDiff Topology
open SmallModes RealModes RootMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

/-- Extension by zero across a closed support lying inside the smooth chart. -/
theorem contMDiff_indicator_of_support {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {O S : Set M} {Z : M → V}
    (hO : IsOpen O) (hS : IsClosed S) (hSO : S ⊆ O)
    (hZ : ContMDiffOn planeModel 𝓘(ℝ, V) ∞ Z O)
    (hz : ∀ x ∈ O, x ∉ S → Z x = 0) :
    ContMDiff planeModel 𝓘(ℝ, V) ∞ (O.indicator Z) ∧
      tsupport (O.indicator Z) ⊆ S := by
  classical
  have hs : tsupport (O.indicator Z) ⊆ S := by
    apply closure_minimal _ hS
    intro x hx
    by_contra hxS
    by_cases hxO : x ∈ O
    · exact hx (by rw [indicator_of_mem hxO, hz x hxO hxS])
    · exact hx (indicator_of_notMem hxO Z)
  refine ⟨contMDiff_of_tsupport (fun x hx => ?_), hs⟩
  have hxO : x ∈ O := hSO (hs hx)
  apply ((hZ x hxO).contMDiffAt (hO.mem_nhds hxO)).congr_of_eventuallyEq
  filter_upwards [hO.mem_nhds hxO] with y hy
  exact indicator_of_mem hy Z

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldSmoothing
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual smoothing maps on a closed surface, assembled from a fixed atlas. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma restore_smooth (p : M) {χ : M → ℝ}
    (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ)
    (hs : tsupport χ ⊆ (chart p).source) {h : Base → V} (hh : ContDiff ℝ ∞ h) :
    ContMDiff planeModel 𝓘(ℝ, V) ∞ (restore p χ h) := by
  apply (contMDiff_indicator_of_support (chart p).open_source
    (isClosed_tsupport χ) hs
    (hχ.contMDiffOn.smul (hh.contMDiff.comp_contMDiffOn (chart_smooth p))) ?_).1
  intro x _ hx
  change χ x • h (chart p x) = 0
  rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorFiberCoordinates
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The three independent coordinates of a symmetric surface tensor, with
an explicit continuous linear reconstruction into the full tensor fiber. -/
noncomputable section
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateFiberNormed
local instance coordinateFiberSpace_r3d1707_1 : NormedSpace ℝ TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDualSmul
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateFiberGroup
lemma fiberFromThree_symmetric (H : Tensor) (v w : Plane) :
    fiberFromThree H v w = fiberFromThree H w v := by
  rw [fiberFromThree_apply, fiberFromThree_apply]
  simp only [evaluate]
  ring

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorMeanCoordinates
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Encode global tensor sections by their finite atlas coordinates. This
retains the compact-surface partition identity while permitting the finite
mean iteration to run on a normed vector-valued function space. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanModelSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.sectionTensorNormed
local instance sectionTensorSpace_r3d1707_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorProject_encode (u : ∀ x : M, CovariantTwoTensor x) :
    A.tensorProject (A.tensorEncode u) = A.tensorEncode u := by
  unfold tensorProject
  rw [A.tensorDecode_encode]

variable [CompactSpace M]

omit [CompactSpace M] in
lemma tensorBound_of_encode {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ContDiff ℝ ∞ (A.tensorEncode u)) {s C : ℝ} {m : ℕ}
    (hs : 0 ≤ s) (hC : 0 ≤ C) (hb : _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m C (A.tensorEncode u)) :
    A.TensorWeightedBound s m C u :=
  fun i => hb.component uniqueDiffOn_univ hs hC hu.contDiffOn i

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorSmoothingSymmetry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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
local instance symmetryModelComplete_r3d1707_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelSpace
local instance symmetryModelComplete_r3d1707_2 : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryDualSmul
variable (A : SmoothingAtlas M)

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

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorPhaseDecomposition
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite phase-basis decomposition on global symmetric tensor sections.
The atlas partition restores the tensor exactly, including chart overlaps. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean PhaseGeometry
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
local instance phaseFiberNormed_r3d1707_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance phaseFiberSpace_r3d1707_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance phaseDualAdd_r3d1707_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance phaseDualSmul_r3d1707_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance phaseSectionNormed_r3d1707_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance phaseSectionSpace_r3d1707_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorDecode_symmetric {f : Base → A.centers → TensorFiber}
    (hf : ∀ x i v w, f x i v w = f x i w v) :
    ∀ p v w, A.tensorDecode f p v w = A.tensorDecode f p w v := by
  have ht (i : A.centers) : (fun x => (f x i).flip) = (fun x => f x i) := by
    funext x
    ext v w
    exact hf x i w v
  intro p v w
  simp only [tensorDecode, sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hh := A.tensorRestore_flip i (fun x => f x i)
  rw [ht] at hh
  exact congrArg (fun b : CovariantTwoTensor p => b v w) (congrFun hh p)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorPlaneCoordinates
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reading and restoring global tensors in the two real coordinates used
by the charted oscillatory solver. The bounds preserve derivative order. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates RealModes
open JetPolynomial (Base planeCoordinateIsometry weightedBound_comp_isometry)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadSectionNormed
local instance planeReadSectionSpace_r3d1707_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorPlaneRestore_symmetric (f : A.centers → SmallModes.Base → Tensor) :
    ∀ p v w, A.tensorPlaneRestore f p v w = A.tensorPlaneRestore f p w v := by
  apply A.tensorDecode_symmetric
  intro x i v w
  exact fiberFromThree_symmetric _ _ _

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UniformFiniteMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A uniform version of finite mean substitution: the admissible size is
chosen from the majorants before the actual mean operator is chosen. -/
noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteMean
open ClosedSurfaceR4.WeightedEstimates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem finite_substitution_uniform_inputs {r0 r1 : ℝ} (hgap : r0 < r1) {L : ℕ}
    {B K : ℕ → ℝ → ℝ}
    {C : ℕ → ℝ} (hC : ∀ m, 1 ≤ C m) (n : ℕ) :
    ∃ η0 : ℝ, 0 < η0 ∧ η0 ≤ 1 ∧
      ∀ (U : Set E), UniqueDiffOn ℝ U → ∀ s : ℝ, 0 ≤ s → ∀ reference H : E → F,
      ContDiffOn ℝ ∞ H U → (∀ p ∈ U, ‖H p - reference p‖ ≤ r0) →
      (∀ m, WeightedBound U s m (C m) H) →
      ∀ (T : ℝ → (E → F) → E → F), MeanBounds U s reference r1 L T B K →
      ∀ η, 0 < η → η ≤ η0 →
      ∀ j ≤ n, ContDiffOn ℝ ∞ (trial H T η j) U ∧
        InTrialBall U reference r1 (trial H T η j) ∧
        (∀ m, WeightedBound U s m (sizeBound L C B j m) (trial H T η j)) ∧
        (∀ m, WeightedBound U s m (differenceBound L C B K j m * η ^ (j + 1))
          (trial H T η j + T η (trial H T η j) - H)) := by
  obtain ⟨D, hD, hbD⟩ := finite_upper (fun j => B 0 (sizeBound L C B j L)) n
  let η0 := min 1 ((r1 - r0) / (2 * D))
  have hη0 : 0 < η0 := lt_min (by norm_num) (div_pos (sub_pos.mpr hgap) (by linarith))
  refine ⟨η0, hη0, min_le_left _ _, ?_⟩
  intro U hU s hs reference H hH hH0 hbH T hT η hη hsmall
  have hη1 : η ≤ 1 := hsmall.trans (min_le_left _ _)
  have hηD : r0 + η * D < r1 := by
    have hh : η ≤ (r1 - r0) / (2 * D) := hsmall.trans (min_le_right _ _)
    have hh' := (le_div_iff₀ (by linarith : 0 < 2 * D)).mp hh
    nlinarith
  have hstates : ∀ j ≤ n + 1,
      ContDiffOn ℝ ∞ (trial H T η j) U ∧ InTrialBall U reference r1 (trial H T η j) ∧
      ∀ m, WeightedBound U s m (sizeBound L C B j m) (trial H T η j) := by
    intro j
    induction j with
    | zero =>
      intro hj
      exact ⟨hH, fun p hp => (hH0 p hp).trans_lt hgap, hbH⟩
    | succ j ih =>
      intro hj
      obtain ⟨hjS, hjBall, hjB⟩ := ih (by omega)
      have hTS := hT.smooth η hη hη1 _ hjS hjBall
      have hVal (m : ℕ) := hT.value η hη hη1 m (sizeBound L C B j (m + L))
        (trial H T η j) (sizeBound_ge_one hC hT.B_pos _ _) hjS hjBall (hjB (m + L))
      refine ⟨hH.sub hTS, ?_, ?_⟩
      · intro p hp
        calc
          ‖trial H T η (j + 1) p - reference p‖ =
              ‖(H p - reference p) - T η (trial H T η j) p‖ := by
            congr 1
            dsimp [trial]
            abel
          _ ≤ ‖H p - reference p‖ + ‖T η (trial H T η j) p‖ := norm_sub_le _ _
          _ ≤ r0 + η * D := by
            apply add_le_add (hH0 p hp)
            exact ((hVal 0).norm_le hp).trans (mul_le_mul_of_nonneg_left (by simpa using hbD j (by omega)) hη.le)
          _ < r1 := hηD
      · intro m
        have hh := (hbH m).sub hU hs hH hTS (hVal m)
        apply hh.mono_const
        dsimp only [sizeBound]
        have hp : 0 ≤ B m (sizeBound L C B j (m + L)) :=
          le_trans zero_le_one (hT.B_pos m _ (sizeBound_ge_one hC hT.B_pos j (m + L)))
        nlinarith
  have hdiff : ∀ j ≤ n, ∀ m,
      WeightedBound U s m (differenceBound L C B K j m * η ^ (j + 1))
        (trial H T η (j + 1) - trial H T η j) := by
    intro j
    induction j with
    | zero =>
      intro hj m
      have hBall : InTrialBall U reference r1 H := fun p hp => (hH0 p hp).trans_lt hgap
      have hTS := hT.smooth η hη hη1 H hH hBall
      have hh := (hT.value η hη hη1 m (C (m + L)) H (hC _) hH hBall (hbH _)).neg hU hTS
      have he : trial H T η (0 + 1) - trial H T η 0 = -(T η H) := by
        funext p; simp only [trial, Pi.sub_apply, Pi.neg_apply]; abel
      rw [he]
      have hh' : WeightedBound U s m (η * B m (C (m + L))) (-(T η H)) :=
        hh.congr (by intro p hp; rfl)
      convert hh' using 1
      all_goals try with_reducible_and_instances rfl
      try rfl
      dsimp only [differenceBound]
      simp only [Nat.zero_add, pow_one]
      ring
    | succ j ih =>
      intro hj m
      obtain ⟨hf, hfBall, hbf⟩ := hstates (j + 1) (by omega)
      obtain ⟨hg, hgBall, hbg⟩ := hstates j (by omega)
      let C' := max (sizeBound L C B (j + 1) (m + L)) (sizeBound L C B j (m + L))
      have hC' : 1 ≤ C' := (sizeBound_ge_one hC hT.B_pos _ _).trans (le_max_left _ _)
      have hD' : 0 ≤ differenceBound L C B K j (m + L) * η ^ (j + 1) :=
        mul_nonneg (differenceBound_nonneg hC hT.B_pos hT.K_pos _ _) (pow_nonneg hη.le _)
      have hh := hT.difference η hη hη1 m C' _ _ _ hC' hD' hf hg hfBall hgBall
        ((hbf (m + L)).mono_const (le_max_left _ _))
        ((hbg (m + L)).mono_const (le_max_right _ _)) (ih (by omega) (m + L))
      have hTF := hT.smooth η hη hη1 _ hf hfBall
      have hTG := hT.smooth η hη hη1 _ hg hgBall
      have hn := hh.neg hU (hTF.sub hTG)
      rw [show j + 1 + 1 = j + 2 by omega, trial_difference]
      convert hn using 1
      all_goals try with_reducible_and_instances rfl
      try rfl
      dsimp only [differenceBound, C']
      rw [pow_succ]
      ring
  intro j hj
  obtain ⟨hjS, hjBall, hjB⟩ := hstates j (by omega)
  refine ⟨hjS, hjBall, hjB, ?_⟩
  intro m
  rw [trial_residual]
  have hnext := (hstates (j + 1) (by omega)).1
  exact (hdiff j hj m).neg hU (hnext.sub hjS)

end ClosedSurfaceR4.FiniteMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FixedMeanSubstitution
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite mean correction for one fixed operator with derivative loss.
The smallness threshold is uniform in the operator; no infinite-dimensional
inverse or convergence of a derivative-losing iteration is asserted. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteMean
open WeightedEstimates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma rescaledMean_self {η : ℝ} (hη : η ≠ 0) (A : (E → F) → E → F) :
    rescaledMean η A η = A := by
  funext f
  simp only [rescaledMean, div_self hη, one_smul]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma trial_rescaledMean {η : ℝ} (hη : η ≠ 0)
    (H : E → F) (A : (E → F) → E → F) (j : ℕ) :
    trial H (rescaledMean η A) η j = fixedTrial H A j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change H - rescaledMean η A η (trial H (rescaledMean η A) η j) =
      H - A (fixedTrial H A j)
    rw [rescaledMean_self hη, ih]

end ClosedSurfaceR4.FiniteMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasGlobalFreeModes
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite free correction is an actual sum of globally smooth phase modes. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

variable {n : A.centers → ℕ}
  {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
  {ε τ : ℝ} {s : ℝ≥0} {r : A.centers → ℝ} {ρ R : ℝ}
  {reference : A.centers → SmallModes.Base → Tensor}

omit [CompactSpace M] in
lemma freeGlobalPhase_smooth
    (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (r i) ρ R (reference i))
    (i : A.centers) (j : Fin 3) : ContMDiff planeModel 𝓘(ℝ) ∞ (A.freeGlobalPhase d i j) :=
  restore_smooth (i : M) (A.outer_smooth i) (A.outer_support i) ((d i).solver j).smoothPhase

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorMeanIteration
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite mean substitution on actual global tensor sections, represented
by redundant atlas coordinates. Every iterate stays in the representation
range, so no leading-identity premise on arbitrary plane fields is needed. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates FiniteMean
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.iterationDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.iterationModelNormed
local instance iterationModelSpace_r3d1707_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance iterationDualSmul_r3d1707_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance iterationSectionTensorNormed_r3d1707_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance iterationSectionTensorSpace_r3d1707_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorMeanOperator_project
    (T : (∀ x : M, CovariantTwoTensor x) → ∀ x : M, CovariantTwoTensor x)
    (f : Base → A.centers → TensorFiber) :
    A.tensorProjectLM (A.tensorMeanOperator T f) = A.tensorMeanOperator T f :=
  A.tensorProject_encode _

lemma tensorMean_trial_project (H : ∀ x : M, CovariantTwoTensor x)
    (T : (∀ x : M, CovariantTwoTensor x) → ∀ x : M, CovariantTwoTensor x) (j : ℕ) :
    A.tensorProjectLM (fixedTrial (A.tensorEncode H) (A.tensorMeanOperator T) j) =
      fixedTrial (A.tensorEncode H) (A.tensorMeanOperator T) j := by
  induction j with
  | zero => exact A.tensorProject_encode H
  | succ j _ =>
    change A.tensorProjectLM (A.tensorEncode H - A.tensorMeanOperator T
      (fixedTrial (A.tensorEncode H) (A.tensorMeanOperator T) j)) = _
    rw [(A.tensorProjectLM).map_sub,show A.tensorProjectLM (A.tensorEncode H) = A.tensorEncode H from
      A.tensorProject_encode H,A.tensorMeanOperator_project]
    rfl

lemma tensorEncode_meanTrial (H : ∀ x : M, CovariantTwoTensor x)
    (T : (∀ x : M, CovariantTwoTensor x) → ∀ x : M, CovariantTwoTensor x) (j : ℕ) :
    A.tensorEncode (A.tensorMeanTrial H T j) =
      fixedTrial (A.tensorEncode H) (A.tensorMeanOperator T) j :=
  A.tensorMean_trial_project H T j

lemma tensorMeanTrial_zero (H : ∀ x : M, CovariantTwoTensor x)
    (T : (∀ x : M, CovariantTwoTensor x) → ∀ x : M, CovariantTwoTensor x) :
    A.tensorMeanTrial H T 0 = H := A.tensorDecode_encode H

lemma tensorMeanTrial_succ (H : ∀ x : M, CovariantTwoTensor x)
    (T : (∀ x : M, CovariantTwoTensor x) → ∀ x : M, CovariantTwoTensor x) (j : ℕ) :
    A.tensorMeanTrial H T (j + 1) = H - T (A.tensorMeanTrial H T j) := by
  change A.tensorDecode (A.tensorEncode H - A.tensorMeanOperator T
    (fixedTrial (A.tensorEncode H) (A.tensorMeanOperator T) j)) = _
  rw [A.tensorDecode_sub, A.tensorDecode_encode]
  change H - A.tensorDecode (A.tensorEncode (T (A.tensorMeanTrial H T j))) = _
  rw [A.tensorDecode_encode]

lemma tensorEncode_meanResidual (H : ∀ x : M, CovariantTwoTensor x)
    (T : (∀ x : M, CovariantTwoTensor x) → ∀ x : M, CovariantTwoTensor x) (j : ℕ) :
    A.tensorEncode (A.tensorMeanTrial H T j + T (A.tensorMeanTrial H T j) - H) =
      fixedTrial (A.tensorEncode H) (A.tensorMeanOperator T) j +
        A.tensorMeanOperator T (fixedTrial (A.tensorEncode H) (A.tensorMeanOperator T) j) -
        A.tensorEncode H := by
  rw [A.tensorEncode_sub, A.tensorEncode_add, A.tensorEncode_meanTrial]
  rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorAtlasMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global nonlinear mean is the finite restoration of the actual
local means evaluated on unweighted chart readings. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasMeanFiberSpace
local instance atlasMeanDualAdd_r3d1707_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasMeanDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasMeanFiberNormed
local instance atlasMeanSectionNormed_r3d1707_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasMeanSectionSpace_r3d1707_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma atlasMean_symmetric
    (μ : A.centers → (SmallModes.Base → Tensor) → SmallModes.Base → Tensor)
    (u : ∀ x : M, CovariantTwoTensor x) : ∀ p v w, A.atlasMean μ u p v w = A.atlasMean μ u p w v :=
  A.tensorPlaneRestore_symmetric _

lemma one_le_tensorReadBallConstant : 1 ≤ A.tensorReadBallConstant :=
  (Classical.choose_spec A.tensorPlaneRead_decode_ball).1

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorFiniteMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite derivative-losing mean substitution on global surface tensors.
The actual section iterates are recovered exactly from their atlas encoding. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates FiniteMean
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteMeanDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteMeanDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteMeanModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteMeanModelSpace
local instance finiteMeanSectionTensorNormed_r3d1707_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance finiteMeanSectionTensorSpace_r3d1707_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem tensor_finite_mean_substitution_uniform {r₀ r : ℝ} (hgap : r₀ < r)
    {L : ℕ} {B K : ℕ → ℝ → ℝ} {C : ℕ → ℝ} (hC : ∀ m, 1 ≤ C m)
    (steps : ℕ) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧ ∀ s : ℝ, 0 < s →
      ∀ reference H : ∀ x : M, CovariantTwoTensor x,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (H x)) →
      (∀ x, ‖A.tensorEncode H x - A.tensorEncode reference x‖ ≤ r₀) →
      (∀ m, A.TensorWeightedBound s m (C m) H) →
      ∀ η : ℝ, 0 < η → η ≤ η₀ →
      ∀ T : (∀ x : M, CovariantTwoTensor x) → ∀ x : M, CovariantTwoTensor x,
      MeanBounds univ s (A.tensorEncode reference) r L
        (rescaledMean η (A.tensorMeanOperator T)) B K →
      ∀ j ≤ steps,
        ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
          (fun x => TotalSpace.mk' TensorFiber x (A.tensorMeanTrial H T j x)) ∧
        InTrialBall univ (A.tensorEncode reference) r (A.tensorEncode (A.tensorMeanTrial H T j)) ∧
        (∀ m, A.TensorWeightedBound s m (sizeBound L C B j m) (A.tensorMeanTrial H T j)) ∧
        (∀ m, A.TensorWeightedBound s m (differenceBound L C B K j m * η ^ (j + 1))
          (A.tensorMeanTrial H T j + T (A.tensorMeanTrial H T j) - H)) := by
  obtain ⟨η₀,hη₀,hη₁,ht⟩ := finite_substitution_uniform_inputs
    (E := Base) (F := A.centers → TensorFiber) (B := B) (K := K) hgap hC steps
  refine ⟨η₀,hη₀,hη₁,?_⟩
  intro s hs reference H hH hH0 hbH η hη hsmall T hm j hj
  have henc := A.tensorEncode_smooth hH
  obtain ⟨ha,hb,hc,hd⟩ := ht univ uniqueDiffOn_univ s hs.le
    (A.tensorEncode reference) (A.tensorEncode H) henc.contDiffOn (fun x _ => hH0 x)
    (fun m => A.tensorEncode_bound hH hs (zero_le_one.trans (hC m)) (hbH m))
    _ hm η hη hsmall j hj
  rw [trial_rescaledMean hη.ne'] at ha hb hc hd
  rw [rescaledMean_self hη.ne'] at hd
  have htrial : ContDiff ℝ ∞ (fixedTrial (A.tensorEncode H) (A.tensorMeanOperator T) j) :=
    contDiffOn_univ.mp ha
  have hmean : ContDiff ℝ ∞ (A.tensorMeanOperator T
      (fixedTrial (A.tensorEncode H) (A.tensorMeanOperator T) j)) := by
    have hh := hm.smooth η hη (hsmall.trans hη₁) _ ha hb
    rw [rescaledMean_self hη.ne'] at hh
    exact contDiffOn_univ.mp hh
  have hres : ContDiff ℝ ∞ (A.tensorEncode
      (A.tensorMeanTrial H T j + T (A.tensorMeanTrial H T j) - H)) := by
    rw [A.tensorEncode_meanResidual]
    exact (htrial.add hmean).sub henc
  refine ⟨A.tensorDecode_smooth htrial,?_,?_,?_⟩
  · rw [A.tensorEncode_meanTrial]
    exact hb
  · intro m
    apply A.tensorBound_of_encode (by rw [A.tensorEncode_meanTrial]; exact htrial) hs.le
      (zero_le_one.trans (sizeBound_ge_one hC hm.B_pos j m))
    rw [A.tensorEncode_meanTrial]
    exact hc m
  · intro m
    apply A.tensorBound_of_encode hres hs.le
      (mul_nonneg (differenceBound_nonneg hC hm.B_pos hm.K_pos j m) (pow_nonneg hη.le _))
    rw [A.tensorEncode_meanResidual]
    exact hd m

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_TensorSymmetricMean
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symmetry is invariant under the actual global finite mean iteration. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
local instance symmetricMeanFiberNormed_r3d1707_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance symmetricMeanFiberSpace_r3d1707_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance symmetricMeanDualAdd_r3d1707_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance symmetricMeanDualSmul_r3d1707_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance symmetricMeanSectionNormed_r3d1707_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance symmetricMeanSectionSpace_r3d1707_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorMeanTrial_symmetric (H : ∀ x : M, CovariantTwoTensor x)
    (T : (∀ x : M, CovariantTwoTensor x) → ∀ x : M, CovariantTwoTensor x)
    (hH : ∀ p v w, H p v w = H p w v)
    (hT : ∀ u, (∀ p v w, u p v w = u p w v) → ∀ p v w, T u p v w = T u p w v)
    (j : ℕ) : ∀ p v w, A.tensorMeanTrial H T j p v w = A.tensorMeanTrial H T j p w v := by
  induction j with
  | zero => simpa only [A.tensorMeanTrial_zero] using hH
  | succ j ih =>
    rw [A.tensorMeanTrial_succ]
    intro p v w
    change H p v w - T (A.tensorMeanTrial H T j) p v w =
      H p w v - T (A.tensorMeanTrial H T j) p w v
    rw [hH p v w, hT _ ih p v w]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_UniformAtlasMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform global majorants for the actual charted polynomial means.
Constants precede both scales, all coordinate maps and all local solvers. -/
noncomputable section
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates FiniteMean
open JetPolynomial (Base)
open JetPolynomial.Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.uniformAtlasFiberSpace
local instance uniformAtlasDualAdd_r3d1707_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.uniformAtlasDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.uniformAtlasFiberNormed
local instance uniformAtlasSectionNormed_r3d1707_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance uniformAtlasSectionSpace_r3d1707_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem uniform_atlas_mean_majorants_all_radii
    {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
    (p : ∀ i, Fin 3 → ChartedMeanProfile (P i)) {ρ R : ℝ} (hρ : 0 < ρ)
    (reference : ∀ x : M, CovariantTwoTensor x)
    (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (reference x))) (q : ℕ) :
    let L := Finset.univ.sup (fun i : A.centers => tensorOrder (P i)+1+(q+1)*(tensorOrder (P i)+1))
    let loss := Finset.univ.sup (fun i : A.centers => tensorLoss (P i))
    ∃ D₀ : ℝ, 1 ≤ D₀ ∧ ∀ r : ℝ, 0 ≤ r →
      (∀ f : Base → A.centers → TensorFiber, ContDiff ℝ ∞ f →
        InTrialBall univ (A.tensorEncode reference) r f → ∀ i : A.centers,
        InTrialBall univ (A.tensorPlaneRead i reference) (D₀*r)
          (A.tensorPlaneRead i (A.tensorDecode f))) ∧ ∃ β κ : ℕ → ℝ → ℝ,
      ∀ {ε τ : ℝ} {s : ℝ≥0}
        (d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (D₀*r) ρ R (A.tensorPlaneRead i reference)),
      (∀ i, (d i).Fits (p i)) → 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 → τ / s + ε / τ ^ loss ≤ 1 → ∀ δ : ℝ, 0 < δ →
      MeanBounds univ s (A.tensorEncode reference) r L
        (rescaledMean (τ / s + ε / τ ^ loss)
          (A.tensorMeanOperator (A.atlasMean (fun i => (d i).mean hρ δ q)))) β κ := by
  exact ⟨A.tensorReadBallConstant,A.one_le_tensorReadBallConstant,
    A.uniform_atlas_mean_majorants_fixed_ball (R := R) p hρ reference href q⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ProfiledAtlasAdjustedMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.tensorOrder_emptyMetricPolynomial _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform finite mean adjustment from profiles, including varying base maps. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean PhaseGeometry WeightedEstimates FiniteMean
open JetPolynomial (Base)
open JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.profiledMeanFiberSpace
local instance profiledMeanDualAdd_r3d1707_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.profiledMeanDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.profiledMeanFiberNormed
local instance profiledMeanSectionNormed_r3d1707_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance profiledMeanSectionSpace_r3d1707_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem profiled_atlas_adjusted_mean
    {n : A.centers → ℕ} {P : (i : A.centers) → Fin 3 → Fin (n i) → JetPolynomial.Expression}
    (p : ∀ i, Fin 3 → ChartedMeanProfile (P i))
    {r₁ ρ R : ℝ} (hr₁ : 0 < r₁) (hρ : 0 < ρ)
    (reference : ∀ x : M, CovariantTwoTensor x)
    (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (reference x)))
    (Q : A.centers → PhaseBasis) (w : A.centers → Fin 3 → ℝ)
    (hw : ∀ i j, w i j ≠ 0) (q : ℕ) :
    let L := Finset.univ.sup (fun i : A.centers => tensorOrder (P i)+1+(q+1)*(tensorOrder (P i)+1))
    let loss := Finset.univ.sup (fun i : A.centers => tensorLoss (P i))
    ∃ r D₀ : ℝ, 0 < r ∧ 1 ≤ D₀ ∧ D₀*r ≤ r₁ ∧
      ∃ β κ : ℕ → ℝ → ℝ,
      ∀ C : ℕ → ℝ, (∀ m, 1 ≤ C m) → ∀ steps : ℕ,
      ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧
      ∀ (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
      ∀ (H : ∀ x : M, CovariantTwoTensor x),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (H x)) →
      (∀ x v v', H x v v' = H x v' v) →
      (∀ x, ‖A.tensorEncode H x - A.tensorEncode reference x‖ ≤ r/2) →
      (∀ m, A.TensorWeightedBound s m (C m) H) →
      ∀ (ε τ : ℝ), 0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 → τ/s + ε/τ^loss ≤ η₀ →
      ∀ d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (D₀*r) ρ R (A.tensorPlaneRead i reference),
        (∀ i, (d i).Fits (p i)) →
        (∀ i j, coordinatePhase ((d i).phase j) = phaseLinear (w i j • (Q i).ξ j)) →
        (∀ i j x, x ∈ ((d i).solver j).e.source →
          ((d i).data j).cutoff (((d i).solver j).e x) = A.planeWeight i x / w i j) →
        (∀ i j x, x ∈ ((d i).solver j).e.source →
          ((d i).data j).form (((d i).solver j).e x) = (Q i).Q j) →
        (∀ i j, tsupport (A.planeWeight i) ⊆ ((d i).solver j).e.source) →
      ∀ δ : ℝ, 0 < δ → ∀ j ≤ steps, ∃ u : ∀ x : M, CovariantTwoTensor x,
        ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
          (fun x => TotalSpace.mk' TensorFiber x (u x)) ∧
        (∀ x v v', u x v v' = u x v' v) ∧
        InTrialBall univ (A.tensorEncode reference) r (A.tensorEncode u) ∧
        (∀ i, InTrialBall univ (A.tensorPlaneRead i reference) (D₀*r) (A.tensorPlaneRead i u)) ∧
        (∀ m, A.TensorWeightedBound s m (sizeBound L C β j m) u) ∧
        (∀ m, A.TensorWeightedBound s m
          (δ^2 * (differenceBound L C β κ j m * (τ/s + ε/τ^loss)^(j+1)))
          (A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) - δ^2 • H)) := by
  obtain ⟨D₀,hD₀,hall⟩ := A.uniform_atlas_mean_majorants_all_radii (R := R) p hρ reference href q
  have hDpos : 0 < D₀ := zero_lt_one.trans_le hD₀
  let r := r₁/(2*D₀)
  have hr : 0 < r := div_pos hr₁ (mul_pos (by norm_num) hDpos)
  have hDr : D₀*r = r₁/2 := by dsimp [r]; field_simp
  obtain ⟨hball,β,κ,hm⟩ := hall r hr.le
  refine ⟨r,D₀,hr,hD₀,?_,β,κ,?_⟩
  · rw [hDr]
    linarith
  · intro C hC steps
    obtain ⟨η₀,hη₀,hη₁,htall⟩ := A.tensor_finite_mean_substitution_uniform
      (by linarith : r/2 < r) hC steps (B := β) (K := κ)
    refine ⟨η₀,hη₀,hη₁,?_⟩
    intro s hs hs1 H hH hsym hH0 hHC ε τ hτ hτs hε hε1 hsmall d hfit hphase hcut hform hsup δ hδ j hj
    have hη : 0 < τ/s + ε/τ^(Finset.univ.sup (fun i : A.centers => tensorLoss (P i))) :=
      add_pos_of_pos_of_nonneg (div_pos hτ hs) (div_nonneg hε (pow_nonneg hτ.le _))
    obtain ⟨hu,hb,hsize,herror⟩ := htall s hs reference H hH hH0 hHC _ hη hsmall _
      (hm d hfit hτ hs hτs hs1 hε hε1 (hsmall.trans hη₁) δ hδ) j hj
    have hsymu := A.tensorMeanTrial_symmetric H (A.atlasMean (fun i => (d i).mean hρ δ q)) hsym
      (fun u _ => A.atlasMean_symmetric _ u) j
    have hlocal (i : A.centers) := hball _ (A.tensorEncode_smooth hu) hb i
    simp only [A.tensorDecode_encode] at hlocal
    refine ⟨_,hu,hsymu,hb,hlocal,hsize,?_⟩
    intro m
    exact A.charted_family_atlas_quadratic_residual d hρ Q w hw hphase hcut hform hsup
      _ H hu hH hsymu hlocal hδ.ne' hτ.ne' q (herror m)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ProfiledPolynomialSmallIncrement
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite mean adjustment gives a small increment uniformly over nearby input maps. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry WeightedEstimates FiniteMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.profiledPolynomialSmallFiberSpace
local instance profiledPolynomialSmallDualAdd_r3d1707_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.profiledPolynomialSmallDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.profiledPolynomialSmallFiberNormed
local instance profiledPolynomialSmallSectionNormed_r3d1707_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance profiledPolynomialSmallSectionSpace_r3d1707_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem profiled_polynomial_atlas_small_increment_oai
    {n : A.centers → ℕ} {nq : ℕ}
    (Pol : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
    (hPol : ∀ i k l, (Pol i k l).SmoothCoeffs univ)
    (P : A.centers → Fin 3 → Fin nq → Expression)
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
    (hquad : A.PolynomialQuadraticRepresentation Pol P)
    (hlin : A.PolynomialLinearRepresentation Pol P)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
    {r₁ ρ R : ℝ} (hr₁ : 0 < r₁) (hρ : 0 < ρ)
    (reference : ∀ x : M, CovariantTwoTensor x)
    (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (reference x)))
    (p : ∀ i, Fin 3 → ChartedMeanProfile (P i))
    (d₀ : ∀ i, ChartedMeanFamilyData (P i) 0 1 1 r₁ ρ R (A.tensorPlaneRead i reference))
    (Q : A.centers → PhaseBasis) (w : A.centers → Fin 3 → ℝ)
    (hw : ∀ i j, w i j ≠ 0)
    (hphase₀ : ∀ i j, coordinatePhase ((d₀ i).phase j) = phaseLinear (w i j • (Q i).ξ j))
    (hImm : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) x))
    (hgood : ∀ k l x, x ∈ (modeSupport
      (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
        (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
      PhaseGeometry.Good (RealModes.realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) x)
        (phaseDerivative (coordinatePhase (A.globalQuadraticPhase
          (fun a : A.centers × Fin 3 => A.freeGlobalPhase d₀ a.1 a.2) k l)) x))
    (Ω : A.centers → Set JetPolynomial.Base) (hΩ : ∀ i, IsOpen (Ω i))
    (KΩ : A.centers → TopologicalSpace.Compacts JetPolynomial.Base) (hΩK : ∀ i, Ω i ⊆ KΩ i)
    (hweight : ∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ Ω i)
    (houter : ∀ i : A.centers, (chart (i : M)) '' tsupport (A.outer i) ⊆ Ω i)
    (D : ℕ → ℝ) (hD : ∀ m, 0 ≤ D m)
    (q : ℕ) :
    ∃ r D₀ : ℝ, 0 < r ∧ 1 ≤ D₀ ∧ D₀*r ≤ r₁ ∧
      ∀ C : ℕ → ℝ, (∀ m, 1 ≤ C m) →
      ∃ (ρ₀ η₀ : ℝ) (B T : ℕ → ℝ), 0 < ρ₀ ∧ 0 < η₀ ∧ η₀ ≤ 1 ∧
        (∀ m, 0 ≤ B m) ∧ (∀ m, 0 ≤ T m) ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G → ∀ b : ℝ,
        0 ≤ b → b < ρ₀ → A.WeightedBound 1 2 b (G-F) →
      ∀ (s : ℝ≥0), 0 < (s : ℝ) → s ≤ 1 →
        (∀ m, A.ShiftedBound 2 m s (D m) G) →
      ∀ (H : ∀ x : M, CovariantTwoTensor x),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (H x)) →
      (∀ x v v', H x v v' = H x v' v) →
      (∀ x, ‖A.tensorEncode H x - A.tensorEncode reference x‖ ≤ r/2) →
      (∀ m, A.TensorWeightedBound s m (C m) H) →
      ∀ τ δ ε : ℝ, 0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 →
      τ/s+ε/τ^(max (Finset.univ.sup (fun i : A.centers => tensorLoss (P i)))
        (Finset.univ.sup (fun i : A.centers => tensorLoss (Pol i)))) ≤ η₀ → 0 < δ → δ ≤ τ →
      ∀ d : ∀ i, ChartedMeanFamilyData (P i) ε τ s (D₀*r) ρ R (A.tensorPlaneRead i reference),
        (∀ i, (d i).Fits (p i)) →
        (∀ i, (d i).phase = (d₀ i).phase) →
        (∀ i, (d i).G = A.jetChartMap i G) →
        (∀ i j x, x ∈ ((d i).solver j).e.source →
          ((d i).data j).cutoff (((d i).solver j).e x) = A.planeWeight i x / w i j) →
        (∀ i j x, x ∈ ((d i).solver j).e.source →
          ((d i).data j).form (((d i).solver j).e x) = (Q i).Q j) →
        (∀ i j, tsupport (A.planeWeight i) ⊆ ((d i).solver j).e.source) →
        (∀ i j, (modeSupport ((d i).support j) : Set SmallModes.Base) ⊆
          (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
      ∃ X : M → Space, ContMDiff planeModel spaceModel ∞ X ∧
        (∀ m, A.WeightedBound τ m (B m*(δ*τ)) X) ∧
        (∀ m, A.TensorWeightedBound τ m (T m*(δ*(τ/s+ε/τ^(max (Finset.univ.sup (fun i : A.centers => tensorLoss (P i)))
            (Finset.univ.sup (fun i : A.centers => tensorLoss (Pol i)))))^(q+1)+δ^3/τ))
          (A.atlasPolynomialMetric Pol ε (G+X)-A.atlasPolynomialMetric Pol ε G-δ^2 • H)) := by
  obtain ⟨r,D₀,hr,hD₀,hDr,β,κ,hmean⟩ := A.profiled_atlas_adjusted_mean
    p hr₁ hρ reference href Q w hw q
  refine ⟨r,D₀,hr,hD₀,hDr,?_⟩
  intro C hC
  let L := Finset.univ.sup (fun i : A.centers => tensorOrder (P i)+1+(q+1)*(tensorOrder (P i)+1))
  let Cu := fun m => max 1 (sizeBound L C β q m)
  let E := fun m => max 1 (differenceBound L C β κ q m)
  have hCu (m) : 0 ≤ Cu m := zero_le_one.trans (le_max_left _ _)
  have hE (m) : 0 ≤ E m := zero_le_one.trans (le_max_left _ _)
  obtain ⟨ρ₀,hρ₀,hall⟩ := A.input_polynomial_small_increment_fixed_phase Pol hPol P hP hquad hlin F hF
    (fun a : A.centers × Fin 3 => A.freeGlobalPhase d₀ a.1 a.2)
    (fun a => A.freeGlobalPhase_smooth d₀ a.1 a.2) hImm hgood Ω hΩ KΩ hΩK hweight houter
  obtain ⟨B,T,hB,hT,hsmall⟩ := hall p hρ (fun _ => D₀*r)
    (fun i => A.tensorPlaneRead i reference) D hD Cu E hCu hE q
  obtain ⟨η₀,hη₀,hη₁,hmeanUniform⟩ := hmean C hC q
  refine ⟨ρ₀,η₀,B,T,hρ₀,hη₀,hη₁,hB,hT,?_⟩
  intro G hG b hb hbρ hclose s hs hs1 hd H hH hsym hnear hbC τ δ ε hτ hτs hε hε1 hη hδ hδτ d hfit hphase hmap hcut hform hsup hK
  have hbuild := hmeanUniform s hs hs1 H hH hsym hnear hbC
  have hphase' (i j) : coordinatePhase ((d i).phase j) = phaseLinear (w i j • (Q i).ξ j) := by
    rw [hphase i]
    exact hphase₀ i j
  let lossP := Finset.univ.sup (fun i : A.centers => tensorLoss (P i))
  let loss := max lossP (Finset.univ.sup (fun i : A.centers => tensorLoss (Pol i)))
  let η := τ/s+ε/τ^loss
  have hηP : τ/s+ε/τ^lossP ≤ η := by
    apply add_le_add le_rfl
    apply div_le_div_of_nonneg_left hε (pow_pos hτ _)
    exact pow_le_pow_of_le_one hτ.le (hτs.trans hs1) (le_max_left _ _)
  have hη0 : 0 ≤ η := add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  have hηP0 : 0 ≤ τ/s+ε/τ^lossP := add_nonneg (div_nonneg hτ.le hs.le) (div_nonneg hε (pow_nonneg hτ.le _))
  obtain ⟨u,hu,_,_,hball,hsize,herror⟩ := hbuild ε τ hτ hτs hε hε1 (hηP.trans hη)
    d hfit hphase' hcut hform hsup δ hδ q le_rfl
  have hbu (m) : A.TensorWeightedBound s m (Cu m) u :=
    fun k => (hsize m k).mono_const (le_max_right _ _)
  have hmu (m) : A.TensorWeightedBound τ m (E m*δ^2*η^(q+1))
      (A.tensorPlaneRestore (fun i => (d i).quadraticMean hρ δ q (A.tensorPlaneRead i u)) - δ^2 • H) := by
    intro k
    have hh := (herror m k).shrink_scale hτ.le hτs
    apply hh.mono_const
    have hp := pow_le_pow_left₀ hηP0 hηP (q+1)
    calc
      δ^2*(differenceBound L C β κ q m*(τ/s+ε/τ^lossP)^(q+1)) ≤
          δ^2*(E m*η^(q+1)) := mul_le_mul_of_nonneg_left
            ((mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hηP0 _)).trans
              (mul_le_mul_of_nonneg_left hp (hE m))) (sq_nonneg δ)
      _ = _ := by ring
  apply hsmall G hG b hb hbρ hclose d hfit _ hmap hτ hs hτs hs1 hε hε1 η hη0 (hη.trans hη₁)
    le_rfl hd hK δ hδ hδτ u H hu hH hball hbu hmu
  intro a
  unfold freeGlobalPhase
  rw [hphase a.1]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.profiled_polynomial_atlas_small_increment_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.profiled_polynomial_atlas_small_increment_oai.{u_1}
