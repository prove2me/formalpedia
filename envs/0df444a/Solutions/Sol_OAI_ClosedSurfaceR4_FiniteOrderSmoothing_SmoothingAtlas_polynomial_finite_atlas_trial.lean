-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_finite_atlas_trial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:44:16.303666+00:00
-- url     : https://prove2.me/submissions/f0b53824-66a0-4163-9ad0-2c6c666bb8c1

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_polynomial_finite_atlas_mean

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
local instance coordinateFiberSpace_ra43caa_1 : NormedSpace ℝ TensorFiber := inferInstance
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
local instance sectionTensorSpace_ra43caa_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
local instance symmetryModelComplete_ra43caa_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelSpace
local instance symmetryModelComplete_ra43caa_2 : CompleteSpace TensorFiber := inferInstance
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
local instance phaseFiberNormed_ra43caa_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance phaseFiberSpace_ra43caa_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance phaseDualAdd_ra43caa_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance phaseDualSmul_ra43caa_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance phaseSectionNormed_ra43caa_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance phaseSectionSpace_ra43caa_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
local instance planeReadSectionSpace_ra43caa_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FiniteMeanThreshold
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A quantitative threshold for the actual finite mean iteration. The
radius and the finite value bound stay explicit in the conclusion. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteMean
open WeightedEstimates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem finite_substitution_at {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s : ℝ} (hs : 0 ≤ s) {reference H : E → F} {r0 r1 : ℝ} (hgap : r0 < r1)
    {L : ℕ} {T : ℝ → (E → F) → E → F} {B K : ℕ → ℝ → ℝ}
    (hT : MeanBounds U s reference r1 L T B K)
    {C : ℕ → ℝ} (hC : ∀ m, 1 ≤ C m) (hH : ContDiffOn ℝ ∞ H U)
    (hH0 : ∀ p ∈ U, ‖H p-reference p‖ ≤ r0)
    (hbH : ∀ m, WeightedBound U s m (C m) H) (n : ℕ) (D : ℝ)
    (hbD : ∀ j ≤ n, B 0 (sizeBound L C B j L) ≤ D)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hηD : r0+η*D < r1) :
    ∀ j ≤ n, ContDiffOn ℝ ∞ (trial H T η j) U ∧
      InTrialBall U reference r1 (trial H T η j) ∧
      (∀ m, WeightedBound U s m (sizeBound L C B j m) (trial H T η j)) ∧
      (∀ m, WeightedBound U s m (differenceBound L C B K j m*η^(j+1))
        (trial H T η j+T η (trial H T η j)-H)) := by
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


theorem finite_substitution_with_threshold {U : Set E} (hU : UniqueDiffOn ℝ U)
    {s : ℝ} (hs : 0 ≤ s) {reference H : E → F} {r0 r1 : ℝ} (hgap : r0 < r1)
    {L : ℕ} {T : ℝ → (E → F) → E → F} {B K : ℕ → ℝ → ℝ}
    (hT : MeanBounds U s reference r1 L T B K)
    {C : ℕ → ℝ} (hC : ∀ m, 1 ≤ C m) (hH : ContDiffOn ℝ ∞ H U)
    (hH0 : ∀ p ∈ U, ‖H p-reference p‖ ≤ r0)
    (hbH : ∀ m, WeightedBound U s m (C m) H) (n : ℕ) {D : ℝ} (hD : 0 < D)
    (hbD : ∀ j ≤ n, B 0 (sizeBound L C B j L) ≤ D) :
    0 < min 1 ((r1-r0)/(2*D)) ∧
    ∀ η : ℝ, 0 < η → η ≤ min 1 ((r1-r0)/(2*D)) →
    ∀ j ≤ n, ContDiffOn ℝ ∞ (trial H T η j) U ∧
      InTrialBall U reference r1 (trial H T η j) ∧
      (∀ m, WeightedBound U s m (sizeBound L C B j m) (trial H T η j)) ∧
      (∀ m, WeightedBound U s m (differenceBound L C B K j m*η^(j+1))
        (trial H T η j+T η (trial H T η j)-H)) := by
  refine ⟨lt_min zero_lt_one (div_pos (sub_pos.mpr hgap) (by positivity)),?_⟩
  intro η hη hsmall
  have hη1 : η ≤ 1 := hsmall.trans (min_le_left _ _)
  have hηD : r0+η*D < r1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2*D)).mp
      (hsmall.trans (min_le_right _ _))
    nlinarith
  exact finite_substitution_at hU hs hgap hT hC hH hH0 hbH n D hbD hη hη1 hηD

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PositivePolynomialBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit normal-frame budgets have fixed polynomial growth. This
keeps their exponents independent of multiplicative input constants. -/
noncomputable section
namespace ClosedSurfaceR4.RealModes

lemma polynomialBound_const {c : ℝ} (hc : 0 ≤ c) : HasPolynomialBound (fun _ => c) := by
  exact ⟨0,max 1 c,le_max_left _ _,fun x _ => ⟨hc,by
    simp only [pow_zero,mul_one]
    exact le_max_right (1 : ℝ) c⟩⟩

lemma HasPolynomialBound.add {f g : ℝ → ℝ} (hf : HasPolynomialBound f)
    (hg : HasPolynomialBound g) : HasPolynomialBound (fun x => f x+g x) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  obtain ⟨e,D,hD,hg⟩ := hg
  refine ⟨d+e,C+D,by linarith,?_⟩
  intro x hx
  have hf' := hf x hx
  have hg' := hg x hx
  refine ⟨add_nonneg hf'.1 hg'.1,?_⟩
  calc
    f x+g x ≤ C*x^d+D*x^e := add_le_add hf'.2 hg'.2
    _ ≤ C*x^(d+e)+D*x^(d+e) := add_le_add
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (Nat.le_add_right d e)) (zero_le_one.trans hC))
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (Nat.le_add_left e d)) (zero_le_one.trans hD))
    _ = (C+D)*x^(d+e) := by ring

lemma HasPolynomialBound.mul {f g : ℝ → ℝ} (hf : HasPolynomialBound f)
    (hg : HasPolynomialBound g) : HasPolynomialBound (fun x => f x*g x) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  obtain ⟨e,D,hD,hg⟩ := hg
  refine ⟨d+e,C*D,by
    nlinarith [mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hD)],?_⟩
  intro x hx
  have hf' := hf x hx
  have hg' := hg x hx
  refine ⟨mul_nonneg hf'.1 hg'.1,?_⟩
  calc
    f x*g x ≤ (C*x^d)*(D*x^e) := mul_le_mul hf'.2 hg'.2 hg'.1
      (mul_nonneg (zero_le_one.trans hC) (pow_nonneg (zero_le_one.trans hx) _))
    _ = (C*D)*x^(d+e) := by rw [pow_add]; ring

lemma HasPolynomialBound.pow {f : ℝ → ℝ} (hf : HasPolynomialBound f) (n : ℕ) :
    HasPolynomialBound (fun x => (f x)^n) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  refine ⟨d*n,C^n,one_le_pow₀ hC,?_⟩
  intro x hx
  have hh := hf x hx
  refine ⟨pow_nonneg hh.1 _,?_⟩
  calc
    (f x)^n ≤ (C*x^d)^n := pow_le_pow_left₀ hh.1 hh.2 _
    _ = C^n*x^(d*n) := by rw [mul_pow,pow_mul]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialBudgetAlgebra
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite composition and inverse-scale evaluation of the polynomial
budgets in the correction construction. -/
noncomputable section
namespace ClosedSurfaceR4.RealModes

lemma HasPolynomialBound.of_le {f g : ℝ → ℝ} (hg : HasPolynomialBound g)
    (h0 : ∀ x, 1 ≤ x → 0 ≤ f x) (hle : ∀ x, 1 ≤ x → f x ≤ g x) :
    HasPolynomialBound f := by
  obtain ⟨d,C,hC,hg⟩ := hg
  exact ⟨d,C,hC,fun x hx => ⟨h0 x hx,(hle x hx).trans (hg x hx).2⟩⟩

lemma HasPolynomialBound.max {f g : ℝ → ℝ} (hf : HasPolynomialBound f)
    (hg : HasPolynomialBound g) : HasPolynomialBound (fun x => max (f x) (g x)) := by
  have hfn : ∀ x, 1 ≤ x → 0 ≤ f x := by
    obtain ⟨_,_,_,h⟩ := hf
    exact fun x hx => (h x hx).1
  have hgn : ∀ x, 1 ≤ x → 0 ≤ g x := by
    obtain ⟨_,_,_,h⟩ := hg
    exact fun x hx => (h x hx).1
  exact (hf.add hg).of_le (fun x hx => (hfn x hx).trans (le_max_left _ _))
    (fun x hx => max_le (le_add_of_nonneg_right (hgn x hx)) (le_add_of_nonneg_left (hfn x hx)))

lemma HasPolynomialBound.sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, HasPolynomialBound (f i)) :
    HasPolynomialBound (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using polynomialBound_const (show (0:ℝ) ≤ 0 by rfl)
  | @insert i s hi ih =>
    have h := (hf i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi] using h

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMeanIteration
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial growth of the actual finite mean iteration and of the
finite value budget appearing in its explicit smallness threshold. -/
noncomputable section
namespace ClosedSurfaceR4.RealModes

lemma HasPolynomialBound.nonneg {f : ℝ → ℝ} (hf : HasPolynomialBound f)
    {x : ℝ} (hx : 1 ≤ x) : 0 ≤ f x := by
  obtain ⟨_,_,_,h⟩ := hf
  exact (h x hx).1

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.PhaseMean
open RealModes FiniteMean

theorem polynomialMeanProfile_growth (p : ℕ → ℕ) (C : ℕ → ℝ)
    (G : ℕ → ℝ → ℝ) (hC : ∀ m, 0 ≤ C m) (hG : ∀ m, HasPolynomialBound (G m))
    (m : ℕ) {H : ℝ → ℝ} (hH : HasPolynomialBound H) :
    HasPolynomialBound (fun x => polynomialMeanProfile p C (fun r => G r x) m (H x)) :=
  (polynomialBound_const (hC m)).mul
    (((hG m).add ((polynomialBound_const zero_le_one).max hH)).pow (p m))

theorem polynomialMeanSize_growth (L : ℕ) (p : ℕ → ℕ) (C : ℕ → ℝ)
    (G H : ℕ → ℝ → ℝ) (hC : ∀ m, 0 ≤ C m)
    (hG : ∀ m, HasPolynomialBound (G m)) (hH : ∀ m, HasPolynomialBound (H m))
    (j m : ℕ) : HasPolynomialBound (polynomialMeanSize L p C G H j m) := by
  induction j generalizing m with
  | zero => exact hH m
  | succ j ih =>
    exact (hH m).add (polynomialMeanProfile_growth p C G hC hG m (ih (m+L)))

theorem polynomialMeanDifference_growth (L : ℕ) (p : ℕ → ℕ) (C : ℕ → ℝ)
    (G H : ℕ → ℝ → ℝ) (hC : ∀ m, 0 ≤ C m)
    (hG : ∀ m, HasPolynomialBound (G m)) (hH : ∀ m, HasPolynomialBound (H m))
    (j m : ℕ) : HasPolynomialBound (polynomialMeanDifference L p C G H j m) := by
  induction j generalizing m with
  | zero => exact polynomialMeanProfile_growth p C G hC hG m (hH (m+L))
  | succ j ih =>
    exact (polynomialMeanProfile_growth p C G hC hG m
      ((polynomialMeanSize_growth L p C G H hC hG hH (j+1) (m+L)).max
        (polynomialMeanSize_growth L p C G H hC hG hH j (m+L)))).mul (ih (m+L))

/-- A polynomial upper bound for the finite quantity controlling the
radius of the mean iteration; it is uniform in the iteration index. -/
theorem polynomialMean_threshold_budget (L : ℕ) (p : ℕ → ℕ) (C : ℕ → ℝ)
    (G H : ℕ → ℝ → ℝ) (hC : ∀ m, 0 ≤ C m)
    (hG : ∀ m, HasPolynomialBound (G m)) (hH : ∀ m, HasPolynomialBound (H m)) (n : ℕ) :
    ∃ d : ℕ, ∃ A : ℝ, 1 ≤ A ∧ ∀ x : ℝ, 1 ≤ x → ∀ j ≤ n,
      polynomialMeanProfile p C (fun r => G r x) 0 (polynomialMeanSize L p C G H j L x) ≤ A*x^d := by
  let f := fun j x => polynomialMeanProfile p C (fun r => G r x) 0
    (polynomialMeanSize L p C G H j L x)
  have hf (j : ℕ) : HasPolynomialBound (f j) :=
    polynomialMeanProfile_growth p C G hC hG 0 (polynomialMeanSize_growth L p C G H hC hG hH j L)
  obtain ⟨d,A,hA,hsum⟩ := HasPolynomialBound.sum (Finset.range (n+1)) f (fun j _ => hf j)
  refine ⟨d,A,hA,?_⟩
  intro x hx j hj
  exact (Finset.single_le_sum (fun i _ => (hf i).nonneg hx)
    (Finset.mem_range.mpr (by omega : j < n+1))).trans (hsum x hx).2

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialBudgetMeanFamily
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Assemble the actual finite metric mean from one common bound on its
seven local budgets. The envelope records the derivative shift explicitly. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean

lemma meanGeometryEnvelope_growth (q : ℕ) (H B : ℕ → ℝ → ℝ)
    (hH : ∀ m, HasPolynomialBound (H m)) (hB : ∀ m, HasPolynomialBound (B m))
    (m : ℕ) : HasPolynomialBound (fun x =>
      meanGeometryEnvelope q (fun k => H k x) (fun k => B k x) m) :=
  (((polynomialBound_const zero_le_one).add (hH m)).add (hB (m+q+2))).add (hB m)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMeanTransport
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit polynomial majorants survive the read/restore operations in
an atlas. All dependence on transport constants stays in the profile. -/
noncomputable section
namespace ClosedSurfaceR4.PhaseMean
open RealModes

lemma transportedMeanGeometry_growth (L : ℕ) (G D E : ℕ → ℝ → ℝ)
    (hG : ∀ m, HasPolynomialBound (G m)) (hD : ∀ m, HasPolynomialBound (D m))
    (hE : ∀ m, HasPolynomialBound (E m)) (m : ℕ) :
    HasPolynomialBound (fun x => transportedMeanGeometry L
      (fun r => G r x) (fun r => D r x) (fun r => E r x) m) :=
  (((polynomialBound_const zero_le_one).add (hG m)).add (hD (m+L))).add (hE m)

end ClosedSurfaceR4.PhaseMean

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
local instance iterationModelSpace_ra43caa_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance iterationDualSmul_ra43caa_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance iterationSectionTensorNormed_ra43caa_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance iterationSectionTensorSpace_ra43caa_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
local instance atlasMeanDualAdd_ra43caa_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasMeanDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasMeanFiberNormed
local instance atlasMeanSectionNormed_ra43caa_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasMeanSectionSpace_ra43caa_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma atlasMean_symmetric
    (μ : A.centers → (SmallModes.Base → Tensor) → SmallModes.Base → Tensor)
    (u : ∀ x : M, CovariantTwoTensor x) : ∀ p v w, A.atlasMean μ u p v w = A.atlasMean μ u p w v :=
  A.tensorPlaneRestore_symmetric _

lemma tensorReadBallConstant_ball
    (reference : ∀ x : M, CovariantTwoTensor x)
    (href : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (reference x)))
    (f : Base → A.centers → TensorFiber) (r : ℝ) (hr : 0 ≤ r)
    (hf : ContDiff ℝ ∞ f) (hb : InTrialBall univ (A.tensorEncode reference) r f)
    (i : A.centers) :
    InTrialBall univ (A.tensorPlaneRead i reference) (A.tensorReadBallConstant*r)
      (A.tensorPlaneRead i (A.tensorDecode f)) :=
  (Classical.choose_spec A.tensorPlaneRead_decode_ball).2 reference href f r hr hf hb i

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialTensorMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit polynomial threshold for the actual global tensor iteration. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean RealModes WeightedEstimates FiniteMean
open JetPolynomial (Base)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialTensorMeanDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialTensorMeanDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialTensorMeanFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialTensorMeanFiberSpace
local instance polynomialTensorMeanSectionNormed_ra43caa_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialTensorMeanSectionSpace_ra43caa_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem polynomial_tensor_mean_threshold (L : ℕ) (p : ℕ → ℕ) (C : ℕ → ℝ)
    (G H : ℕ → ℝ → ℝ) (hC : ∀ m, 0 ≤ C m)
    (hG : ∀ m, HasPolynomialBound (G m)) (hH : ∀ m, HasPolynomialBound (H m)) (steps : ℕ) :
    ∃ d : ℕ, ∃ E : ℝ, 1 ≤ E ∧ ∀ x : ℝ, 1 ≤ x →
      ∀ {s : ℝ}, 0 < s → ∀ reference f : ∀ y : M, CovariantTwoTensor y,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (f y)) →
      ∀ r₀ r : ℝ, r₀ < r →
      (∀ y, ‖A.tensorEncode f y-A.tensorEncode reference y‖ ≤ r₀) →
      (∀ m, 1 ≤ H m x) → (∀ m, A.TensorWeightedBound s m (H m x) f) →
      ∀ η : ℝ, 0 < η → η ≤ min 1 ((r-r₀)/(2*(E*x^d))) →
      ∀ T : (∀ y : M, CovariantTwoTensor y) → ∀ y : M, CovariantTwoTensor y,
      MeanBounds univ s (A.tensorEncode reference) r L
        (rescaledMean η (A.tensorMeanOperator T))
        (polynomialMeanProfile p C (fun m => G m x))
        (polynomialMeanProfile p C (fun m => G m x)) →
      ∀ j ≤ steps,
        ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
          (fun y => TotalSpace.mk' TensorFiber y (A.tensorMeanTrial f T j y)) ∧
        InTrialBall univ (A.tensorEncode reference) r (A.tensorEncode (A.tensorMeanTrial f T j)) ∧
        (∀ m, A.TensorWeightedBound s m (polynomialMeanSize L p C G H j m x)
          (A.tensorMeanTrial f T j)) ∧
        (∀ m, A.TensorWeightedBound s m (polynomialMeanDifference L p C G H j m x*η^(j+1))
          (A.tensorMeanTrial f T j+T (A.tensorMeanTrial f T j)-f)) := by
  obtain ⟨d,E,hE,hvalue⟩ := polynomialMean_threshold_budget L p C G H hC hG hH steps
  refine ⟨d,E,hE,?_⟩
  intro x hx s hs reference f hf r₀ r hgap hnear hH1 hbound η hη hsmall T hT j hj
  have henc := A.tensorEncode_smooth hf
  have hh := finite_substitution_with_threshold uniqueDiffOn_univ hs.le hgap hT hH1 henc.contDiffOn
    (fun y _ => hnear y)
    (fun m => A.tensorEncode_bound hf hs (zero_le_one.trans (hH1 m)) (hbound m)) steps
    (mul_pos (zero_lt_one.trans_le hE) (pow_pos (zero_lt_one.trans_le hx) d)) (hvalue x hx)
  obtain ⟨ha,hb,hc,hd⟩ := hh.2 η hη hsmall j hj
  rw [trial_rescaledMean hη.ne'] at ha hb hc hd
  rw [rescaledMean_self hη.ne'] at hd
  have htrial : ContDiff ℝ ∞ (fixedTrial (A.tensorEncode f) (A.tensorMeanOperator T) j) :=
    contDiffOn_univ.mp ha
  have hη1 : η ≤ 1 := hsmall.trans (min_le_left _ _)
  have hmean : ContDiff ℝ ∞ (A.tensorMeanOperator T
      (fixedTrial (A.tensorEncode f) (A.tensorMeanOperator T) j)) := by
    have h := hT.smooth η hη hη1 _ ha hb
    rw [rescaledMean_self hη.ne'] at h
    exact contDiffOn_univ.mp h
  have hres : ContDiff ℝ ∞ (A.tensorEncode
      (A.tensorMeanTrial f T j+T (A.tensorMeanTrial f T j)-f)) := by
    rw [A.tensorEncode_meanResidual]
    exact (htrial.add hmean).sub henc
  refine ⟨A.tensorDecode_smooth htrial,?_,?_,?_⟩
  · rw [A.tensorEncode_meanTrial]
    exact hb
  · intro m
    apply A.tensorBound_of_encode (by rw [A.tensorEncode_meanTrial]; exact htrial) hs.le
      (zero_le_one.trans (sizeBound_ge_one hH1 hT.B_pos j m))
    rw [A.tensorEncode_meanTrial]
    exact hc m
  · intro m
    apply A.tensorBound_of_encode hres hs.le
      (mul_nonneg (differenceBound_nonneg hH1 hT.B_pos hT.K_pos j m) (pow_nonneg hη.le _))
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
local instance symmetricMeanFiberNormed_ra43caa_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance symmetricMeanFiberSpace_ra43caa_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance symmetricMeanDualAdd_ra43caa_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance symmetricMeanDualSmul_ra43caa_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance symmetricMeanSectionNormed_ra43caa_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance symmetricMeanSectionSpace_ra43caa_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialFiniteAtlasTrial
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! One polynomial profile for all actual grid amplitudes, before the variable family. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialFiniteTrialDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialFiniteTrialDualSmul
variable (A : SmoothingAtlas M)


attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialFiniteTrialFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialFiniteTrialFiberSpace
local instance polynomialFiniteTrialSectionNormed_ra43caa_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialFiniteTrialSectionSpace_ra43caa_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem polynomial_finite_atlas_trial_oai (q : ℕ) (B H Y : ℕ → ℝ → ℝ)
    (hB : ∀ m, HasPolynomialBound (B m)) (hH : ∀ m, HasPolynomialBound (H m))
    (hY : ∀ m, HasPolynomialBound (Y m)) :
    ∃ e : ℕ, ∃ E : ℝ, ∃ S T : ℕ → ℝ → ℝ, 1 ≤ E ∧
      (∀ m, HasPolynomialBound (S m)) ∧ (∀ m, HasPolynomialBound (T m)) ∧
    ∀ x : ℝ, 1 ≤ x →
    ∀ (reference : ∀ y : M, CovariantTwoTensor y),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (reference y)) →
    ∀ r : ℝ, 0 < r → ∀ {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
      {n : A.centers → ℕ} {P : ∀ i, Fin 3 → Fin (n i) → Expression}
      {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
      {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
      {τ : ℝ} {s : ℝ≥0}
      {c : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) τ s}
      {ρ R : ℝ}
      (d : ∀ i j, ChartedMeanData (c i j) (A.tensorReadBallConstant*r) ρ R
        (A.tensorPlaneRead i reference)),
      ∀ hρ : 0 < ρ, 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      (∀ m, 1 ≤ H m x) → (∀ m, 1 ≤ Y m x) →
      (∀ i m, (Fintype.card (ι i) : ℝ) ≤ H m x ∧ ρ⁻¹ ≤ H m x) →
      (∀ i j m, (d i j).budgets.inv m ≤ B m x ∧ (d i j).budgets.chi m ≤ B m x ∧
        (d i j).budgets.forms m ≤ B m x ∧ (d i j).budgets.pull m ≤ B m x ∧
        (d i j).budgets.psi m ≤ B m x ∧ (d i j).budgets.normal m ≤ B m x ∧
        (d i j).budgets.mode m ≤ B m x) →
      (τ/s) ≤ min 1 ((r-r/2)/(2*(E*x^e))) →
      ∀ f : ∀ y : M, CovariantTwoTensor y,
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (f y)) →
      (∀ y v w, f y v w = f y w v) →
      (∀ y, ‖A.tensorEncode f y-A.tensorEncode reference y‖ ≤ r/2) →
      (∀ m, A.TensorWeightedBound s m (Y m x) f) →
      ∀ δ : ℝ, 0 < δ → ∃ u : ∀ y : M, CovariantTwoTensor y,
        ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
          (fun y => TotalSpace.mk' TensorFiber y (u y)) ∧
        (∀ y v w, u y v w = u y w v) ∧
        FiniteMean.InTrialBall univ (A.tensorEncode reference) r (A.tensorEncode u) ∧
        (∀ i, FiniteMean.InTrialBall univ (A.tensorPlaneRead i reference)
          (A.tensorReadBallConstant*r) (A.tensorPlaneRead i u)) ∧
        (∀ m, A.TensorWeightedBound s m (S m x) u) ∧
        (∀ m, A.TensorWeightedBound s m (T m x*(τ/s)^(q+1))
          (u+A.atlasMean (fun i => chartedFamilyMean (d i) hρ δ q) u-f)) := by
  classical
  obtain ⟨p,C,D,E,hC,hD,hE,hmean⟩ := A.polynomial_finite_atlas_mean q
  let p' := fun m => 2*p m+2
  let C' := fun m => 1+C m
  let Z := fun m x => transportedMeanGeometry (q+2)
    (meanGeometryEnvelope q (fun j => H j x) (fun j => B j x)) D E m
  have hC' (m : ℕ) : 0 ≤ C' m := by dsimp [C'] <;> linarith [hC m]
  have hZ (m : ℕ) : HasPolynomialBound (Z m) :=
    transportedMeanGeometry_growth (q+2)
      (fun m x => meanGeometryEnvelope q (fun j => H j x) (fun j => B j x) m)
      (fun m _ => D m) (fun m _ => E m)
      (meanGeometryEnvelope_growth q H B hH hB)
      (fun m => polynomialBound_const (zero_le_one.trans (hD m)))
      (fun m => polynomialBound_const (hE m)) m
  obtain ⟨e,A₀,hA₀,htrial⟩ := A.polynomial_tensor_mean_threshold (q+2) p' C' Z Y hC' hZ hY q
  let S := polynomialMeanSize (q+2) p' C' Z Y q
  let T := polynomialMeanDifference (q+2) p' C' Z Y q
  have hS (m : ℕ) : HasPolynomialBound (S m) :=
    polynomialMeanSize_growth (q+2) p' C' Z Y hC' hZ hY q m
  have hT (m : ℕ) : HasPolynomialBound (T m) :=
    polynomialMeanDifference_growth (q+2) p' C' Z Y hC' hZ hY q m
  refine ⟨e,A₀,S,T,hA₀,hS,hT,?_⟩
  intro x hx reference href r hr ι _ n P G hG φ K τ s c ρ R d hρ hτ hs hτs hs1
    hHx hYx hcard hbud hsmall f hf hsym hnear hsize δ hδ
  have hBx (m : ℕ) : 0 ≤ B m x := by
    obtain ⟨_,_,_,hh⟩ := hB m
    exact (hh x hx).1
  let μ := A.atlasMean (fun i => chartedFamilyMean (d i) hρ δ q)
  have hm := hmean reference href r hr.le d hρ hτ hs hτs hs1
    (fun m => H m x) (fun m => B m x) hHx hBx hcard hbud δ hδ
  have ht := htrial x hx hs reference f hf (r/2) r (by linarith)
    hnear hYx hsize (τ/s) (div_pos hτ hs) hsmall μ hm q le_rfl
  let u := A.tensorMeanTrial f μ q
  have hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun y => TotalSpace.mk' TensorFiber y (u y)) := ht.1
  have hb := ht.2.1
  have hlocal (i : A.centers) := A.tensorReadBallConstant_ball reference href
    (A.tensorEncode u) r hr.le (A.tensorEncode_smooth hu) hb i
  simp only [A.tensorDecode_encode] at hlocal
  exact ⟨u,hu,A.tensorMeanTrial_symmetric f μ hsym
    (fun v _ => A.atlasMean_symmetric _ v) q,hb,hlocal,ht.2.2.1,ht.2.2.2⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_finite_atlas_trial_oai.{u_1, u_2} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_finite_atlas_trial_oai.{u_1, u_2}
