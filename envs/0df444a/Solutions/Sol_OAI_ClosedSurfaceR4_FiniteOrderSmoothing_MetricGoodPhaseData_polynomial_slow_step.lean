-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.polynomial_slow_step
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:31:11.832052+00:00
-- url     : https://prove2.me/submissions/e8747ac8-f73c-4236-8ac7-1fca86a0dc32

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
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_polynomial_small_increment

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



lemma WeightedBound.mono_order {U : Set E} {s C : ℝ} {m r : ℕ} {f : E → F}
    (h : WeightedBound U s m C f) (hr : r ≤ m) : WeightedBound U s r C f :=
  fun j hj => h j (hj.trans hr)


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

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldSmoothingLinearity
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global smoothing construction is linear on smooth maps. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma localize_add (p : M) (ψ : M → ℝ) (f g : M → V) :
    localize p ψ (f + g) = localize p ψ f + localize p ψ g := by
  funext x
  by_cases hx : x ∈ (chart p).target <;> simp [localize, hx, smul_add]

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
local instance coordinateFiberSpace_rab5283_1 : NormedSpace ℝ TensorFiber := inferInstance
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
local instance symmetryModelComplete_rab5283_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelSpace
local instance symmetryModelComplete_rab5283_2 : CompleteSpace TensorFiber := inferInstance
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
local instance phaseFiberNormed_rab5283_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance phaseFiberSpace_rab5283_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance phaseDualAdd_rab5283_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance phaseDualSmul_rab5283_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance phaseSectionNormed_rab5283_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance phaseSectionSpace_rab5283_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
local instance planeReadSectionSpace_rab5283_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasMetricBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness and elementary norm operations for actual global metric tensors. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricBoundDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricBoundDualSmul
variable (A : SmoothingAtlas M)
include A

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricBoundFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricBoundFiberSpace
local instance metricBoundSectionNormed_rab5283_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricBoundSectionSpace_rab5283_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorWeightedBound_add {T S : ∀ p : M, CovariantTwoTensor p}
    (hT : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (T p)))
    (hS : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (S p)))
    {s C D : ℝ} {m : ℕ} (hs : 0 ≤ s)
    (hbT : A.TensorWeightedBound s m C T) (hbS : A.TensorWeightedBound s m D S) :
    A.TensorWeightedBound s m (C+D) (T+S) := by
  intro i
  change WeightedEstimates.WeightedBound univ s m (C+D) (A.bundleLocalize A.tensorTriv i (T+S))
  rw [A.bundleLocalize_add]
  exact (hbT i).add uniqueDiffOn_univ hs
    (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hT).contDiffOn
    (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hS).contDiffOn (hbS i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialPerturbationCalculus
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The perturbation operators and their actual first variations. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Perturbation

variable {n : ℕ}

lemma eval_smooth {O : Set LowJet} {U : Set Base} {P : Fin n → Expression}
    (hP : ∀ l, (P l).SmoothCoeffs O) (ε : ℝ) {G : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) U O) :
    ContDiffOn ℝ ∞ (eval P ε G) (U ×ˢ Set.univ) := by
  exact ContDiffOn.sum (fun l _ => contDiffOn_const.mul ((P l).eval_smooth hG hQ (hP l)))

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialValueBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform evaluation bounds for the polynomial part of the actual mean
metric. The loss is fixed by P, before any accuracy order is chosen. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

lemma coordinatePolynomialValue_smooth {n : ℕ} {P : Fin 3 → Fin n → Expression}
    (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ) {G : Base → Space}
    (hG : ContDiff ℝ ∞ G) (ε : ℝ) :
    ContDiff ℝ ∞ (coordinatePolynomialValue P ε G 0) := by
  apply contDiff_pi.mpr
  intro k
  have hs : ContDiff ℝ ∞ (fun p : Base => eval (P k) ε G (p,0)) := by
    have he : ContDiff ℝ ∞ (eval (P k) ε G) := contDiffOn_univ.mp (by
      simpa only [Set.univ_prod_univ] using
        (eval_smooth (U := Set.univ) (hP k) ε hG (fun _ _ => Set.mem_univ _)))
    exact he.comp (contDiff_id.prodMk contDiff_const)
  change ContDiff ℝ ∞ ((fun p : Base => eval (P k) ε G (p,0)) ∘ planeCoordinateIsometry.symm)
  exact hs.comp planeCoordinateIsometry.symm.contDiff

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialMetric
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual globally restored polynomial perturbation of the metric,
with its exact first, second and higher-order variation decomposition. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialMetricDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialMetricDualSmul
variable (A : SmoothingAtlas M)
variable {n : A.centers → ℕ}

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialMetricFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialMetricFiberNormed
local instance polynomialMetricSectionNormed_rab5283_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialMetricSectionSpace_rab5283_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma atlasPolynomialValue_symmetric
    (P : (i : A.centers) → Fin 3 → Fin (n i) → Expression) (ε : ℝ) (G : M → Space) :
    ∀ x v w, A.atlasPolynomialValue P ε G x v w = A.atlasPolynomialValue P ε G x w v :=
  A.tensorPlaneRestore_symmetric _

omit [CompactSpace M] in
lemma atlasPolynomialMetric_symmetric
    (P : (i : A.centers) → Fin 3 → Fin (n i) → Expression) (ε : ℝ) (G : M → Space) :
    ∀ x v w, A.atlasPolynomialMetric P ε G x v w = A.atlasPolynomialMetric P ε G x w v := by
  intro x v w
  change inducedTensor G x v w+A.atlasPolynomialValue P ε G x v w =
    inducedTensor G x w v+A.atlasPolynomialValue P ε G x w v
  rw [inducedTensor_symmetric G x v w,A.atlasPolynomialValue_symmetric P ε G x v w]

lemma atlasPolynomialValue_smooth
    {P : (i : A.centers) → Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ) {G : M → Space}
    (hG : ContMDiff planeModel spaceModel ∞ G) (ε : ℝ) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (A.atlasPolynomialValue P ε G x)) :=
  A.tensorPlaneRestore_smooth (fun i => coordinatePolynomialValue_smooth (hP i)
    (A.jetChartMap_smooth i hG) ε)

lemma atlasPolynomialMetric_smooth
    {P : (i : A.centers) → Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ) {G : M → Space}
    (hG : ContMDiff planeModel spaceModel ∞ G) (ε : ℝ) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (A.atlasPolynomialMetric P ε G x)) :=
  (A.inducedTensor_smooth hG).add_section (A.atlasPolynomialValue_smooth hP hG ε)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedAtlasQuadraticResidual
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact zero-phase residual of the actual charted free family. -/
noncomputable section
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean PhaseGeometry WeightedEstimates FiniteMean
open JetPolynomial (Base)
open JetPolynomial.Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasSectionNormed
local instance quadraticAtlasSectionSpace_rab5283_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorWeightedBound_const_smul
    {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (u x)))
    {s C : ℝ} {m : ℕ}
    (hb : A.TensorWeightedBound s m C u) (a : ℝ) :
    A.TensorWeightedBound s m (|a| * C) (a • u) := by
  intro i
  have hb' := (hb i).const_smul uniqueDiffOn_univ
    (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hu).contDiffOn a
  change _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m (|a| * C) (A.bundleLocalize A.tensorTriv i (a • u))
  rw [A.bundleLocalize_smul]
  exact hb'

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_GlobalMetricStepBound
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global weighted estimate for the concrete unsmoothed normalized-defect update. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.stepBoundDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.stepBoundDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.stepBoundFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.stepBoundFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.stepBoundSectionNormed
local instance stepBoundSectionSpace_rab5283_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorWeightedBound_sub {T S : ∀ p : M, CovariantTwoTensor p}
    (hT : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (T p)))
    (hS : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (S p)))
    {s C D : ℝ} {m : ℕ} (hs : 0 ≤ s)
    (hbT : A.TensorWeightedBound s m C T) (hbS : A.TensorWeightedBound s m D S) :
    A.TensorWeightedBound s m (C+D) (T-S) := by
  intro i
  have he : A.bundleLocalize A.tensorTriv i (T-S) =
      A.bundleLocalize A.tensorTriv i T - A.bundleLocalize A.tensorTriv i S := by
    funext x
    by_cases hx : x ∈ (chart (i : M)).target <;>
      simp [bundleLocalize,localize,bundleComponent,hx,smul_sub]
  change WeightedEstimates.WeightedBound univ s m (C+D) (A.bundleLocalize A.tensorTriv i (T-S))
  rw [he]
  exact (hbT i).sub uniqueDiffOn_univ hs
    (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hT).contDiffOn
    (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hS).contDiffOn (hbS i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPrimitiveMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact normalized mean identities for the global primitive iteration.
The residual is always that of the actual restored polynomial metric. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasPrimitiveDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasPrimitiveDualSmul
variable (A : SmoothingAtlas M) {n : A.centers → ℕ}

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasPrimitiveFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasPrimitiveFiberNormed
local instance atlasPrimitiveSectionNormed_rab5283_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasPrimitiveSectionSpace_rab5283_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma polynomialMeanTarget_eq
    (P : (i : A.centers) → Fin 3 → Fin (n i) → Expression) (ε δ δ' : ℝ)
    (γ : ∀ x : M, CovariantTwoTensor x) (G : M → Space) :
    A.polynomialMeanTarget P ε δ δ' γ G =
      γ+A.normalizedPolynomialDefect P ε δ γ G-(δ'^2/δ^2) • γ := by
  funext x
  ext v w
  change (δ^2)⁻¹*(γ x v w-A.atlasPolynomialMetric P ε G x v w-δ'^2*γ x v w) =
    γ x v w+((δ^2)⁻¹*(γ x v w-A.atlasPolynomialMetric P ε G x v w)-γ x v w)-
      (δ'^2/δ^2)*γ x v w
  ring

lemma normalizedPolynomialDefect_smooth
    {P : (i : A.centers) → Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ) {ε δ : ℝ}
    {γ : ∀ x : M, CovariantTwoTensor x}
    (hγ : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (γ x)))
    {G : M → Space} (hG : ContMDiff planeModel spaceModel ∞ G) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (A.normalizedPolynomialDefect P ε δ γ G x)) :=
  (((hγ.sub_section (A.atlasPolynomialMetric_smooth hP hG ε)).const_smul_section).sub_section hγ)

lemma polynomialMeanTarget_smooth
    {P : (i : A.centers) → Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ) {ε δ δ' : ℝ}
    {γ : ∀ x : M, CovariantTwoTensor x}
    (hγ : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (γ x)))
    {G : M → Space} (hG : ContMDiff planeModel spaceModel ∞ G) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (A.polynomialMeanTarget P ε δ δ' γ G x)) :=
  ((hγ.sub_section (A.atlasPolynomialMetric_smooth hP hG ε)).sub_section
    (hγ.const_smul_section (a := δ'^2))).const_smul_section

lemma normalizedPolynomialDefect_after_step
    {P : (i : A.centers) → Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
    {ε δ δ' s C : ℝ} {m : ℕ} (hδ : δ ≠ 0) (hδ' : δ' ≠ 0)
    {γ : ∀ x : M, CovariantTwoTensor x}
    (hγ : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (γ x)))
    {G G' : M → Space} (hG : ContMDiff planeModel spaceModel ∞ G)
    (hG' : ContMDiff planeModel spaceModel ∞ G')
    (hb : A.TensorWeightedBound s m C
      (A.atlasPolynomialMetric P ε G'-A.atlasPolynomialMetric P ε G-
        δ^2 • A.polynomialMeanTarget P ε δ δ' γ G)) :
    A.TensorWeightedBound s m (C/δ'^2) (A.normalizedPolynomialDefect P ε δ' γ G') := by
  have he : A.normalizedPolynomialDefect P ε δ' γ G' =
      (-(δ'^2)⁻¹) • (A.atlasPolynomialMetric P ε G'-A.atlasPolynomialMetric P ε G-
        δ^2 • A.polynomialMeanTarget P ε δ δ' γ G) := by
    funext x
    ext v w
    change (δ'^2)⁻¹*(γ x v w-A.atlasPolynomialMetric P ε G' x v w)-γ x v w =
      -(δ'^2)⁻¹*(A.atlasPolynomialMetric P ε G' x v w-A.atlasPolynomialMetric P ε G x v w-
        δ^2*((δ^2)⁻¹*(γ x v w-A.atlasPolynomialMetric P ε G x v w-δ'^2*γ x v w)))
    field_simp
    ring
  have hT := A.polynomialMeanTarget_smooth (ε := ε) (δ := δ) (δ' := δ') hP hγ hG
  have hsmooth := ((A.atlasPolynomialMetric_smooth hP hG' ε).sub_section
    (A.atlasPolynomialMetric_smooth hP hG ε)).sub_section
      (hT.const_smul_section (a := δ^2))
  have hh := A.tensorWeightedBound_const_smul hsmooth hb (-(δ'^2)⁻¹)
  rw [← he] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rw [abs_neg,abs_of_pos (inv_pos.mpr (sq_pos_of_ne_zero hδ'))]
  ring


/-- The next input stays in the same bounded family whenever the old
normalized defect does. -/
lemma polynomialMeanTarget_bound
    {P : (i : A.centers) → Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
    {ε δ δ' s A₀ B₀ : ℝ} {m : ℕ} (hδ : 0 < δ) (hδ' : 0 ≤ δ')
    (hδδ : δ' ≤ δ) (hs : 0 ≤ s) (hA₀ : 0 ≤ A₀)
    {γ : ∀ x : M, CovariantTwoTensor x}
    (hγ : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (γ x)))
    {G : M → Space} (hG : ContMDiff planeModel spaceModel ∞ G)
    (hγb : A.TensorWeightedBound s m A₀ γ)
    (hDb : A.TensorWeightedBound s m B₀ (A.normalizedPolynomialDefect P ε δ γ G)) :
    A.TensorWeightedBound s m (2*A₀+B₀) (A.polynomialMeanTarget P ε δ δ' γ G) := by
  have hr : 0 ≤ δ'^2/δ^2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hr1 : δ'^2/δ^2 ≤ 1 := (div_le_one (sq_pos_of_pos hδ)).2 (by nlinarith)
  have hscaled := A.tensorWeightedBound_const_smul hγ hγb (δ'^2/δ^2)
  have hscaled' : A.TensorWeightedBound s m A₀ ((δ'^2/δ^2) • γ) := by
    intro i
    apply (hscaled i).mono_const
    rw [abs_of_nonneg hr]
    exact mul_le_of_le_one_left hA₀ hr1
  have hD := A.normalizedPolynomialDefect_smooth (ε := ε) (δ := δ) hP hγ hG
  have hsum := A.tensorWeightedBound_add hγ hD hs hγb hDb
  have hsub := A.tensorWeightedBound_sub (hγ.add_section hD)
    (hγ.const_smul_section (a := δ'^2/δ^2)) hs hsum hscaled'
  rw [A.polynomialMeanTarget_eq]
  convert hsub using 1
  all_goals try with_reducible_and_instances rfl
  ring

omit [CompactSpace M] in
/-- Quantitative closeness of the next input in the fixed tensor encoding. -/
lemma polynomialMeanTarget_distance
    (P : (i : A.centers) → Fin 3 → Fin (n i) → Expression) (ε δ δ' : ℝ)
    (γ : ∀ x : M, CovariantTwoTensor x) (G : M → Space)
    (x : JetPolynomial.Base) {a b : ℝ}
    (hD : ‖A.tensorEncode (A.normalizedPolynomialDefect P ε δ γ G) x‖ ≤ a)
    (hγ : ‖A.tensorEncode γ x‖ ≤ b) :
    ‖A.tensorEncode (A.polynomialMeanTarget P ε δ δ' γ G) x-A.tensorEncode γ x‖ ≤
      a+(δ'^2/δ^2)*b := by
  rw [A.polynomialMeanTarget_eq,A.tensorEncode_sub,A.tensorEncode_add,A.tensorEncode_smul]
  change ‖(A.tensorEncode γ x+A.tensorEncode (A.normalizedPolynomialDefect P ε δ γ G) x-
    (δ'^2/δ^2) • A.tensorEncode γ x)-A.tensorEncode γ x‖ ≤ _
  have he : (A.tensorEncode γ x+A.tensorEncode (A.normalizedPolynomialDefect P ε δ γ G) x-
    (δ'^2/δ^2) • A.tensorEncode γ x)-A.tensorEncode γ x =
    A.tensorEncode (A.normalizedPolynomialDefect P ε δ γ G) x-
      (δ'^2/δ^2) • A.tensorEncode γ x := by abel
  rw [he]
  calc
    _ ≤ ‖A.tensorEncode (A.normalizedPolynomialDefect P ε δ γ G) x‖+
        ‖(δ'^2/δ^2) • A.tensorEncode γ x‖ := norm_sub_le _ _
    _ = ‖A.tensorEncode (A.normalizedPolynomialDefect P ε δ γ G) x‖+
        (δ'^2/δ^2)*‖A.tensorEncode γ x‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
    _ ≤ _ := add_le_add hD (mul_le_mul_of_nonneg_left hγ
      (div_nonneg (sq_nonneg _) (sq_nonneg _)))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CorrectionScaleAlgebra
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact scale arithmetic in the normalized metric-error estimate. -/
noncomputable section

namespace ClosedSurfaceR4.ExactCorrection

lemma scale_quotient_product {t : ℝ} (ht : 0 < t) (a b c : ℝ) :
    (t ^ a * t ^ b) / t ^ c = t ^ (a + b - c) := by
  rw [← Real.rpow_add ht, Real.rpow_sub ht]

lemma scale_ratio_power {t : ℝ} (ht : 0 < t) (a b c d e : ℝ) :
    (t ^ a * (t ^ b / t ^ c) ^ d) / (t ^ e) ^ (2 : ℕ) =
      t ^ (a + (b - c) * d - 2 * e) := by
  rw [← Real.rpow_sub ht, ← Real.rpow_mul ht.le]
  rw [← Real.rpow_natCast (t ^ e) 2, ← Real.rpow_mul ht.le]
  rw [scale_quotient_product ht]
  congr 1
  ring

lemma scale_cubic_quotient {t : ℝ} (ht : 0 < t) (a b c : ℝ) :
    ((t ^ a) ^ (3 : ℕ) / t ^ b) / (t ^ c) ^ (2 : ℕ) =
      t ^ (3 * a - b - 2 * c) := by
  rw [← Real.rpow_natCast (t ^ a) 3, ← Real.rpow_mul ht.le]
  rw [← Real.rpow_natCast (t ^ c) 2, ← Real.rpow_mul ht.le]
  rw [← Real.rpow_sub ht, ← Real.rpow_sub ht]
  congr 1
  ring

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ShiftedSmoothingBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothing bounds with an unweighted finite derivative prefix. In the
correction scheme the map has prefix order two and the metric defect order zero. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates MeasureTheory
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma ShiftedBound.deriv_le {q m : ℕ} {s C : ℝ} {f : Base → V}
    (h : ShiftedBound q m s C f) (hs : 0 < s) {j : ℕ} (hj : j ≤ q + m) (x : Base) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ C / s ^ (j - q) := by
  apply (le_div_iff₀ (pow_pos hs _)).mpr
  simpa only [mul_comm] using h j hj x

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FixedOrderThreshold
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At each fixed order, all analytic smallness conditions and the
finite derivative budget hold below one positive scale threshold. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace ClosedSurfaceR4.ExactCorrection

lemma positive_power_threshold (c p b : ℝ) (hp : 0 < p) (hb : 0 < b) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ t : ℝ, 0 < t → t < ε → c*t^p < b := by
  have hf : ContinuousAt (fun t : ℝ => c*t^p) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const 0 p (Or.inr hp.le))
  have he : ∀ᶠ t in 𝓝 (0 : ℝ), c*t^p < b :=
    hf.eventually (gt_mem_nhds (by simpa only [Real.zero_rpow hp.ne',mul_zero] using hb))
  obtain ⟨ε,hε,heε⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨min ε 1,lt_min hε zero_lt_one,min_le_right _ _,?_⟩
  intro t ht hsmall
  apply heε
  simpa only [Real.dist_eq,sub_zero,abs_of_pos ht] using hsmall.trans_le (min_le_left ε 1)

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ShiftedScaleGain
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inherited derivatives gain a scale ratio above the fixed prefix. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Reducing the scale preserves the unweighted prefix and contracts all
higher weighted derivatives by at least `τ/t`. -/
theorem ShiftedBound.shrink_with_prefix {q m : ℕ} {t τ A C : ℝ} {f : Base → V}
    (hb : ShiftedBound q 0 t A f) (hc : ShiftedBound q m t C f)
    (ht : 0 < t) (hτ : 0 ≤ τ) (hτt : τ ≤ t) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ShiftedBound q m τ (A + (τ / t) * C) f := by
  intro j hj x
  by_cases hjq : j ≤ q
  · have h := hb j (by omega) x
    simp only [Nat.sub_eq_zero_of_le hjq, pow_zero, one_mul] at h ⊢
    exact h.trans (le_add_of_nonneg_right (mul_nonneg (div_nonneg hτ ht.le) hC))
  · have hp : (τ / t) ^ (j - q) ≤ τ / t := by
      simpa only [pow_one] using pow_le_pow_of_le_one (div_nonneg hτ ht.le)
        ((div_le_one ht).mpr hτt) (show 1 ≤ j - q by omega)
    calc
      _ ≤ τ ^ (j - q) * (C / t ^ (j - q)) :=
        mul_le_mul_of_nonneg_left (hc.deriv_le ht hj x) (pow_nonneg hτ _)
      _ = (τ / t) ^ (j - q) * C := by rw [div_pow]; ring
      _ ≤ (τ / t) * C := mul_le_mul_of_nonneg_right hp hC
      _ ≤ _ := le_add_of_nonneg_left hA

/-- Adding the actual increment adds its shifted derivative budget. -/
theorem ShiftedBound.add {q m : ℕ} {s A B : ℝ} {f g : Base → V}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hs : 0 ≤ s)
    (hb : ShiftedBound q m s A f) (hc : ShiftedBound q m s B g) :
    ShiftedBound q m s (A + B) (f + g) := by
  intro j hj x
  rw [iteratedFDeriv_add_apply (hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt
    (hg.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt]
  calc
    _ ≤ s ^ (j - q) * (‖iteratedFDeriv ℝ j f x‖ + ‖iteratedFDeriv ℝ j g x‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (pow_nonneg hs _)
    _ = s ^ (j - q) * ‖iteratedFDeriv ℝ j f x‖ +
        s ^ (j - q) * ‖iteratedFDeriv ℝ j g x‖ := by ring
    _ ≤ _ := add_le_add (hb j hj x) (hc j hj x)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_GlobalScaleGain
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inherited-map part of the all-order correction recurrence. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
/-- Shrinking the scale gains one ratio in every positive weighted order. -/
theorem shifted_shrink_with_prefix {q m : ℕ} {t τ P C : ℝ} {f : M → V}
    (hb : A.ShiftedBound q 0 t P f) (hc : A.ShiftedBound q m t C f)
    (ht : 0 < t) (hτ : 0 ≤ τ) (hτt : τ ≤ t) (hP : 0 ≤ P) (hC : 0 ≤ C) :
    A.ShiftedBound q m τ (P + (τ / t) * C) f :=
  fun i => (hb i).shrink_with_prefix (hc i) ht hτ hτt hP hC

/-- The new map keeps the old low-derivative baseline; its inherited high
orders contract, and the actual increment contributes its own budget. -/
theorem shifted_map_recurrence {q m : ℕ} {t τ P C D : ℝ} {f u : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ, V) ∞ f)
    (hu : ContMDiff planeModel 𝓘(ℝ, V) ∞ u)
    (hb : A.ShiftedBound q 0 t P f) (hc : A.ShiftedBound q m t C f)
    (hd : A.ShiftedBound q m τ D u)
    (ht : 0 < t) (hτ : 0 ≤ τ) (hτt : τ ≤ t) (hP : 0 ≤ P) (hC : 0 ≤ C) :
    A.ShiftedBound q m τ (P + (τ / t) * C + D) (f + u) := by
  have hsh := A.shifted_shrink_with_prefix hb hc ht hτ hτt hP hC
  intro i
  rw [localize_add]
  exact (hsh i).add
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hf)
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hu) hτ (hd i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_GlobalInputRecurrence
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both components of the actual next input admit a common recurrence bound. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates JetPolynomial
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma shiftedBound_of_weighted {f : Base → V} {s C : ℝ} {q m : ℕ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hb : WeightedEstimates.WeightedBound univ s (q+m) C f) :
    ShiftedBound q m s (C/s^q) f := by
  intro j hj x
  have hh := hb.deriv_le hs hj (mem_univ x)
  rw [iteratedFDerivWithin_univ] at hh
  by_cases hq : q ≤ j
  · have he : s^j = s^(j-q)*s^q := by rw [← pow_add,Nat.sub_add_cancel hq]
    calc
      _ ≤ s^(j-q)*(C/s^j) := mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
      _ = _ := by rw [he]; field_simp
  · have hjq : j ≤ q := by omega
    simp only [Nat.sub_eq_zero_of_le hjq,pow_zero,one_mul]
    exact hh.trans (div_le_div_of_nonneg_left hC (pow_pos hs _)
      (pow_le_pow_of_le_one hs.le hs1 hjq))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputRecurrenceFiberSpace
omit [CompactSpace M] in
lemma weighted_to_shifted {F : M → V} {s C : ℝ} {q m : ℕ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hb : A.WeightedBound s (q+m) C F) : A.ShiftedBound q m s (C/s^q) F :=
  fun i => shiftedBound_of_weighted hs hs1 hC (hb i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_AtlasPrimitiveUpdate
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Propagation of the actual slow-map norms and normalized polynomial
error through one primitive increment. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma weighted_increment_unscaled {X : M → Space} {τ C : ℝ} {m : ℕ}
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hC : 0 ≤ C)
    (hX : A.WeightedBound τ m C X) : A.WeightedBound 1 m (C/τ^m) X := by
  intro i j hj x hx
  simp only [one_pow,one_mul]
  exact ((hX i).deriv_le hτ hj hx).trans
    (div_le_div_of_nonneg_left hC (pow_pos hτ _)
      (pow_le_pow_of_le_one hτ.le hτ1 hj))

/-- The output bounds concern the map that is actually added, and the
normalized defect of its actual polynomial metric. -/
theorem polynomial_increment_propagation {n : A.centers → ℕ}
    {Pol : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression}
    (hPol : ∀ i k l, (Pol i k l).SmoothCoeffs univ)
    {γ : ∀ x : M, CovariantTwoTensor x}
    (hγ : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (γ x)))
    {F G X : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    (hG : ContMDiff planeModel spaceModel ∞ G) (hX : ContMDiff planeModel spaceModel ∞ X)
    {s τ δ δ' ε c : ℝ} (hs : 0 < s) (hτ : 0 < τ) (hτs : τ ≤ s) (hτ1 : τ ≤ 1)
    (hδ : 0 < δ) (hδ' : 0 < δ')
    (P B E : ℕ → ℝ) (hP : ∀ m, 0 ≤ P m) (hB : ∀ m, 0 ≤ B m)
    (hclose : A.WeightedBound 1 2 c (G-F))
    (hmap : ∀ m, A.ShiftedBound 2 m s (P m) G)
    (hinc : ∀ m, A.WeightedBound τ m (B m*(δ*τ)) X)
    (herr : ∀ m, A.TensorWeightedBound τ m (E m)
      (A.atlasPolynomialMetric Pol ε (G+X)-A.atlasPolynomialMetric Pol ε G-
        δ^2 • A.polynomialMeanTarget Pol ε δ δ' γ G)) :
    A.WeightedBound 1 2 (c+B 2*δ/τ) (G+X-F) ∧
    (∀ m, A.ShiftedBound 2 m τ (P 0+P m+B (2+m)*δ/τ) (G+X)) ∧
    (∀ m, A.TensorWeightedBound τ m (E m/δ'^2)
      (A.normalizedPolynomialDefect Pol ε δ' γ (G+X))) := by
  have htC (m : ℕ) : 0 ≤ B m*(δ*τ) := mul_nonneg (hB m) (mul_nonneg hδ.le hτ.le)
  have hcX := A.weighted_increment_unscaled hτ hτ1 (htC 2) (hinc 2)
  have hcX' : A.WeightedBound 1 2 (B 2*δ/τ) X := by
    convert hcX using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
  have hc := A.weightedBound_add (hG.sub hF) hX zero_le_one hclose hcX'
  have heq : G+X-F = (G-F)+X := by abel
  rw [heq]
  refine ⟨hc,?_,?_⟩
  · intro m
    have hx := A.weighted_to_shifted hτ hτ1 (htC (2+m)) (hinc (2+m))
    have hx' : A.ShiftedBound 2 m τ (B (2+m)*δ/τ) X := by
      convert hx using 1
      all_goals try with_reducible_and_instances rfl
      field_simp
    have hm := A.shifted_map_recurrence hG hX (hmap 0) (hmap m) hx'
      hs hτ.le hτs (hP 0) (hP m)
    intro i j hj x
    exact (hm i j hj x).trans (by
      have hr : τ/s ≤ 1 := (div_le_one hs).2 hτs
      have hh := mul_le_of_le_one_left (hP m) hr
      linarith)
  · intro m
    exact A.normalizedPolynomialDefect_after_step hPol hδ.ne' hδ'.ne'
      hγ hG (hG.add hX) (herr m)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveSlowErrorProfiles
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform all-order power profiles for the two primitive error terms. -/
noncomputable section
namespace ClosedSurfaceR4.PrimitiveRealization

lemma normalized_slow_error_profile {z d d' b κ a η C : ℝ} {q : ℕ}
    (hz : 0 < z) (hz1 : z ≤ 1) (hC : 0 ≤ C) (hη : 0 ≤ η)
    (hηb : η ≤ 2*z^κ)
    (ha : a ≤ d+κ*q-2*d') (hb : a ≤ 3*d-b-2*d') :
    (C*(z^d*η^q+(z^d)^3/z^b))/(z^d')^2 ≤ C*(2^q+1)*z^a := by
  have hpa : z^d*(z^κ)^q/(z^d')^2 = z^(d+κ*q-2*d') := by
    simpa only [Real.rpow_zero,div_one,Real.rpow_natCast,sub_zero] using
      ExactCorrection.scale_ratio_power hz d κ 0 (q : ℝ) d'
  have hpb := ExactCorrection.scale_cubic_quotient hz d b d'
  calc
    _ ≤ (C*(z^d*(2*z^κ)^q+(z^d)^3/z^b))/(z^d')^2 := by gcongr
    _ = C*2^q*z^(d+κ*q-2*d')+C*z^(3*d-b-2*d') := by
      rw [mul_pow]
      calc
        _ = (C*2^q)*(z^d*(z^κ)^q/(z^d')^2)+C*(((z^d)^3/z^b)/(z^d')^2) := by ring
        _ = _ := by rw [hpa,hpb]
    _ ≤ C*2^q*z^a+C*z^a := add_le_add
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hz hz1 ha)
        (mul_nonneg hC (pow_nonneg (by norm_num) _)))
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hz hz1 hb) hC)
    _ = _ := by ring

lemma slow_parameter_bound_of_exponents {z b b' : ℝ} {loss : ℕ}
    (hz : 0 < z) (hz1 : z ≤ 1) :
    z^b'/z^b+z/(z^b')^loss ≤ 2*z^(min (b'-b) (1-b'*loss)) := by
  have hfirst : z^b'/z^b = z^(b'-b) := (Real.rpow_sub hz _ _).symm
  have hsecond : z/(z^b')^loss = z^(1-b'*(loss : ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hz.le,Real.rpow_sub hz,Real.rpow_one]
  rw [hfirst,hsecond]
  have h₁ := Real.rpow_le_rpow_of_exponent_ge hz hz1
    (min_le_left (b'-b) (1-b'*loss))
  have h₂ := Real.rpow_le_rpow_of_exponent_ge hz hz1
    (min_le_right (b'-b) (1-b'*loss))
  linarith

end ClosedSurfaceR4.PrimitiveRealization

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_MetricPolynomialSlowStep
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One uniform step of the finite slow-map construction. The derivative
profiles and the small parameter threshold precede the nearby map. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation WeightedEstimates PrimitiveRealization
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.slowPolynomialFiberNormed
local instance slowPolynomialFiberSpace_rab5283_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance slowPolynomialDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
namespace MetricGoodPhaseData
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.slowPolynomialFiberNormed
local instance slowPolynomialFiberSpace_rab5283_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance slowPolynomialDualSmul_rab5283_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {g : SmoothMetric M} {F : M → Space}

local instance slowPolynomialSectionNormed_rab5283_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance slowPolynomialSectionSpace_rab5283_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- An actual primitive update improves the amplitude exponent and retains
uniform all-order profiles. The fixed loss is chosen before every scale. -/
theorem polynomial_slow_step_oai (data : MetricGoodPhaseData g F)
    {n : data.A.centers → ℕ}
    (Pol : ∀ i : data.A.centers, Fin 3 → Fin (n i) → Expression)
    (hPol : ∀ i k l, (Pol i k l).SmoothCoeffs univ)
    (hF : ContMDiff planeModel spaceModel ∞ F) :
    ∃ loss : ℕ, ∀ (b b' d d' a u : ℝ), 0 ≤ b → b < b' → b'*(loss : ℝ) < 1 →
      2*b' < d → d < d' → 2*d' < 3*d-b' → 0 < a → 0 < u →
    ∀ (P D : ℕ → ℝ) (L : ℝ), (∀ m, 0 ≤ P m) → (∀ m, 0 ≤ D m) → 0 ≤ L →
      (∀ m, data.A.ShiftedBound 2 m 1 (P m) F) →
    ∃ (a' η L' : ℝ) (P' D' : ℕ → ℝ), 0 < a' ∧ 0 < η ∧ η ≤ 1 ∧ 0 ≤ L' ∧
      (∀ m, 0 ≤ P' m) ∧ (∀ m, 0 ≤ D' m) ∧
    ∀ z : ℝ, 0 < z → z < η → ∀ G : M → Space,
      ContMDiff planeModel spaceModel ∞ G →
      data.A.WeightedBound 1 3 (L*z^u) (G-F) →
      (∀ m, data.A.ShiftedBound 2 m (z^b) (P m) G) →
      (∀ m, data.A.TensorWeightedBound (z^b) m (D m*z^a)
        (data.A.normalizedPolynomialDefect Pol z (z^d) g.inner G)) →
      ∃ G' : M → Space, ContMDiff planeModel spaceModel ∞ G' ∧
        data.A.WeightedBound 1 3 (L'*z^(min u (d-2*b'))) (G'-F) ∧
        (∀ m, data.A.ShiftedBound 2 m (z^b') (P' m) G') ∧
        (∀ m, data.A.TensorWeightedBound (z^b') m (D' m*z^a')
          (data.A.normalizedPolynomialDefect Pol z (z^d') g.inner G')) := by
  classical
  obtain ⟨loss,hstep⟩ := data.polynomial_small_increment Pol hPol hF
  refine ⟨loss,?_⟩
  intro b b' d d' a u hb hbb hloss hbd2 hdd hcubic ha hu P D L hP hD hL hPF
  have hbd : b' < d := by linarith
  let κ : ℝ := min (b'-b) (1-b'*(loss : ℝ))
  have hκ : 0 < κ := lt_min (sub_pos.mpr hbb) (sub_pos.mpr hloss)
  obtain ⟨q,hq⟩ := exists_nat_gt ((2*d'-d)/κ)
  have hlinear : 0 < d+κ*(q+1)-2*d' := by
    have hh := (div_lt_iff₀ hκ).mp hq
    nlinarith
  let a' := min (d+κ*(q+1)-2*d') (3*d-b'-2*d')
  have ha' : 0 < a' := lt_min hlinear (by linarith)
  choose K hK hKg using fun m => data.A.exists_bundle_bound data.A.tensorTriv
    data.A.tensorTriv_domain m g.contMDiff
  let C : ℕ → ℝ := fun m => 1+2*K m+D m
  have hC (m : ℕ) : 1 ≤ C m := by
    dsimp [C]
    linarith [hK m,hD m]
  obtain ⟨r,hr,hprof⟩ := hstep P hP hPF q
  obtain ⟨ρ,η₀,B,T,hρ,hη₀,hη₀1,hB,hT,hsolve⟩ := hprof C hC
  obtain ⟨η₁,hη₁,_,h₁⟩ := ExactCorrection.positive_power_threshold L u ρ hu hρ
  obtain ⟨η₂,hη₂,_,h₂⟩ := ExactCorrection.positive_power_threshold (D 0) a (r/4) ha (by positivity)
  obtain ⟨η₃,hη₃,_,h₃⟩ := ExactCorrection.positive_power_threshold (K 0) (2*d'-2*d)
    (r/4) (by linarith) (by positivity)
  obtain ⟨η₄,hη₄,_,h₄⟩ := ExactCorrection.positive_power_threshold 2 κ η₀ hκ hη₀
  let η := min 1 (min η₁ (min η₂ (min η₃ η₄)))
  have hη : 0 < η := lt_min zero_lt_one (lt_min hη₁ (lt_min hη₂ (lt_min hη₃ hη₄)))
  let P' : ℕ → ℝ := fun m => P 0+P m+B (2+m)
  let D' : ℕ → ℝ := fun m => T m*(2^(q+1)+1)
  refine ⟨a',η,L+B 3,P',D',ha',hη,min_le_left _ _,add_nonneg hL (hB 3),
    fun m => add_nonneg (add_nonneg (hP 0) (hP m)) (hB (2+m)),
    fun m => mul_nonneg (hT m) (by positivity),?_⟩
  intro z hz hzη G hG hclose hmap hdefect
  have hclose2 : data.A.WeightedBound 1 2 (L*z^u) (G-F) :=
    fun i => (hclose i).mono_order (by omega)
  have hz1 : z ≤ 1 := hzη.le.trans (min_le_left _ _)
  have hzη₁ : z < η₁ := hzη.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hzη₂ : z < η₂ := hzη.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hzη₃ : z < η₃ := hzη.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hzη₄ : z < η₄ := hzη.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hs : 0 < z^b := Real.rpow_pos_of_pos hz _
  have hτ : 0 < z^b' := Real.rpow_pos_of_pos hz _
  have hδ : 0 < z^d := Real.rpow_pos_of_pos hz _
  have hδ' : 0 < z^d' := Real.rpow_pos_of_pos hz _
  have hs1 : z^b ≤ 1 := Real.rpow_le_one hz.le hz1 hb
  have hτs : z^b' ≤ z^b := Real.rpow_le_rpow_of_exponent_ge hz hz1 hbb.le
  have hτ1 : z^b' ≤ 1 := hτs.trans hs1
  have hδτ : z^d ≤ z^b' := Real.rpow_le_rpow_of_exponent_ge hz hz1 hbd.le
  have hδδ : z^d' ≤ z^d := Real.rpow_le_rpow_of_exponent_ge hz hz1 hdd.le
  have hza : z^a ≤ 1 := Real.rpow_le_one hz.le hz1 ha.le
  let H := data.A.polynomialMeanTarget Pol z (z^d) (z^d') g.inner G
  have hH := data.A.polynomialMeanTarget_smooth (ε := z) (δ := z^d) (δ' := z^d') hPol g.contMDiff hG
  have hHs : ∀ x v w, H x v w = H x w v := by
    intro x v w
    change ((z^d)^2)⁻¹*(g.inner x v w-data.A.atlasPolynomialMetric Pol z G x v w-
      (z^d')^2*g.inner x v w) =
      ((z^d)^2)⁻¹*(g.inner x w v-data.A.atlasPolynomialMetric Pol z G x w v-
        (z^d')^2*g.inner x w v)
    rw [g.symm x v w,data.A.atlasPolynomialMetric_symmetric Pol z G x v w]
  have hHbound (m : ℕ) : data.A.TensorWeightedBound (z^b) m (C m) H := by
    have hbase : data.A.TensorWeightedBound (z^b) m (K m) g.inner :=
      fun i => (hKg m i).shrink_scale hs.le hs1
    have hd := data.A.polynomialMeanTarget_bound hPol hδ hδ'.le hδδ hs.le (hK m)
      g.contMDiff hG hbase (hdefect m)
    intro i
    apply (hd i).mono_const
    dsimp [C]
    have hh := mul_le_of_le_one_right (hD m) hza
    linarith
  have hratio : (z^d')^2/(z^d)^2 = z^(2*d'-2*d) := by
    rw [← Real.rpow_mul_natCast hz.le,← Real.rpow_mul_natCast hz.le,← Real.rpow_sub hz]
    congr 1
    ring
  have hHnear (x : JetPolynomial.Base) :
      ‖data.A.tensorEncode H x-data.A.tensorEncode g.inner x‖ ≤ r/2 := by
    have hnorm := (data.A.tensorEncode_bound
      (data.A.normalizedPolynomialDefect_smooth (ε := z) (δ := z^d) hPol g.contMDiff hG)
      hs (mul_nonneg (hD 0) (Real.rpow_nonneg hz.le _)) (hdefect 0)).norm_le (mem_univ x)
    have hnormg := (data.A.tensorEncode_bound g.contMDiff zero_lt_one (hK 0) (hKg 0)).norm_le (mem_univ x)
    have hh := data.A.polynomialMeanTarget_distance Pol z (z^d) (z^d') g.inner G x hnorm hnormg
    rw [hratio] at hh
    dsimp [H]
    exact hh.trans (by
      have hd := h₂ z hz hzη₂
      have hg := h₃ z hz hzη₃
      nlinarith)
  let ratio := z^b'/z^b+z/(z^b')^loss
  have hratio0 : 0 ≤ ratio := add_nonneg (div_nonneg hτ.le hs.le)
    (div_nonneg hz.le (pow_nonneg hτ.le _))
  have hratioB : ratio ≤ 2*z^κ := slow_parameter_bound_of_exponents hz hz1
  have hratioη : ratio ≤ η₀ := hratioB.trans (h₄ z hz hzη₄).le
  obtain ⟨X,hX,hXb,hXe⟩ := hsolve G hG (L*z^u)
    (mul_nonneg hL (Real.rpow_nonneg hz.le _)) (h₁ z hz hzη₁) hclose2
    ⟨z^b,hs.le⟩ hs hs1 hmap H hH hHs hHnear hHbound
    (z^b') (z^d) z hτ hτs hz.le hz1 hratioη hδ hδτ
  have hprop := data.A.polynomial_increment_propagation hPol g.contMDiff hF hG hX
    hs hτ hτs hτ1 hδ hδ' P B
    (fun m => T m*(z^d*ratio^(q+1)+(z^d)^3/z^b')) hP hB hclose2 hmap hXb hXe
  have hX3 := data.A.weighted_increment_unscaled hτ hτ1
    (mul_nonneg (hB 3) (mul_nonneg hδ.le hτ.le)) (hXb 3)
  have hX3' : data.A.WeightedBound 1 3 (B 3*z^(d-2*b')) X := by
    have heq : B 3*(z^d*z^b')/(z^b')^3 = B 3*z^(d-2*b') := by
      rw [← Real.rpow_mul_natCast hz.le,← Real.rpow_add hz, mul_div_assoc,← Real.rpow_sub hz]
      congr 2
      ring
    simpa only [heq] using hX3
  have hclose3 := data.A.weightedBound_add (hG.sub hF) hX zero_le_one hclose hX3'
  change data.A.WeightedBound 1 3 (L*z^u+B 3*z^(d-2*b')) ((G-F)+X) at hclose3
  have hadd : (G-F)+X = G+X-F := by abel
  rw [hadd] at hclose3
  refine ⟨G+X,hG.add hX,?_,?_,?_⟩
  · intro i
    apply (hclose3 i).mono_const
    have hu' := Real.rpow_le_rpow_of_exponent_ge hz hz1 (min_le_left u (d-2*b'))
    have hd' := Real.rpow_le_rpow_of_exponent_ge hz hz1 (min_le_right u (d-2*b'))
    exact (add_le_add (mul_le_mul_of_nonneg_left hu' hL)
      (mul_le_mul_of_nonneg_left hd' (hB 3))).trans_eq (by ring)
  · intro m i j hj x
    apply (hprop.2.1 m i j hj x).trans
    change P 0+P m+B (2+m)*z^d/z^b' ≤ P 0+P m+B (2+m)
    rw [mul_div_assoc,← Real.rpow_sub hz]
    have hh := Real.rpow_le_one hz.le hz1 (sub_nonneg.mpr hbd.le)
    linarith [mul_le_of_le_one_right (hB (2+m)) hh]
  · intro m i
    apply (hprop.2.2 m i).mono_const
    exact normalized_slow_error_profile hz hz1 (hT m) hratio0 hratioB
      (by simpa only [Nat.cast_add,Nat.cast_one] using
        (min_le_left (d+κ*(q+1)-2*d') (3*d-b'-2*d')))
      (min_le_right _ _)

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.polynomial_slow_step_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.polynomial_slow_step_oai.{u_1}
