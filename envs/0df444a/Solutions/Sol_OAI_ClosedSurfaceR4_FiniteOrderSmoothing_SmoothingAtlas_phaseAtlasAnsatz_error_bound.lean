-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseAtlasAnsatz_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:42:56.616577+00:00
-- url     : https://prove2.me/submissions/b05f7b89-1f9c-4641-ae59-e0a95f47ff29

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
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_phaseAtlasAnsatz_defect

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalIsometryBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Isometric coordinate transport on the open domains used by the local
polynomial estimates. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma weightedBound_comp_isometry_on {A B F : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : A ≃ₗᵢ[ℝ] B) {U : Set B} (hU : IsOpen U) {f : B → F}
    (hf : ContDiff ℝ ∞ f) {s C : ℝ} {m : ℕ}
    (hb : WeightedBound U s m C f) :
    WeightedBound (e ⁻¹' U) s m C (f ∘ e) := by
  intro j hj x hx
  rw [iteratedFDerivWithin_of_isOpen j (hU.preimage e.continuous) hx]
  change s ^ j * ‖iteratedFDeriv ℝ j
    (f ∘ (e.toContinuousLinearEquiv.toContinuousLinearMap : A → B)) x‖ ≤ C
  rw [e.toContinuousLinearEquiv.toContinuousLinearMap.iteratedFDeriv_comp_right hf x (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top),
    ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv]
  change s ^ j * ‖iteratedFDeriv ℝ j f (e x)‖ ≤ C
  have hh := hb j hj (e x) hx
  rw [iteratedFDerivWithin_of_isOpen j hU hx] at hh
  exact hh

end ClosedSurfaceR4.JetPolynomial

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

variable [CompactSpace M]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.planeReadSectionNormed
local instance planeReadSectionSpace_rd8bcb4_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorPlaneRestore_bound (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : A.centers → SmallModes.Base → Tensor) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → (∀ i, ContDiff ℝ ∞ (f i)) →
      (∀ i, _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m C (f i)) →
      A.TensorWeightedBound s m (D*C) (A.tensorPlaneRestore f) := by
  obtain ⟨D,hD,hd⟩ := A.bundle_restoration_bound A.tensorTriv A.tensorTriv_domain m
  refine ⟨D * ‖fiberFromThree‖, mul_nonneg hD (norm_nonneg _), ?_⟩
  intro f s C hs hs1 hC hf hb
  have hh := hd (fun i y => fiberFromThree (f i (planeCoordinateIsometry y))) s
    (‖fiberFromThree‖ * C) hs hs1 (mul_nonneg (norm_nonneg _) hC)
    (fun i => fiberFromThree.contDiff.comp ((hf i).comp planeCoordinateIsometry.contDiff))
    (fun i => (weightedBound_comp_isometry planeCoordinateIsometry (hf i) (hb i)).linear
      uniqueDiffOn_univ hs.le ((hf i).comp planeCoordinateIsometry.contDiff).contDiffOn fiberFromThree)
  have hout : A.TensorWeightedBound s m (D * (‖fiberFromThree‖ * C))
      (A.tensorPlaneRestore f) := hh
  convert hout using 1
  all_goals try with_reducible_and_instances rfl
  ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialAlgebra
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite polynomials in actual coordinate jets, with coefficients smooth in
position, the second jet, and the periodic variable. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial

namespace Expression

lemma smoothCoeffs_map {O : Set LowJet} (e : Expression) (f)
    (hf : ∀ c, ContDiffOn ℝ ∞ c (O ×ˢ Set.univ) → ContDiffOn ℝ ∞ (f c) (O ×ˢ Set.univ))
    (he : e.SmoothCoeffs O) : (e.mapCoeff f).SmoothCoeffs O := by
  induction e with
  | coeff c => exact hf c he
  | atom w a e ih => exact ih he
  | add e g ihe ihg => exact ⟨ihe he.1, ihg he.2⟩

lemma smoothCoeffs_mul {O : Set LowJet} {e f : Expression}
    (he : e.SmoothCoeffs O) (hf : f.SmoothCoeffs O) : (e.mul f).SmoothCoeffs O := by
  induction e with
  | coeff c => exact smoothCoeffs_map f _ (fun d hd => he.mul hd) hf
  | atom w a e ih => exact ih he
  | add e g ihe ihg => exact ⟨ihe he.1, ihg he.2⟩

end Expression
end ClosedSurfaceR4.JetPolynomial

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
local instance metricBoundSectionNormed_rd8bcb4_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricBoundSectionSpace_rd8bcb4_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_LowJetCoordinateChange
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact order-two jet transport under a fixed smooth coordinate map.
The new position is supplied separately, so no inverse coordinate map is
required and the construction applies to arbitrary smooth maps. -/
noncomputable section
open Set
open scoped ContDiff BigOperators Topology

namespace ClosedSurfaceR4.JetPolynomial

lemma coordinatePartial_smooth {f : Base → ℝ} (hf : ContDiff ℝ ∞ f) (v : Fin 2) :
    ContDiff ℝ ∞ (coordinatePartial f v) :=
  (hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const

lemma coordinateChangeFirst_smooth {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    (v : Fin 2) (a : Fin 4) :
    ContDiff ℝ ∞ (fun p : Base × LowJet => coordinateChangeFirst T p.1 p.2 v a) := by
  apply ContDiff.sum
  intro i _
  exact ((coordinatePartial_smooth (contDiff_pi.mp hT i) v).comp contDiff_fst).mul
    ((ContinuousLinearMap.proj (.inr (firstJetSlot i,a)) : LowJet →L[ℝ] ℝ).contDiff.comp contDiff_snd)

lemma coordinateChangeSecond_smooth {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    (v w : Fin 2) (a : Fin 4) :
    ContDiff ℝ ∞ (fun p : Base × LowJet => coordinateChangeSecond T p.1 p.2 v w a) := by
  apply ContDiff.sum
  intro i _
  apply ContDiff.add
  · apply ContDiff.mul
    · exact (coordinatePartial_smooth (contDiff_pi.mp hT i) w).comp contDiff_fst
    · apply ContDiff.sum
      intro j _
      exact ((coordinatePartial_smooth (contDiff_pi.mp hT j) v).comp contDiff_fst).mul
        ((ContinuousLinearMap.proj (.inr (secondJetSlot j i,a)) : LowJet →L[ℝ] ℝ).contDiff.comp
          contDiff_snd)
  · exact ((coordinatePartial_smooth
      (coordinatePartial_smooth (contDiff_pi.mp hT i) w) v).comp contDiff_fst).mul
      ((ContinuousLinearMap.proj (.inr (firstJetSlot i,a)) : LowJet →L[ℝ] ℝ).contDiff.comp contDiff_snd)

lemma lowJetCoordinateChange_smooth {T : Base → Base} (hT : ContDiff ℝ ∞ T) :
    ContDiff ℝ ∞ (lowJetCoordinateChange T) := by
  apply contDiff_pi.mpr
  intro i
  cases i with
  | inl i =>
    exact (ContinuousLinearMap.proj i : Base →L[ℝ] ℝ).contDiff.comp
      (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : Base × LowJet → Base))
  | inr i =>
    rcases i with ⟨w,a⟩
    fin_cases w
    · exact (ContinuousLinearMap.proj (.inr (0,a)) : LowJet →L[ℝ] ℝ).contDiff.comp
        (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : Base × LowJet → LowJet))
    · exact coordinateChangeFirst_smooth hT 0 a
    · exact coordinateChangeFirst_smooth hT 1 a
    · exact coordinateChangeSecond_smooth hT 0 0 a
    · exact coordinateChangeSecond_smooth hT 0 1 a
    · exact coordinateChangeSecond_smooth hT 1 0 a
    · exact coordinateChangeSecond_smooth hT 1 1 a

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialDerivative
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiation preserves finite polynomial dependence on higher jets.
The proof is for actual derivatives, including the low-jet chain rule. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open SmoothPeriodicCalculus

namespace Expression

lemma smoothCoeffs_sumList {ι : Type*} {O : Set LowJet} (l : List ι) (f : ι → Expression)
    (hf : ∀ i ∈ l, (f i).SmoothCoeffs O) : (sumList l f).SmoothCoeffs O := by
  induction l with
  | nil => exact contDiffOn_const
  | cons i l ih => exact ⟨hf i (List.mem_cons_self ..),
      ih (fun j hj => hf j (List.mem_cons_of_mem _ hj))⟩

lemma smoothCoeffs_lowFactor (O : Set LowJet) (v : Fin 2) (i : LowIndex) :
    (lowFactor v i).SmoothCoeffs O := by
  cases i with
  | inl i => exact contDiffOn_const
  | inr i => exact contDiffOn_const

lemma smoothCoeffs_slow {O : Set LowJet} (hO : IsOpen O) (v : Fin 2)
    {e : Expression} (he : e.SmoothCoeffs O) : (e.slow v).SmoothCoeffs O := by
  induction e with
  | coeff c =>
    apply smoothCoeffs_sumList
    intro i _
    exact smoothCoeffs_mul (smoothCoeffs_lowFactor O v i)
      (LocalPeriodicCalculus.slow_smooth hO he (lowBasis i))
  | atom w a e ih => exact ⟨he, ih he⟩
  | add e f ihe ihf => exact ⟨ihe he.1, ihf he.2⟩

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_JetPullbackExpressions
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate derivatives in a second chart, expressed by finite jet
polynomials in the first chart. Only the surface and four-space dimensions
used in the primitive construction are considered. -/
noncomputable section
open Set
open scoped ContDiff BigOperators Topology
namespace ClosedSurfaceR4.JetPolynomial

lemma inverseCoordinateCoefficient_smooth {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S) (i k : Fin 2) :
    ContDiff ℝ ∞ (inverseCoordinateCoefficient T S i k) := by
  have hs : ContDiff ℝ ∞ (fun x => (fderiv ℝ S x (coordinateVector i)) k) :=
    contDiff_pi.mp ((hS.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const) k
  exact hs.comp (hT.comp (lowPosition.contDiff.comp contDiff_fst))

lemma jetPullback_smooth {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S) (w : List (Fin 2)) (a : Fin 4) :
    (jetPullback T S w a).SmoothCoeffs univ := by
  induction w with
  | nil =>
    change ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => z.1 (.inr (0,a))) (univ ×ˢ univ)
    exact ((ContinuousLinearMap.proj (.inr (0,a)) : LowJet →L[ℝ] ℝ).contDiff.comp
      (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : LowJet × ℝ → LowJet))).contDiffOn
  | cons i w ih =>
    apply Expression.smoothCoeffs_sumList
    intro k _
    exact Expression.smoothCoeffs_mul (inverseCoordinateCoefficient_smooth hT hS i k).contDiffOn
      (Expression.smoothCoeffs_slow isOpen_univ k ih)


namespace Expression

lemma coordinatePullback_smooth {T S : Base → Base} {K : LowJet → LowJet}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S) (hK : ContDiff ℝ ∞ K)
    {e : Expression} (he : e.SmoothCoeffs univ) :
    (e.coordinatePullback T S K).SmoothCoeffs univ := by
  induction e with
  | coeff c =>
    have hc : ContDiff ℝ ∞ c := contDiffOn_univ.mp (by simpa only [SmoothCoeffs,univ_prod_univ] using he)
    exact (hc.comp ((hK.comp contDiff_fst).prodMk contDiff_snd)).contDiffOn
  | atom w a e ih => exact smoothCoeffs_mul (jetPullback_smooth hT hS w a) (ih he)
  | add e f ihe ihf => exact ⟨ihe he.1,ihf he.2⟩

end Expression

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CoordinatePolynomialPullback
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate pullback of a finite jet polynomial, with the low-jet
substitution and inverse differential proved from the actual local inverse.
No compatibility of the polynomial values is assumed. -/
noncomputable section
open Set
open scoped ContDiff Topology

namespace ClosedSurfaceR4.JetPolynomial

lemma coordinateLowJetSubstitution_smooth {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S) :
    ContDiff ℝ ∞ (coordinateLowJetSubstitution T S) :=
  (lowJetCoordinateChange_smooth hS).comp
    ((hT.comp lowPosition.contDiff).prodMk contDiff_id)

namespace Expression

lemma localCoordinatePullback_smooth {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S)
    {e : Expression} (he : e.SmoothCoeffs univ) :
    (e.localCoordinatePullback T S).SmoothCoeffs univ :=
  coordinatePullback_smooth hT hS (coordinateLowJetSubstitution_smooth hT hS) he

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialScalar
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar polynomial representations of the finite metric coefficients. -/
noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Expression
open LocalPeriodicExpansion CovarianceCorrector

lemma smoothCoeffs_sumFinset {ι : Type*} {O : Set LowJet} (a : Finset ι) (e : ι → Expression)
    (he : ∀ i ∈ a, (e i).SmoothCoeffs O) : (sumFinset a e).SmoothCoeffs O := by
  apply smoothCoeffs_sumList
  intro i hi
  exact he i (Finset.mem_toList.mp hi)

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CoordinateTensorPullback
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pullback of finite tensor expressions under fixed coordinate changes.
The Jacobian factors, coefficient substitution, and higher jet atoms are
all constructed, so the evaluation identity assumes no tensor covariance. -/
noncomputable section
open Set
open scoped ContDiff BigOperators Matrix Topology

namespace ClosedSurfaceR4.JetPolynomial

lemma tensorCoordinateJacobian_smooth {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    (k l : Fin 3) : ContDiff ℝ ∞ (tensorCoordinateJacobian T k l) := by
  have hd (v : Base) (a : Fin 2) : ContDiff ℝ ∞ (fun x => fderiv ℝ T x v a) :=
    contDiff_pi.mp ((hT.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const) a
  fin_cases l
  · exact (hd _ 0).mul (hd _ 0)
  · exact ((hd _ 0).mul (hd _ 1)).add ((hd _ 1).mul (hd _ 0))
  · exact (hd _ 1).mul (hd _ 1)

lemma tensorCoordinateJacobian_sum (T : Base → Base) (x : Base)
    (A : PhaseMean.Tensor) (k : Fin 3) :
    (∑ l : Fin 3, tensorCoordinateJacobian T k l x * A l) =
      tensorCoordinatePullbackValue T x A k := by
  rw [Fin.sum_univ_three]
  let u := fderiv ℝ T x (planeCoordinateIsometry.symm (PhaseMean.firstDirection k))
  let v := fderiv ℝ T x (planeCoordinateIsometry.symm (PhaseMean.secondDirection k))
  change u 0 * v 0 * A 0 + (u 0 * v 1 + u 1 * v 0) * A 1 + u 1 * v 1 * A 2 =
    A 0 * u 0 * v 0 + A 1 * (u 0 * v 1 + u 1 * v 0) + A 2 * u 1 * v 1
  ring

lemma tensorJacobianCoefficient_smooth {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    (k l : Fin 3) : ContDiff ℝ ∞ (tensorJacobianCoefficient T k l) :=
  (tensorCoordinateJacobian_smooth hT k l).comp (lowPosition.contDiff.comp contDiff_fst)

namespace TensorExpression

lemma coordinatePullback_smooth {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S)
    {E : TensorExpression} (hE : ∀ k, (E k).SmoothCoeffs univ) (k : Fin 3) :
    (coordinatePullback E T S k).SmoothCoeffs univ := by
  apply Expression.smoothCoeffs_sumFinset
  intro l _
  exact Expression.smoothCoeffs_mul (tensorJacobianCoefficient_smooth hT k l).contDiffOn
    (Expression.localCoordinatePullback_smooth hT hS (hE l))

end TensorExpression

namespace Perturbation

lemma tensorPolynomialCoordinatePullback_smooth {n : ℕ}
    {P : Fin 3 → Fin n → Expression} (hP : ∀ k r, (P k r).SmoothCoeffs univ)
    {T S : Base → Base} (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S)
    (k : Fin 3) (r : Fin n) :
    (tensorPolynomialCoordinatePullback P T S k r).SmoothCoeffs univ :=
  TensorExpression.coordinatePullback_smooth hT hS (fun l => hP l r) k

end Perturbation
end ClosedSurfaceR4.JetPolynomial

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

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialMetricFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialMetricFiberSpace
local instance polynomialMetricSectionNormed_rd8bcb4_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialMetricSectionSpace_rd8bcb4_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactLocalBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform slow-scale bounds on a relatively compact coordinate domain. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.WeightedEstimates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem compact_local_weighted_bound {V Ω K : Set E}
    (hV : IsOpen V) (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hVK : V ⊆ K) (hKΩ : K ⊆ Ω) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f Ω) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℝ, 0 ≤ s → s ≤ 1 → WeightedBound V s m C f := by
  obtain ⟨C,hC,hb⟩ := compact_coefficient_bound hΩ.uniqueDiffOn hK hKΩ hf m
  refine ⟨C,hC,?_⟩
  intro s hs hs1 j hj x hx
  rw [iteratedFDerivWithin_of_isOpen j hV hx]
  have hh := hb j hj x (hVK hx)
  rw [iteratedFDerivWithin_of_isOpen j hΩ (hKΩ (hVK hx))] at hh
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hs hs1)).trans hh

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicGlobalization
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactly supported local periodic coefficients extend smoothly by zero. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LocalPeriodicExpansion

open CovarianceCorrector

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma finiteAnsatz_smooth_global {F : A → E} (hF : ContDiff ℝ ∞ F)
    (U : ℕ → Family O E) {K : Set A} (hK : IsClosed K) (hKO : K ⊆ O)
    (hz : ∀ i p, p ∈ O → p ∉ K → (U i).val p = 0)
    (ℓ : A →L[ℝ] ℝ) (L : ℕ) (z : ℝ) :
    ContDiff ℝ ∞ (finiteAnsatz F U ℓ L z) := by
  apply hF.add
  apply ContDiff.sum
  intro i _
  exact contDiff_const.smul (((U i).smooth_global hK hKO (hz i)).comp
    (contDiff_id.prodMk (ℓ.contDiff.div_const z)))

end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CutoffTensorPolynomial
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positional cutoffs of the actual finite tensor polynomial. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

lemma cutoffTensorPolynomial_smooth {n : ℕ} {χ : Base → ℝ}
    (hχ : ContDiff ℝ ∞ χ) {P : Fin 3 → Fin n → Expression}
    (hP : ∀ k r, (P k r).SmoothCoeffs univ) (k : Fin 3) (r : Fin n) :
    (cutoffTensorPolynomial χ P k r).SmoothCoeffs univ :=
  Expression.smoothCoeffs_mul
    ((hχ.comp (lowPosition.contDiff.comp contDiff_fst)).contDiffOn) (hP k r)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorCoordinatePullbackBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed nonlinear coordinate changes preserve weighted tensor error
bounds with a constant independent of the fast scale. -/
noncomputable section
open Set
open scoped ContDiff BigOperators Topology
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma tensorCoordinatePullbackValue_sum (T : Base → Base) (x : Base) :
    tensorCoordinatePullbackValue T x =
      ∑ k : Fin 3, ∑ l : Fin 3,
        tensorCoordinateJacobian T k l x • tensorCoordinateMatrixUnit k l := by
  ext A k
  simp only [sum_apply,smul_apply,
    Finset.sum_apply,Pi.smul_apply,tensorCoordinateMatrixUnit,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply,smul_eq_mul,
    Pi.single_apply]
  simp only [mul_ite,mul_one,mul_zero]
  have hi (j : Fin 3) :
      (∑ l : Fin 3, if k = j then tensorCoordinateJacobian T j l x * A l else 0) =
        if k = j then ∑ l : Fin 3, tensorCoordinateJacobian T j l x * A l else 0 := by
    split_ifs <;> simp_all
  simp_rw [hi]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true, if_true]
  exact (tensorCoordinateJacobian_sum T x A k).symm

lemma tensorCoordinatePullbackValue_smooth {T : Base → Base} (hT : ContDiff ℝ ∞ T) :
    ContDiff ℝ ∞ (tensorCoordinatePullbackValue T) := by
  have he : tensorCoordinatePullbackValue T = fun x =>
      ∑ k : Fin 3, ∑ l : Fin 3,
        tensorCoordinateJacobian T k l x • tensorCoordinateMatrixUnit k l :=
    funext (tensorCoordinatePullbackValue_sum T)
  rw [he]
  apply ContDiff.sum
  intro k _
  apply ContDiff.sum
  intro l _
  exact (tensorCoordinateJacobian_smooth hT k l).smul contDiff_const

theorem fixed_tensor_coordinate_bound {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    {V W : Set Base} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hW : IsOpen W) (hVW : MapsTo T V W) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : Base → PhaseMean.Tensor) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiffOn ℝ ∞ f W →
      WeightedBound W s m C f →
      WeightedBound V s m (D*C) (fun x => tensorCoordinatePullbackValue T x (f (T x))) := by
  obtain ⟨B,hB,hTb⟩ := compact_local_weighted_bound hV isOpen_univ hVc
    subset_closure (subset_univ _) hT.contDiffOn m
  obtain ⟨J,hJ,hJb⟩ := compact_local_weighted_bound hV isOpen_univ hVc
    subset_closure (subset_univ _) (tensorCoordinatePullbackValue_smooth hT).contDiffOn m
  refine ⟨2^m*J*((m.factorial : ℝ)*B^m),by positivity,?_⟩
  intro f s C hs hs1 hC hf hb
  have hc := hb.comp_coordinates hV.uniqueDiffOn hW.uniqueDiffOn hs hs1 hB hC
    hT.contDiffOn hf hVW (fun j _ hj x hx => by
      simpa only [one_pow,one_mul] using hTb 1 zero_le_one le_rfl j hj x hx)
  have hh := (hJb s hs.le hs1).clm_apply hV.uniqueDiffOn hs.le (zero_le_one.trans hJ)
    (by positivity) (tensorCoordinatePullbackValue_smooth hT).contDiffOn
    (hf.comp hT.contDiffOn hVW) hc
  convert hh using 1 <;> first | rfl | ring

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalizedTensorPullbackBound
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The supported tensor pullback has a fixed weighted norm on each finite order. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma localizedTensorPullback_smooth {T : Base → Base} {χ : Base → ℝ}
    {f : Base → PhaseMean.Tensor} (hT : ContDiff ℝ ∞ T) (hχ : ContDiff ℝ ∞ χ)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (localizedTensorPullback T χ f) :=
  hχ.smul ((tensorCoordinatePullbackValue_smooth hT).clm_apply (hf.comp hT))

theorem localized_tensor_pullback_bound {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    {χ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {O W : Set Base} (hO : IsOpen O) (hW : IsOpen W)
    (hχO : tsupport χ ⊆ O) (hTW : MapsTo T O W) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : Base → PhaseMean.Tensor) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f →
      WeightedBound W s m C f →
      WeightedBound univ s m (D*C) (localizedTensorPullback T χ f) := by
  obtain ⟨V,hV,hχV,hVO,hVc⟩ := exists_open_between_and_isCompact_closure hc hO hχO
  have hsub : V ⊆ O := subset_closure.trans hVO
  obtain ⟨D,hD,hd⟩ := fixed_tensor_coordinate_bound hT hV hVc hW (hTW.mono_left hsub) m
  obtain ⟨A,hA,ha⟩ := compact_local_weighted_bound hV isOpen_univ hVc
    subset_closure (subset_univ _) hχ.contDiffOn m
  refine ⟨2^m*A*D,by positivity,?_⟩
  intro f s C hs hs1 hC hf hb
  have hp := (ha s hs.le hs1).smul_real hV.uniqueDiffOn hs.le (zero_le_one.trans hA)
    (mul_nonneg hD hC) hχ.contDiffOn
    (((tensorCoordinatePullbackValue_smooth hT).clm_apply (hf.comp hT)).contDiffOn)
    (hd f s C hs hs1 hC hf.contDiffOn hb)
  have hg := localizedTensorPullback_smooth hT hχ hf
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  by_cases hx : x ∈ V
  · have ht : ContDiffAt ℝ (j : ℕ∞ω) (localizedTensorPullback T χ f) x :=
      (hg.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt
    have hh := hp j hj x hx
    change s^j * ‖iteratedFDerivWithin ℝ j (localizedTensorPullback T χ f) V x‖ ≤ _ at hh
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hV.uniqueDiffOn ht hx] at hh
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    first | rfl | ring
  · have hz : x ∉ tsupport χ := fun hx' => hx (hχV hx')
    have heq : localizedTensorPullback T χ f =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with y hy
      simp only [Pi.zero_apply] at hy
      simp only [localizedTensorPullback,hy,zero_smul]
    rw [(heq.iteratedFDeriv ℝ j).self_of_nhds]
    simp only [iteratedFDeriv_fun_zero,Pi.zero_apply,norm_zero,mul_zero]
    positivity

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPrimitivePolynomial
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Embed the three mean-polynomial coefficients of one primitive in the
actual global atlas operator, with zero contribution from every other chart. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitivePolyDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitivePolyFiberSpace
local instance primitivePolyDualSmul_rd8bcb4_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitivePolyFiberNormed
local instance primitivePolySectionNormed_rd8bcb4_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance primitivePolySectionSpace_rd8bcb4_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma primitiveAtlasPolynomial_smooth {n : ℕ} (i : A.centers)
    {P : Fin 3 → Fin n → Expression} (hP : ∀ k r, (P k r).SmoothCoeffs univ) :
    ∀ j k r, (A.primitiveAtlasPolynomial i P j k r).SmoothCoeffs univ := by
  classical
  intro j k r
  by_cases hji : j = i
  · simpa only [primitiveAtlasPolynomial,ite_eq_left hji] using hP k r
  · simp only [primitiveAtlasPolynomial,ite_eq_right hji,Expression.SmoothCoeffs]
    exact contDiffOn_const

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SingleTensorRestoreBound
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed atlas estimate for the single tensor patch of a primitive. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.singleTensorDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.singleTensorFiberSpace
local instance singleTensorDualSmul_rd8bcb4_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.singleTensorFiberNormed
local instance singleTensorSectionNormed_rd8bcb4_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance singleTensorSectionSpace_rd8bcb4_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.singleTensorCentersDecidableEq
omit [CompactSpace M] in
lemma tensorPlaneRestore_single (i : A.centers) (f : SmallModes.Base → PhaseMean.Tensor) :
    A.tensorPlaneRestore (fun j => if j = i then f else 0) =
      A.bundleRestore A.tensorTriv i (fun y => fiberFromThree (f (planeCoordinateIsometry y))) := by
  classical
  funext p
  unfold tensorPlaneRestore
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji,bundleRestore]
  · exact fun hi => False.elim (hi (Finset.mem_univ _))

lemma single_tensor_restore_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : SmallModes.Base → PhaseMean.Tensor) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f → _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m C f →
      A.TensorWeightedBound s m (D*C)
        (A.bundleRestore A.tensorTriv i (fun y => fiberFromThree (f (planeCoordinateIsometry y)))) := by
  classical
  obtain ⟨D,hD,hd⟩ := A.tensorPlaneRestore_bound m
  refine ⟨D,hD,?_⟩
  intro f s C hs hs1 hC hf hb
  rw [← A.tensorPlaneRestore_single i f]
  apply hd _ s C hs hs1 hC
  · intro j
    split_ifs
    · exact hf
    · exact contDiff_const
  · intro j
    split_ifs
    · exact hb
    · exact (weightedBound_zero univ s m).mono_const hC

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_NonlinearAtlasErrorBound
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact decomposition of a global primitive's metric defect into the
solved polynomial mean error and the finite periodic remainder. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.nonlinearErrorDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.nonlinearErrorDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.nonlinearErrorFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.nonlinearErrorFiberNormed
local instance nonlinearErrorSectionNormed_rd8bcb4_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance nonlinearErrorSectionSpace_rd8bcb4_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma phaseAtlasRemainder_smooth (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsClosed K) (hKO : K ⊆ O)
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ)
    {n : ℕ} {P : Fin 3 → Fin n → Expression} (hP : ∀ k r, (P k r).SmoothCoeffs univ)
    {B : JetPolynomial.Base → PhaseMean.Tensor} (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ (A.phaseAtlasRemainder i F e U ℓ L z P B) := by
  have hbase := (A.jetChartMap_smooth i hF).comp hi
  have hV := spaceCoordinates.contDiff.comp
    (finiteAnsatz_smooth_global ((A.vectorChartRead_smooth i hF).comp hi) U hK hKO
      (fun j x _ hx => hzero j x hx) ℓ L z)
  have hm (f : JetPolynomial.Base → JetPolynomial.Space) (hf : ContDiff ℝ ∞ f) :
      ContDiff ℝ ∞ (fun y => RealModes.realMetricTensor (f ∘ planeCoordinateIsometry.symm)
        (planeCoordinateIsometry y)) :=
    (contDiffOn_univ.mp (RealModes.contDiffOn_realMetricTensor isOpen_univ
      (hf.comp planeCoordinateIsometry.symm.contDiff).contDiffOn)).comp planeCoordinateIsometry.contDiff
  have hh := (((hm _ hV).sub (hm _ hbase)).sub
    ((coordinatePolynomialValue_smooth hP hbase z).comp planeCoordinateIsometry.contDiff)).sub hB
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext y
  simp only [phaseAtlasRemainder,coordinateMetricMap,Pi.add_apply,Function.comp_apply,Function.comp_assoc]
  rw [sub_add_eq_sub_sub]

/-- A local phase remainder and the actual solved mean control the global metric error. -/
theorem phaseAtlasAnsatz_error_bound_oai (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ e.source)
    {W : Set JetPolynomial.Base} (hW : IsOpen W) (hTW : MapsTo e e.source W) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
    ∀ (O : TopologicalSpace.Opens JetPolynomial.Base) (U : ℕ → Family O Space)
      (K : Set JetPolynomial.Base), IsCompact K → K ⊆ O →
      e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base) →
      (∀ j x, x ∉ K → (U j).val x = 0) →
      (∀ x ∈ e.symm '' K, χ x = 1) →
    ∀ (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ) (n : ℕ)
      (P : Fin 3 → Fin n → Expression), (∀ k r, (P k r).SmoothCoeffs univ) →
    ∀ (γ : ∀ x : M, CovariantTwoTensor x),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun x => TotalSpace.mk' TensorFiber x (γ x)) →
    ∀ (B : JetPolynomial.Base → PhaseMean.Tensor), ContDiff ℝ ∞ B →
    ∀ (s C E : ℝ), 0 < s → s ≤ 1 → 0 ≤ E →
      A.TensorWeightedBound s m C (A.atlasPolynomialMetric (A.primitiveAtlasPolynomial i
        (cutoffTensorPolynomial χ (tensorPolynomialCoordinatePullback P e e.symm))) z F-γ) →
      WeightedEstimates.WeightedBound W s m E (A.phaseAtlasRemainder i F e U ℓ L z P B) →
      A.TensorWeightedBound s m (C+D*E)
        (inducedTensor (A.phaseAtlasAnsatz i F e χ U ℓ L z)-
          (γ+A.bundleRestore A.tensorTriv i (fun y => fiberFromThree (localizedTensorPullback e χ B y)))) := by
  obtain ⟨Dt,hDt,ht⟩ := localized_tensor_pullback_bound he hχ hχc e.open_source hW hχs hTW m
  obtain ⟨Dr,hDr,hr⟩ := A.single_tensor_restore_bound i m
  refine ⟨Dr*Dt,mul_nonneg hDr hDt,?_⟩
  intro F hF O U K hK hKO hKA hzero hone ℓ L z n P hP γ hγ B hB s C E hs hs1 hE hmean hrem
  have hR := A.phaseAtlasRemainder_smooth i hF e hi U hK.isClosed hKO hzero ℓ L z hP hB
  have hpull := localizedTensorPullback_smooth he hχ hR
  have hb := ht _ s E hs hs1 hE hR hrem
  have htensor := weightedBound_comp_isometry_on planeCoordinateIsometry.symm isOpen_univ hpull hb
  have hrb := hr (localizedTensorPullback e χ (A.phaseAtlasRemainder i F e U ℓ L z P B) ∘
      planeCoordinateIsometry.symm) s (Dt*E) hs hs1 (mul_nonneg hDt hE)
    (hpull.comp planeCoordinateIsometry.symm.contDiff) (by simpa only [preimage_univ] using htensor)
  simp only [Function.comp_apply,LinearIsometryEquiv.symm_apply_apply] at hrb
  have hRs := A.bundleRestore_smooth A.tensorTriv A.tensorTriv_domain i
    (fiberFromThree.contDiff.comp hpull)
  have hPm := cutoffTensorPolynomial_smooth hχ (tensorPolynomialCoordinatePullback_smooth hP he hi)
  have hms := (A.atlasPolynomialMetric_smooth (A.primitiveAtlasPolynomial_smooth i hPm) hF z).sub_section hγ
  have hadd := A.tensorWeightedBound_add hms hRs hs.le hmean hrb
  rw [A.phaseAtlasAnsatz_defect i hF e he hi hχ hχs U hK hKO hKA hzero hone ℓ L z P γ B]
  simpa only [Function.comp_def,LinearIsometryEquiv.symm_apply_apply,mul_assoc] using hadd

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseAtlasAnsatz_error_bound_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseAtlasAnsatz_error_bound_oai.{u_1}
