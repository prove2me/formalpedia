-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_mode_quadrature
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:33:09.719762+00:00
-- url     : https://prove2.me/submissions/9fe045bc-af0b-45ce-9ef1-3679a4f3a90f

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
import Definitions.Def_OAIQ249SI010
import Definitions.Def_OAIQ249SI011

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasWeightedBounds
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-atlas weighted norms and bounds for the actual restoration operator. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [IsManifold planeModel ∞ M] in
lemma localize_sum {ι : Type*} (b : Finset ι) (p : M) (ψ : M → ℝ) (f : ι → M → V) :
    localize p ψ (∑ i ∈ b, f i) = fun x => ∑ i ∈ b, localize p ψ (f i) x := by
  funext x
  by_cases hx : x ∈ (chart p).target <;>
    simp [localize, hx, Finset.sum_apply, Finset.smul_sum]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ComplexJetDecomposition
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real and imaginary parts commute with all actual ordered jets. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma complexJet_re {H : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H)
    (w : List (Fin 2)) (a : Fin 4) (p : Base) :
    (complexJet H w a p).re = jet (realField H) w a p := by
  exact (congrFun (directional_clm Complex.reCLM (contDiff_pi.mp hH a)
    (w.map coordinateVector)) p).symm

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ComplexQuadraticVariation
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual complexified second polynomial variation, with both direction
slots and their bilinear algebra made explicit. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression

lemma evalComplex_star (e : MixedExpression) (G : Base → Space) (J : JetData) (z : Base × ℝ) :
    e.evalComplex G (fun i w a p => star (J i w a p)) z = star (e.evalComplex G J z) := by
  induction e with
  | coeff c => simp only [evalComplex, Complex.star_def, Complex.conj_ofReal]
  | atom i w a e ih => simp only [evalComplex, ih, star_mul']
  | add e f ihe ihf => simp only [evalComplex, ihe, ihf, star_add]

lemma quadraticComplex_star (e : Expression) (G : Base → Space)
    (J K : DirectionJets) (z : Base × ℝ) :
    quadraticComplex e G (starDirectionJets J) (starDirectionJets K) z =
      star (quadraticComplex e G J K z) := by
  have he : pairJetData G (starDirectionJets J) (starDirectionJets K) =
      fun i w a p => star (pairJetData G J K i w a p) := by
    funext i w a p
    fin_cases i <;> simp [pairJetData, starDirectionJets]
  change (e.variations 1).evalComplex G _ z = _
  rw [he]
  exact evalComplex_star (e.variations 1) G (pairJetData G J K) z

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RealQuadraticVariation
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The real quadratic variation is the sum of its zero and double phases. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression

lemma starDirectionJets_star (J : DirectionJets) :
    starDirectionJets (starDirectionJets J) = J := by
  funext w a p
  exact star_star _

lemma realDirectionJets_eq (J : DirectionJets) :
    realDirectionJets J = (1 / 2 : ℂ) • (J + starDirectionJets J) := by
  funext w a p
  apply Complex.ext <;> simp [realDirectionJets, starDirectionJets]
  ring

lemma quadraticComplex_real_jets (e : Expression) (G : Base → Space)
    (J : DirectionJets) (z : Base × ℝ) :
    quadraticComplex e G (realDirectionJets J) (realDirectionJets J) z =
      (((quadraticComplex e G J J z).re +
        (quadraticComplex e G J (starDirectionJets J) z).re) / 2 : ℝ) := by
  rw [realDirectionJets_eq, quadraticComplex_smul_left, quadraticComplex_smul_right,
    quadraticComplex_add_left, quadraticComplex_add_right, quadraticComplex_add_right,
    quadraticComplex_star]
  have hcross := quadraticComplex_star e G J (starDirectionJets J) z
  rw [starDirectionJets_star] at hcross
  rw [hcross]
  apply Complex.ext <;> simp
  ring

lemma evalComplex_real_jets (e : MixedExpression) (F : Fin 4 → Base → Space) (z : Base × ℝ) :
    e.evalComplex (F 0) (fun i w a p => (jet (F i) w a p : ℂ)) z = (e.eval F z : ℂ) := by
  induction e with
  | coeff c => rfl
  | atom i w a e ih => simp only [evalComplex, eval, ih, Complex.ofReal_mul]
  | add e f ihe ihf => simp only [evalComplex, eval, ihe, ihf, Complex.ofReal_add]

lemma jet_zero (w : List (Fin 2)) (a : Fin 4) (p : Base) :
    jet (0 : Base → Space) w a p = 0 := by
  exact congrFun (iteratedDirectional_zero (w.map coordinateVector)) p

lemma quadraticComplex_real_fields (e : Expression) (G H K : Base → Space) (z : Base × ℝ) :
    quadraticComplex e G (fun w a p => (jet H w a p : ℂ)) (fun w a p => (jet K w a p : ℂ)) z =
      ((e.variations 1).eval ![G, H, K, 0] z : ℂ) := by
  have he : pairJetData G (fun w a p => (jet H w a p : ℂ)) (fun w a p => (jet K w a p : ℂ)) =
      fun i w a p => (jet (![G, H, K, 0] i) w a p : ℂ) := by
    funext i w a p
    fin_cases i <;> simp [pairJetData, jet_zero]
  change (e.variations 1).evalComplex G _ z = _
  rw [he]
  exact evalComplex_real_jets (e.variations 1) ![G, H, K, 0] z

/-- The factor `1/4` includes the Taylor coefficient `1/2` and the real-mode
splitting. The two terms will become the double and zero phases. -/
theorem half_second_variation_real (e : Expression) (G : Base → Space)
    {H : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H) (z : Base × ℝ) :
    (1 / 2 : ℝ) * (e.variations 1).eval ![G, realField H, realField H, 0] z =
      ((quadraticComplex e G (complexJet H) (complexJet H) z).re +
        (quadraticComplex e G (complexJet H) (starDirectionJets (complexJet H)) z).re) / 4 := by
  have he : (fun w a p => (jet (realField H) w a p : ℂ)) = realDirectionJets (complexJet H) := by
    funext w a p
    exact congrArg Complex.ofReal (complexJet_re hH w a p).symm
  have hh := quadraticComplex_real_jets e G (complexJet H) z
  rw [← he, quadraticComplex_real_fields] at hh
  have hr := congrArg Complex.re hh
  simp only [Complex.ofReal_re] at hr
  linarith

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CoordinateQuadraticExpansion
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport the polynomial quadratic expansion into the same coordinates
and phase labels as the metric quadratic expansion. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open MixedExpression ModulatedJets

lemma coordinate_phase_value (τ : ℝ) (φ : Base → ℝ) (x : Base) :
    QuadraticMean.phase (φ x / τ) = phase τ φ x := by
  simp only [QuadraticMean.phase, phase, Complex.ofReal_div]
  congr 1
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_LowJetCoordinateChange
attribute [-instance] _root_.instVAddIntReal_solutions
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


private lemma iteratedDirectional_eventuallyEq {f g : Base → ℝ} {x : Base}
    (h : f =ᶠ[𝓝 x] g) (vs : List Base) :
    WeightedEstimates.iteratedDirectional vs f =ᶠ[𝓝 x]
      WeightedEstimates.iteratedDirectional vs g := by
  induction vs with
  | nil => exact h
  | cons v vs ih =>
    filter_upwards [ih.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun L : Base →L[ℝ] ℝ => L v) hy

/-- Positional jets only depend on the germ of the map. -/
lemma lowJet_eventuallyEq {G H : Base → Space} {x : Base}
    (h : G =ᶠ[𝓝 x] H) : lowJet G x = lowJet H x := by
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
    have ha : (fun y => G y i.2) =ᶠ[𝓝 x] (fun y => H y i.2) :=
      h.mono (fun _ he => congrFun he i.2)
    exact (iteratedDirectional_eventuallyEq ha ((lowWord i.1).map coordinateVector)).self_of_nhds

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorFiberCoordinates
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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
local instance coordinateFiberSpace_r809c2c_1 : NormedSpace ℝ TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDualSmul
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateFiberGroup
lemma fiberToThree_apply (B : TensorFiber) (k : Fin 3) :
    fiberToThree B k = B (planeCoordinates.symm (firstDirection k))
      (planeCoordinates.symm (secondDirection k)) := rfl

lemma plane_basis_expansion (v : Plane) :
    v = (planeCoordinates v).1 • planeCoordinates.symm SmallModes.dx +
      (planeCoordinates v).2 • planeCoordinates.symm SmallModes.dy := by
  apply planeCoordinates.injective
  simp only [map_add, map_smul, ContinuousLinearEquiv.apply_symm_apply]
  exact RealModes.base_decomposition (planeCoordinates v)

lemma fiberFromThree_toThree (B : TensorFiber) (hB : ∀ v w, B v w = B w v) :
    fiberFromThree (fiberToThree B) = B := by
  ext v w
  rw [fiberFromThree_apply]
  have hcross := hB (planeCoordinates.symm SmallModes.dy) (planeCoordinates.symm SmallModes.dx)
  conv_rhs => rw [plane_basis_expansion v, plane_basis_expansion w]
  simp only [map_add, map_smul, add_apply, smul_apply,
    smul_eq_mul]
  simp only [evaluate, fiberToThree_apply]
  simp only [firstDirection, secondDirection, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecTail, Matrix.vecHead]
  dsimp
  rw [hcross]
  ring

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
local instance symmetryModelComplete_r809c2c_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelSpace
local instance symmetryModelComplete_r809c2c_2 : CompleteSpace TensorFiber := inferInstance
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
local instance phaseFiberNormed_r809c2c_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance phaseFiberSpace_r809c2c_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance phaseDualAdd_r809c2c_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance phaseDualSmul_r809c2c_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance phaseSectionNormed_r809c2c_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance phaseSectionSpace_r809c2c_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorEncode_symmetric {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ∀ p v w, u p v w = u p w v) :
    ∀ x i v w, A.tensorEncode u x i v w = A.tensorEncode u x i w v := by
  have ht : (fun p => tensorTranspose (u p)) = u := by
    funext p
    ext v w
    exact (hu p w v)
  intro x i v w
  have hh := A.tensorLocalize_flip i u
  rw [ht] at hh
  exact congrArg (fun b : TensorFiber => b v w) (congrFun hh x)

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorChartRead
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth chart readings of tensors agree with unweighted components on
the phase support and are bounded by the fixed atlas seminorms. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle WeightedEstimates PhaseMean
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartReadDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartReadDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartReadFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.chartReadFiberSpace
local instance chartReadSectionNormed_r809c2c_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance chartReadSectionSpace_r809c2c_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorChartRead_on_weight (i : A.centers) (u : ∀ x : M, CovariantTwoTensor x)
    {p : M} (hp : p ∈ tsupport (A.weight i)) :
    A.tensorChartRead i u (chart (i : M) p) = fiberToThree (A.bundleComponent A.tensorTriv i u p) := by
  change fiberToThree (localize (i : M) (A.outer i)
    (A.bundleComponent A.tensorTriv i u) (chart (i : M) p)) = _
  rw [localize_chart _ _ _ (A.weight_support i hp), A.outer_one i p hp]
  simp only [one_pow, one_smul]

lemma tensorEncode_read (i : A.centers) (u : ∀ x : M, CovariantTwoTensor x)
    {p : M} (hp : p ∈ (chart (i : M)).source) :
    fiberToThree (A.tensorEncode u (chart (i : M) p) i) =
      (A.weight i p)^2 • A.tensorChartRead i u (chart (i : M) p) := by
  change fiberToThree (localize (i : M) (A.weight i)
    (A.bundleComponent A.tensorTriv i u) (chart (i : M) p)) = _
  rw [localize_chart _ _ _ hp, map_smul]
  by_cases hz : A.weight i p = 0
  · simp only [hz, zero_pow (by decide : 2 ≠ 0), zero_smul]
  · rw [A.tensorChartRead_on_weight i u (subset_tsupport _ hz)]

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
local instance planeReadSectionSpace_r809c2c_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorPlaneReconstruction
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact reconstruction from the three independent tensor coordinates. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean
open JetPolynomial (Base planeCoordinateIsometry)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.reconstructionDualAdd
local instance reconstructionFiberNormed_r809c2c_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance reconstructionFiberSpace_r809c2c_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance reconstructionDualSmul_r809c2c_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance reconstructionSectionNormed_r809c2c_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance reconstructionSectionSpace_r809c2c_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorPlaneRestore_encode (u : ∀ x : M, CovariantTwoTensor x)
    (hu : ∀ p v w, u p v w = u p w v) : A.tensorPlaneRestore (A.tensorPlaneEncode u) = u := by
  have he : (fun x i => fiberFromThree (A.tensorPlaneEncode u i (planeCoordinateIsometry x))) =
      A.tensorEncode u := by
    funext x i
    simp only [tensorPlaneEncode, LinearIsometryEquiv.symm_apply_apply]
    exact fiberFromThree_toThree _ (A.tensorEncode_symmetric hu x i)
  change A.tensorDecode (fun x i => fiberFromThree (A.tensorPlaneEncode u i (planeCoordinateIsometry x))) = u
  rw [he, A.tensorDecode_encode]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorPlaneWeight
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual chart cutoff whose square converts an unweighted tensor
reading into its atlas coordinate component. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean WeightedEstimates
open JetPolynomial (Base planeCoordinateIsometry)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
local instance weightPlaneFiberNormed_r809c2c_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance weightPlaneFiberSpace_r809c2c_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance weightPlaneDualAdd_r809c2c_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance weightPlaneDualSmul_r809c2c_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance weightPlaneSectionNormed_r809c2c_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance weightPlaneSectionSpace_r809c2c_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorPlaneEncode_weight (i : A.centers) (u : ∀ x : M, CovariantTwoTensor x)
    (y : SmallModes.Base) :
    A.tensorPlaneEncode u i y = (A.planeWeight i y)^2 • A.tensorPlaneRead i u y := by
  let x := planeCoordinateIsometry.symm y
  change fiberToThree (A.tensorEncode u x i) = (A.chartWeight i x)^2 • A.tensorChartRead i u x
  by_cases hx : x ∈ (chart (i : M)).target
  · have hp := (chart (i : M)).map_target hx
    have hh := A.tensorEncode_read i u hp
    rw [(chart (i : M)).right_inv hx] at hh
    simpa only [chartWeight, indicator_of_mem hx] using hh
  · simp only [tensorEncode, bundleLocalize, localize, indicator_of_notMem hx, map_zero,
      chartWeight, zero_pow (by decide : 2 ≠ 0), zero_smul]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialRepresentation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constructed coordinate representatives of the same global polynomial
tensor. These are derived from the actual read/restore maps. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base Expression)
open JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polyRepDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polyRepFiberSpace
local instance polyRepDualSmul_r809c2c_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polyRepFiberNormed
local instance polyRepSectionNormed_r809c2c_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polyRepSectionSpace_r809c2c_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma tensorChartRead_sum {ι : Type*} [Fintype ι] (i : A.centers)
    (u : ι → ∀ p : M, CovariantTwoTensor p) :
    A.tensorChartRead i (∑ k, u k) = ∑ k, A.tensorChartRead i (u k) := by
  classical
  funext x
  by_cases hx : x ∈ (chart (i : M)).target
  · simp only [tensorChartRead,Function.comp_apply,bundleCutoff,localize,
      indicator_of_mem hx,bundleComponent,Finset.sum_apply,map_sum,Finset.smul_sum]
  · simp only [tensorChartRead,Function.comp_apply,bundleCutoff,localize,
      indicator_of_notMem hx,map_zero,Finset.sum_apply,Finset.sum_const_zero]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GlobalOscillatoryModes
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global phase/amplitude representatives of the actual supported oscillations. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (planeCoordinateIsometry)
open QuadraticMean (realMode realPartCLM)

lemma realMode_contDiff {n : ℕ} (τ : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℂ) => realMode (p.1/τ) p.2) := by
  change ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℂ) =>
    realPartCLM n (QuadraticMean.phase (p.1/τ) • p.2))
  apply (realPartCLM n).contDiff.comp
  apply ContDiff.smul (f := fun p : ℝ × (Fin n → ℂ) => QuadraticMean.phase (p.1/τ))
    (g := fun p : ℝ × (Fin n → ℂ) => p.2)
  · have ha : ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℂ) => ((p.1/τ : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_fst.div_const τ)
    exact Complex.contDiff_exp.comp (ha.mul contDiff_const)
  · exact contDiff_snd

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
lemma surfaceMode_smooth {n : ℕ} (τ : ℝ) {φ : M → ℝ} {Z : M → Fin n → ℂ}
    (hφ : ContMDiff planeModel 𝓘(ℝ) ∞ φ)
    (hZ : ContMDiff planeModel 𝓘(ℝ,Fin n → ℂ) ∞ Z) :
    ContMDiff planeModel 𝓘(ℝ,Fin n → ℝ) ∞ (surfaceMode τ φ Z) :=
  (realMode_contDiff τ).contMDiff.comp (hφ.prodMk_space hZ)

variable [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma vectorChartRead_mode_on_support {n : ℕ} (i : A.centers) (τ : ℝ)
    (φ : M → ℝ) (Z : M → Fin n → ℂ) {x : JetPolynomial.Base}
    (hx : x ∈ (A.chartWeightCompact i : Set JetPolynomial.Base)) :
    A.vectorChartRead i (surfaceMode τ φ Z) x =
      realMode (A.vectorChartRead i φ x/τ) (A.vectorChartRead i Z x) := by
  rw [A.vectorChartRead_on_support i _ hx,A.vectorChartRead_on_support i _ hx,
    A.vectorChartRead_on_support i _ hx]
  rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GlobalModeDifferential
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual chart differentials of global oscillatory modes. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (planeCoordinateIsometry)
open QuadraticMean (realMode realPartCLM)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma vectorPlaneRead_const_smul {n : ℕ} (i : A.centers) (c : ℂ) (Z : M → Fin n → ℂ) :
    A.vectorPlaneRead i (fun p => c • Z p) = fun x => c • A.vectorPlaneRead i Z x := by
  funext x
  by_cases hx : planeCoordinateIsometry.symm x ∈ (chart (i : M)).target
  · simp only [vectorPlaneRead,vectorChartRead,localize,Function.comp_apply,indicator_of_mem hx]
    exact smul_comm _ _ _
  · simp only [vectorPlaneRead,vectorChartRead,localize,Function.comp_apply,indicator_of_notMem hx,
      smul_zero]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasMetricLocalModel
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local coordinate models of the complete perturbed global metric. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricLocalDualAdd
local instance metricLocalFiberNormed_r809c2c_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance metricLocalFiberSpace_r809c2c_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance metricLocalDualSmul_r809c2c_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance metricLocalSectionNormed_r809c2c_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricLocalSectionSpace_r809c2c_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma tensorChartRead_add (i : A.centers) (u v : ∀ p : M, CovariantTwoTensor p) :
    A.tensorChartRead i (u+v) = A.tensorChartRead i u+A.tensorChartRead i v := by
  have h := A.tensorChartRead_sum i ![u,v]
  simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one] using h

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasModeGerms
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every global mode sum has the expected local oscillatory germ on an
active atlas chart. No equality of cutoffs outside that locus is assumed. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma jetChartMap_euclidean (i : A.centers) (X : M → RealModes.RVec 4) :
    A.jetChartMap i (spaceCoordinates.symm ∘ X) = A.vectorChartRead i X := by
  funext x
  change spaceCoordinates (localize (i : M) (A.outer i) (spaceCoordinates.symm ∘ X) x) = _
  by_cases hx : x ∈ (chart (i : M)).target
  · simp only [localize,indicator_of_mem hx,Function.comp_apply,map_smul,
      ContinuousLinearEquiv.apply_symm_apply,vectorChartRead]
  · simp only [localize,indicator_of_notMem hx,map_zero,vectorChartRead]

lemma jetChartMap_modes_germ {ι : Type*} [Fintype ι]
    (i : A.centers) (τ : ℝ) (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    {x : Base} (hx : A.chartWeight i x ≠ 0) :
    A.jetChartMap i (spaceCoordinates.symm ∘ ∑ j, surfaceMode τ (φ j) (Z j)) =ᶠ[𝓝 x]
      (QuadraticMean.sumDisplacement τ
        (fun j => coordinatePhase (A.vectorChartRead i (φ j)))
        (fun j => coordinateAmplitude (A.vectorChartRead i (Z j))) ∘ planeCoordinateIsometry) := by
  have hopen := (A.chartWeight_smooth i).continuous.isOpen_support
  rw [A.jetChartMap_euclidean]
  filter_upwards [hopen.mem_nhds hx] with y hy
  have hys : y ∈ (A.chartWeightCompact i : Set Base) := by
    rw [← A.chartWeight_tsupport i]
    exact subset_tsupport (A.chartWeight i) hy
  change localize (i : M) (A.outer i) (∑ j, surfaceMode τ (φ j) (Z j)) y = _
  rw [localize_sum]
  simp only [Function.comp_apply,QuadraticMean.sumDisplacement,
    QuadraticMean.displacement,coordinatePhase,coordinateAmplitude,
    planeCoordinateIsometry.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact A.vectorChartRead_mode_on_support i τ (φ j) (Z j) hys

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialLocality
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite jet expression depends only on the germ of its input map. -/
noncomputable section
open scoped ContDiff Topology
namespace ClosedSurfaceR4.JetPolynomial

lemma jet_eventuallyEq {G H : Base → Space} {x : Base}
    (h : G =ᶠ[𝓝 x] H) (w : List (Fin 2)) (a : Fin 4) :
    jet G w a =ᶠ[𝓝 x] jet H w a := by
  induction w with
  | nil => exact h.mono (fun _ he => congrFun he a)
  | cons i w ih =>
    filter_upwards [ih.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun L : Base →L[ℝ] ℝ => L (coordinateVector i)) hy

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_MixedPolynomialLocality
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Mixed variations only use the germs of their four input fields. -/
noncomputable section
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.JetPolynomial

lemma MixedExpression.eval_eq_of_eventuallyEq {F G : Fin 4 → Base → Space} {x : Base}
    (h : ∀ i, F i =ᶠ[𝓝 x] G i) (e : MixedExpression) (t : ℝ) :
    e.eval F (x,t) = e.eval G (x,t) := by
  induction e with
  | coeff c =>
    change c (lowJet (F 0) x,t) = c (lowJet (G 0) x,t)
    rw [lowJet_eventuallyEq (h 0)]
  | atom i w a e ih =>
    change jet (F i) w a x * e.eval F (x,t) = jet (G i) w a x * e.eval G (x,t)
    rw [(jet_eventuallyEq (h i) w a).self_of_nhds,ih]
  | add e f ihe ihf =>
    change e.eval F (x,t)+f.eval F (x,t) = e.eval G (x,t)+f.eval G (x,t)
    rw [ihe,ihf]

namespace Perturbation

lemma coordinateQuadraticPolynomial_eq_of_eventuallyEq {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {X Y : RealModes.RField 4} {x : Base}
    (h : X ∘ planeCoordinateIsometry =ᶠ[𝓝 x] Y ∘ planeCoordinateIsometry) (t : ℝ) :
    coordinateQuadraticPolynomial P ε G X t (planeCoordinateIsometry x) =
      coordinateQuadraticPolynomial P ε G Y t (planeCoordinateIsometry x) := by
  have hf : ∀ i : Fin 4, (![G,X ∘ planeCoordinateIsometry,X ∘ planeCoordinateIsometry,0] i) =ᶠ[𝓝 x]
      (![G,Y ∘ planeCoordinateIsometry,Y ∘ planeCoordinateIsometry,0] i) := by
    intro i
    fin_cases i
    · exact Filter.EventuallyEq.rfl
    · exact h
    · exact h
    · exact Filter.EventuallyEq.rfl
  funext k
  simp only [coordinateQuadraticPolynomial,planeCoordinateIsometry.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro l _
  rw [MixedExpression.eval_eq_of_eventuallyEq hf ((P k l).variations 1) t]

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialQuadrature
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial Hessian has the same two-quadrature zero-mode identity
as the metric Hessian. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression ModulatedJets

lemma complexJet_const_smul {H : Base → Fin 4 → ℂ}
    (hH : ContDiff ℝ ∞ H) (c : ℂ) :
    complexJet (fun p => c • H p) = c • complexJet H := by
  funext w a p
  exact congrFun (directional_clm (c • ContinuousLinearMap.id ℝ ℂ)
    (contDiff_pi.mp hH a) (w.map coordinateVector)) p

lemma starDirectionJets_const_smul (J : DirectionJets) (c : ℂ) :
    starDirectionJets (c • J) = star c • starDirectionJets J := by
  funext w a p
  simp only [starDirectionJets,Pi.smul_apply,smul_eq_mul,star_mul']

lemma half_second_variation_quadrature (e : Expression) (G : Base → Space)
    {H : Base → Fin 4 → ℂ} (hH : ContDiff ℝ ∞ H) (z : Base × ℝ) :
    (1 / 2 : ℝ) * (e.variations 1).eval ![G,realField H,realField H,0] z +
      (1 / 2 : ℝ) * (e.variations 1).eval
        ![G,realField (fun p => Complex.I • H p),realField (fun p => Complex.I • H p),0] z =
      2 * (quadraticComplex e G (complexJet H)
        (starDirectionJets (complexJet H)) z).re / 4 := by
  have hI : ContDiff ℝ ∞ (fun p => Complex.I • H p) :=
    (contDiff_const (c := Complex.I)).smul hH
  rw [half_second_variation_real e G hH,half_second_variation_real e G hI,
    complexJet_const_smul hH,starDirectionJets_const_smul,
    quadraticComplex_smul_left,quadraticComplex_smul_right,
    quadraticComplex_smul_left,quadraticComplex_smul_right]
  simp only [Complex.star_def,Complex.conj_I]
  simp only [← mul_assoc,Complex.I_mul_I,neg_mul,mul_neg,neg_neg,one_mul,
    Complex.neg_re]
  ring

namespace Perturbation

lemma polynomial_quadrature_sum {n : ℕ} (P : Fin n → Expression) (ε : ℝ)
    (G : Base → Space) {φ : Base → ℝ} {H : Base → Fin 4 → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hH : ContDiff ℝ ∞ H) (τ t : ℝ) (x : Base) :
    (∑ l, ε^(l.val+1) * ((1/2 : ℝ) * ((P l).variations 1).eval
      ![G,realField (fun p => phase τ φ p • H p),realField (fun p => phase τ φ p • H p),0] (x,t))) +
    (∑ l, ε^(l.val+1) * ((1/2 : ℝ) * ((P l).variations 1).eval
      ![G,realField (fun p => phase τ φ p • (Complex.I • H p)),
        realField (fun p => phase τ φ p • (Complex.I • H p)),0] (x,t))) =
    2 * quadraticMeanCoefficient P ε G φ H τ t x := by
  rw [← quadraticMeanPair_self P ε G hφ hH]
  unfold quadraticMeanPair
  rw [← Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  have he : (fun p => phase τ φ p • (Complex.I • H p)) =
      fun p => Complex.I • (phase τ φ p • H p) := by
    funext p
    exact smul_comm _ _ _
  rw [he,← mul_add]
  rw [half_second_variation_quadrature (P l) G
    (H := fun p => phase τ φ p • H p) ((phase_smooth hφ τ).smul hH)]
  ring

lemma real_mode_coordinates (τ : ℝ) (φ : Base → ℝ) (H : Base → Fin 4 → ℂ) :
    realField (fun p => phase τ φ p • H p) =
      QuadraticMean.displacement τ (coordinatePhase φ) (coordinateAmplitude H) ∘
        planeCoordinateIsometry := by
  funext x a
  simp only [realField,QuadraticMean.displacement,QuadraticMean.realMode,
    QuadraticMean.realPart,Function.comp_apply,coordinatePhase,coordinateAmplitude,
    planeCoordinateIsometry.symm_apply_apply,Pi.smul_apply,smul_eq_mul,coordinate_phase_value]

theorem coordinate_polynomial_quadrature {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {φ : Base → ℝ} {H : Base → Fin 4 → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hH : ContDiff ℝ ∞ H) (τ t : ℝ) :
    coordinateQuadraticPolynomial P ε G
        (QuadraticMean.displacement τ (coordinatePhase φ) (coordinateAmplitude H)) t +
      coordinateQuadraticPolynomial P ε G
        (QuadraticMean.displacement τ (coordinatePhase φ)
          (coordinateAmplitude (fun p => Complex.I • H p))) t =
      (2 : ℝ) • (fun y k => quadraticMeanCoefficient (P k) ε G φ H τ t
        (planeCoordinateIsometry.symm y)) := by
  ext y k
  have hh := polynomial_quadrature_sum (P k) ε G hφ hH τ t
    (planeCoordinateIsometry.symm y)
  simp only [real_mode_coordinates,coordinateQuadraticPolynomial,Pi.add_apply,
    Pi.smul_apply,smul_eq_mul] at hh ⊢
  exact hh

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialModeMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The full quadratic global interaction has one supported family of
oscillatory targets, including the polynomial perturbation. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.modeMeanDualAdd
local instance modeMeanFiberNormed_r809c2c_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance modeMeanFiberSpace_r809c2c_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance modeMeanDualSmul_r809c2c_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)



local instance modeMeanSectionNormed_r809c2c_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance modeMeanSectionSpace_r809c2c_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma local_single_mode_quadratic {m : ℕ} (i : A.centers)
    (Q : Fin 3 → Fin m → Expression) (ε : ℝ) (G : Base → JetPolynomial.Space)
    (τ : ℝ) (φ : M → ℝ) (Z : M → Fin 4 → ℂ)
    {x : Base} (hx : A.chartWeight i x ≠ 0) :
    coordinateQuadraticPolynomial Q ε G
      (A.jetChartMap i (spaceCoordinates.symm ∘ surfaceMode τ φ Z) ∘ planeCoordinateIsometry.symm)
      0 (planeCoordinateIsometry x) =
    coordinateQuadraticPolynomial Q ε G
      (QuadraticMean.displacement τ (A.vectorPlaneRead i φ) (A.vectorPlaneRead i Z))
      0 (planeCoordinateIsometry x) := by
  have hh := A.jetChartMap_modes_germ (ι := Unit) i τ (fun _ => φ) (fun _ => Z) hx
  have he : (A.jetChartMap i (spaceCoordinates.symm ∘ surfaceMode τ φ Z) ∘
      planeCoordinateIsometry.symm) ∘ planeCoordinateIsometry =ᶠ[𝓝 x]
      QuadraticMean.displacement τ (A.vectorPlaneRead i φ) (A.vectorPlaneRead i Z) ∘
        planeCoordinateIsometry := by
    simpa only [Fintype.sum_unique,QuadraticMean.sumDisplacement,vectorPlaneRead,
      Function.comp_def,planeCoordinateIsometry.symm_apply_apply] using hh
  exact coordinateQuadraticPolynomial_eq_of_eventuallyEq Q ε G he 0

theorem polynomial_mode_quadrature_oai {n : A.centers → ℕ} {m : ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (Q : A.centers → Fin 3 → Fin m → Expression)
    (hrep : A.PolynomialQuadraticRepresentation P Q)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F) (ε τ : ℝ)
    (φ : M → ℝ) (Z : M → Fin 4 → ℂ)
    (hφ : ContMDiff planeModel 𝓘(ℝ) ∞ φ)
    (hZ : ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ Z) :
    A.atlasPolynomialQuadratic P ε F (spaceCoordinates.symm ∘ surfaceMode τ φ Z)+
      A.atlasPolynomialQuadratic P ε F
        (spaceCoordinates.symm ∘ surfaceMode τ φ (fun p => Complex.I • Z p)) =
      (2 : ℝ) • A.polynomialModeMean Q F ε τ φ Z := by
  let W := spaceCoordinates.symm ∘ surfaceMode τ φ Z
  let WI := spaceCoordinates.symm ∘ surfaceMode τ φ (fun p => Complex.I • Z p)
  have hi : ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (fun p => Complex.I • Z p) :=
    ((contDiff_const (c := Complex.I)).smul contDiff_id).contMDiff.comp hZ
  have hW : ContMDiff planeModel spaceModel ∞ W :=
    spaceCoordinates.symm.contDiff.contMDiff.comp (surfaceMode_smooth τ hφ hZ)
  have hWI : ContMDiff planeModel spaceModel ∞ WI :=
    spaceCoordinates.symm.contDiff.contMDiff.comp (surfaceMode_smooth τ hφ hi)
  let R := A.atlasPolynomialQuadratic P ε F W+A.atlasPolynomialQuadratic P ε F WI
  have hs : ∀ p v w, R p v w = R p w v := by
    intro p v w
    exact congrArg₂ (· + ·) (A.tensorPlaneRestore_symmetric _ p v w)
      (A.tensorPlaneRestore_symmetric _ p v w)
  change R = _
  rw [← A.tensorPlaneRestore_encode R hs]
  unfold polynomialModeMean
  rw [← A.tensorPlaneRestore_smul]
  congr 1
  funext i y
  rw [A.tensorPlaneEncode_weight]
  by_cases hz : A.planeWeight i y = 0
  · simp only [hz,zero_pow (by decide : 2 ≠ 0),zero_smul,Pi.smul_apply,smul_zero]
  · have hx : A.chartWeight i (planeCoordinateIsometry.symm y) ≠ 0 := hz
    have hc : planeCoordinateIsometry.symm y ∈ (A.chartWeightCompact i : Set Base) := by
      rw [← A.chartWeight_tsupport i]
      exact subset_tsupport _ hx
    have hr := hrep F W hF hW i _ hc ε
    have hri := hrep F WI hF hWI i _ hc ε
    have he := A.local_single_mode_quadratic i (Q i) ε (A.jetChartMap i F) τ φ Z hx
    have hei := A.local_single_mode_quadratic i (Q i) ε (A.jetChartMap i F) τ φ
      (fun p => Complex.I • Z p) hx
    simp only [planeCoordinateIsometry.apply_symm_apply] at hr hri he hei
    change (A.planeWeight i y)^2 • A.tensorChartRead i R (planeCoordinateIsometry.symm y) = _
    dsimp only [R]
    rw [A.tensorChartRead_add]
    simp only [Pi.add_apply]
    rw [← hr,← hri,he,hei]
    have hreadI : A.vectorPlaneRead i (fun p => Complex.I • Z p) =
        coordinateAmplitude (fun x => Complex.I • A.vectorChartRead i Z x) := by
      rw [A.vectorPlaneRead_const_smul]
      rfl
    rw [hreadI]
    have hq := congrFun (coordinate_polynomial_quadrature (Q i) ε (A.jetChartMap i F)
      (A.vectorChartRead_smooth i hφ) (A.vectorChartRead_smooth i hZ) τ 0) y
    simp only [Pi.add_apply,Pi.smul_apply] at hq ⊢
    rw [show A.vectorPlaneRead i φ = coordinatePhase (A.vectorChartRead i φ) from rfl,
      show A.vectorPlaneRead i Z = coordinateAmplitude (A.vectorChartRead i Z) from rfl,hq]
    exact smul_comm _ _ _

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_mode_quadrature_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_mode_quadrature_oai.{u_1}
