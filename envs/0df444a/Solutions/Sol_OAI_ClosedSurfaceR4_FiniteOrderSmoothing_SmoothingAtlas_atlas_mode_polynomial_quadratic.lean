-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_mode_polynomial_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:33:59.546122+00:00
-- url     : https://prove2.me/submissions/2e040831-53ff-4acc-aa01-60622176a0c2

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteQuadraticVariation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite sums in the actual complexified Hessian. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression ModulatedJets

lemma quadraticComplex_sum {ι κ : Type*} (a : Finset ι) (b : Finset κ)
    (e : Expression) (G : Base → Space) (J : ι → DirectionJets) (K : κ → DirectionJets)
    (z : Base × ℝ) :
    quadraticComplex e G (∑ i ∈ a, J i) (∑ j ∈ b, K j) z =
      ∑ i ∈ a, ∑ j ∈ b, quadraticComplex e G (J i) (K j) z := by
  change quadraticComplexBilinear e G z (∑ i ∈ a, J i) (∑ j ∈ b, K j) = _
  rw [map_sum]
  simp only [LinearMap.sum_apply, map_sum]
  rw [Finset.sum_comm]
  rfl

lemma complexJet_add {H K : Base → Fin 4 → ℂ}
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) :
    complexJet (fun p => H p + K p) = complexJet H + complexJet K := by
  funext w a p
  exact congrFun (directional_add (contDiff_pi.mp hH a) (contDiff_pi.mp hK a)
    (w.map coordinateVector)) p

lemma complexJet_zero : complexJet (0 : Base → Fin 4 → ℂ) = 0 := by
  funext w a p
  exact congrFun (iteratedDirectional_zero (w.map coordinateVector)) p

lemma complexJet_sum {ι : Type*} (a : Finset ι) (H : ι → Base → Fin 4 → ℂ)
    (hH : ∀ i ∈ a, ContDiff ℝ ∞ (H i)) :
    complexJet (fun p => ∑ i ∈ a, H i p) = ∑ i ∈ a, complexJet (H i) := by
  classical
  induction a using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact complexJet_zero
  | @insert i a hi ih =>
    have hsm : ContDiff ℝ ∞ (fun p => ∑ j ∈ a, H j p) :=
      ContDiff.sum (fun j hj => hH j (Finset.mem_insert_of_mem hj))
    simp only [Finset.sum_insert hi]
    rw [complexJet_add (hH i (Finset.mem_insert_self _ _)) hsm,
      ih (fun j hj => hH j (Finset.mem_insert_of_mem hj))]

lemma starDirectionJets_sum {ι : Type*} (a : Finset ι) (J : ι → DirectionJets) :
    starDirectionJets (∑ i ∈ a, J i) = ∑ i ∈ a, starDirectionJets (J i) := by
  funext w b p
  simp [starDirectionJets, Finset.sum_apply, star_sum]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FinitePolynomialPhases
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite expansion of the polynomial quadratic term before
separating its zero phases. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression ModulatedJets

lemma half_second_variation_sum {ι : Type*} [Fintype ι]
    (e : Expression) (G : Base → Space) (H : ι → Base → Fin 4 → ℂ)
    (hH : ∀ i, ContDiff ℝ ∞ (H i)) (z : Base × ℝ) :
    (1 / 2 : ℝ) * (e.variations 1).eval
      ![G, realField (fun p => ∑ i, H i p), realField (fun p => ∑ i, H i p), 0] z =
      (∑ i, ∑ j, (quadraticComplex e G (complexJet (H i)) (complexJet (H j)) z).re / 4) +
      ∑ i, ∑ j, (quadraticComplex e G (complexJet (H i))
        (starDirectionJets (complexJet (H j))) z).re / 4 := by
  have hsum : ContDiff ℝ ∞ (fun p => ∑ i, H i p) := ContDiff.sum (fun i _ => hH i)
  rw [half_second_variation_real e G hsum, complexJet_sum Finset.univ H (fun i _ => hH i),
    starDirectionJets_sum, quadraticComplex_sum, quadraticComplex_sum]
  simp only [Complex.re_sum, Finset.sum_div, add_div]


theorem half_second_variation_phases {ι : Type*} [Fintype ι]
    (e : Expression) (G : Base → Space) (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ)
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (hH : ∀ i, ContDiff ℝ ∞ (H i)) (τ : ℝ) (z : Base × ℝ) :
    (1 / 2 : ℝ) * (e.variations 1).eval
      ![G, realField (oscillatorySum τ φ H), realField (oscillatorySum τ φ H), 0] z =
      (∑ i, ∑ j, ((phase τ (φ i) z.1 * phase τ (φ j) z.1) *
        conjugatedVariation e G (pairPhases (φ i) (φ j)) (pairDirections (H i) (H j)) τ 1 z).re / 4) +
      ∑ i, ∑ j, ((phase τ (φ i) z.1 * phase τ (fun p => -φ j p) z.1) *
        conjugatedVariation e G (pairPhases (φ i) (fun p => -φ j p))
          (pairDirections (H i) (starField (H j))) τ 1 z).re / 4 := by
  have hsm (i : ι) : ContDiff ℝ ∞ (fun p => phase τ (φ i) p • H i p) :=
    (phase_smooth (hφ i) τ).smul (hH i)
  rw [show oscillatorySum τ φ H = fun p => ∑ i, phase τ (φ i) p • H i p from rfl,
    half_second_variation_sum e G _ hsm]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [quadraticComplex_phase_factor]
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [← complexJet_starField (hsm j), starField_phase, quadraticComplex_phase_factor]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialZeroPhaseExpansion
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separate the actual polynomial Hessian into its zero-phase part and
explicit doubled and mixed phases. Ordered pairs retain all multiplicities. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression ModulatedJets
namespace Perturbation

lemma phase_mul (τ : ℝ) (φ ψ : Base → ℝ) (p : Base) :
    phase τ φ p * phase τ ψ p = phase τ (fun x => φ x + ψ x) p := by
  simp only [phase, Complex.ofReal_add, mul_add, Complex.exp_add]

lemma quadraticMeanCoefficient_eq_phaseCoefficient {n : ℕ}
    (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : Base → ℝ) (H : Base → Fin 4 → ℂ) (τ t : ℝ) (p : Base) :
    quadraticMeanCoefficient P ε G φ H τ t p =
      (quadraticPhaseCoefficient P ε G φ (fun x => -φ x) H (starField H) τ t p).re := by
  simp only [quadraticMeanCoefficient, quadraticPhaseCoefficient, Complex.div_ofNat_re]

lemma quadraticPhaseCoefficient_oscillation {n : ℕ}
    (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ ψ : Base → ℝ) (H K : Base → Fin 4 → ℂ) (τ : ℝ) (z : Base × ℝ) :
    (phase τ (fun x => φ x + ψ x) z.1 *
      quadraticPhaseCoefficient P ε G φ ψ H K τ z.2 z.1).re =
    ∑ l, ε ^ (l.val + 1) *
      ((phase τ φ z.1 * phase τ ψ z.1) *
        conjugatedVariation (P l) G (pairPhases φ ψ) (pairDirections H K) τ 1 z).re / 4 := by
  rw [← phase_mul]
  simp only [quadraticPhaseCoefficient, conjugated, div_eq_mul_inv, Finset.mul_sum,
    Finset.sum_mul, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.inv_re, Complex.inv_im,
    Complex.normSq_ofNat]
  norm_num
  ring

lemma weighted_half_second_variation_phases {n : ℕ} {ι : Type*} [Fintype ι]
    (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ)
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (hH : ∀ i, ContDiff ℝ ∞ (H i))
    (τ : ℝ) (z : Base × ℝ) :
    (∑ l : Fin n, ε ^ (l.val + 1) * ((1 / 2 : ℝ) * ((P l).variations 1).eval
      ![G, realField (oscillatorySum τ φ H), realField (oscillatorySum τ φ H), 0] z)) =
    (∑ i, ∑ j, (phase τ (fun x => φ i x + φ j x) z.1 *
      quadraticPhaseCoefficient P ε G (φ i) (φ j) (H i) (H j) τ z.2 z.1).re) +
    ∑ i, ∑ j, (phase τ (fun x => φ i x - φ j x) z.1 *
      quadraticPhaseCoefficient P ε G (φ i) (fun x => -φ j x)
        (H i) (starField (H j)) τ z.2 z.1).re := by
  classical
  simp only [half_second_variation_phases _ G φ H hφ hH τ z,
    mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  congr 1 <;> rw [Finset.sum_comm] <;> apply Finset.sum_congr rfl <;> intro i hi <;>
    rw [Finset.sum_comm] <;> apply Finset.sum_congr rfl <;> intro j hj
  · simpa only [mul_div_assoc] using (quadraticPhaseCoefficient_oscillation P ε G (φ i) (φ j) (H i) (H j) τ z).symm
  · simpa only [mul_div_assoc, sub_eq_add_neg] using (quadraticPhaseCoefficient_oscillation P ε G (φ i) (fun x => -φ j x)
      (H i) (starField (H j)) τ z).symm

/-- The omitted terms have exactly the doubled/sum/difference phases. The
geometric good-phase hypothesis is only needed later to solve these modes. -/
theorem quadratic_zero_phase_expansion {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ)
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (hH : ∀ i, ContDiff ℝ ∞ (H i))
    (τ t : ℝ) (p : Base) :
    (∑ l : Fin n, ε ^ (l.val + 1) * ((1 / 2 : ℝ) * ((P l).variations 1).eval
      ![G, realField (oscillatorySum τ φ H), realField (oscillatorySum τ φ H), 0] (p,t))) =
    (∑ i, quadraticMeanCoefficient P ε G (φ i) (H i) τ t p) +
      quadraticOscillation P ε G φ H τ t p := by
  rw [weighted_half_second_variation_phases P ε G φ H hφ hH τ (p,t)]
  have hrow (i : ι) :
      (∑ j, (phase τ (fun x => φ i x - φ j x) p *
        quadraticPhaseCoefficient P ε G (φ i) (fun x => -φ j x)
          (H i) (starField (H j)) τ t p).re) =
      quadraticMeanCoefficient P ε G (φ i) (H i) τ t p +
      ∑ j ∈ Finset.univ.erase i, (phase τ (fun x => φ i x - φ j x) p *
        quadraticPhaseCoefficient P ε G (φ i) (fun x => -φ j x)
          (H i) (starField (H j)) τ t p).re := by
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)]
    have hz : phase τ (fun _ : Base => (0 : ℝ)) p = 1 := by simp [phase]
    simp only [sub_self, hz, one_mul, quadraticMeanCoefficient_eq_phaseCoefficient]
    ring
  simp only [hrow, Finset.sum_add_distrib, quadraticOscillation]
  ring

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialQuadraticFamily
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Index the polynomial quadratic remainder by the same doubled and
mixed labels used for the metric quadratic remainder. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open ModulatedJets

theorem quadraticOscillation_eq_family {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ) (τ t : ℝ) (p : Base) :
    quadraticOscillation P ε G φ H τ t p =
      ∑ l : RealModes.QuadraticLabel ι,
        (phase τ (quadraticFamilyPhase φ l) p * quadraticFamilyCoefficient P ε G φ H τ t l p).re := by
  have hsplit (i : ι) :
      (∑ j, (phase τ (fun x => φ i x + φ j x) p *
        quadraticPhaseCoefficient P ε G (φ i) (φ j) (H i) (H j) τ t p).re) =
      (phase τ (fun x => 2 * φ i x) p *
        quadraticPhaseCoefficient P ε G (φ i) (φ i) (H i) (H i) τ t p).re +
      ∑ j ∈ Finset.univ.erase i, (phase τ (fun x => φ i x + φ j x) p *
        quadraticPhaseCoefficient P ε G (φ i) (φ j) (H i) (H j) τ t p).re := by
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)]
    have hh : (fun x => φ i x + φ i x) = (fun x => 2 * φ i x) := by funext x; ring
    rw [hh, add_comm]
  rw [quadraticOscillation, Fintype.sum_sum_type]
  simp only [hsplit, Finset.sum_add_distrib]
  change _ = _ + ∑ l : Σ i : ι, {j : ι // j ≠ i} × Bool, _
  rw [Fintype.sum_sigma]
  have hcross :
      (∑ i, ∑ j ∈ Finset.univ.erase i, (phase τ (fun x => φ i x + φ j x) p *
        quadraticPhaseCoefficient P ε G (φ i) (φ j) (H i) (H j) τ t p).re) +
      (∑ i, ∑ j ∈ Finset.univ.erase i, (phase τ (fun x => φ i x - φ j x) p *
        quadraticPhaseCoefficient P ε G (φ i) (fun x => -φ j x) (H i) (starField (H j)) τ t p).re) =
      ∑ i, ∑ l : {j : ι // j ≠ i} × Bool,
        (phase τ (quadraticFamilyPhase φ (.inr ⟨i,l⟩)) p *
          quadraticFamilyCoefficient P ε G φ H τ t (.inr ⟨i,l⟩) p).re := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
    trans ∑ j : {j : ι // j ≠ i},
      ((phase τ (fun x => φ i x + φ j x) p *
        quadraticPhaseCoefficient P ε G (φ i) (φ j) (H i) (H j) τ t p).re +
       (phase τ (fun x => φ i x - φ j x) p *
        quadraticPhaseCoefficient P ε G (φ i) (fun x => -φ j x)
          (H i) (starField (H j)) τ t p).re)
    · exact Finset.sum_subtype (Finset.univ.erase i) (fun j => by simp) _
    apply Finset.sum_congr rfl
    intro j hj
    rw [Fintype.sum_bool]
    simp only [quadraticFamilyPhase, quadraticFamilyCoefficient, Bool.false_eq_true, ↓reduceIte]
    ring
  change (_ + _) + _ = _ + _
  rw [add_assoc, hcross]
  rfl

end ClosedSurfaceR4.JetPolynomial.Perturbation

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

lemma real_oscillatorySum_coordinates {ι : Type*} [Fintype ι]
    (τ : ℝ) (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ) :
    realField (oscillatorySum τ φ H) =
      QuadraticMean.sumDisplacement τ (fun i => coordinatePhase (φ i))
        (fun i => coordinateAmplitude (H i)) ∘ planeCoordinateIsometry := by
  funext x a
  simp only [realField, oscillatorySum, Finset.sum_apply, Complex.re_sum,
    QuadraticMean.sumDisplacement, Function.comp_apply, QuadraticMean.displacement,
    QuadraticMean.realMode, QuadraticMean.realPart, coordinatePhase, coordinateAmplitude,
    planeCoordinateIsometry.symm_apply_apply, Pi.smul_apply, smul_eq_mul, coordinate_phase_value]

lemma coordinate_quadratic_phase {ι : Type*} (φ : ι → Base → ℝ)
    (l : RealModes.QuadraticLabel ι) (x : SmallModes.Base) :
    quadraticFamilyPhase φ l (planeCoordinateIsometry.symm x) =
      RealModes.quadraticPhase (fun i => coordinatePhase (φ i)) l x := by
  rcases l with i | ⟨i,j,b⟩
  · rfl
  · cases b <;> rfl

theorem coordinate_quadratic_polynomial_expansion {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (φ : ι → Base → ℝ) (H : ι → Base → Fin 4 → ℂ)
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (hH : ∀ i, ContDiff ℝ ∞ (H i)) (τ t : ℝ) :
    let X := QuadraticMean.sumDisplacement τ (fun i => coordinatePhase (φ i))
      (fun i => coordinateAmplitude (H i))
    coordinateQuadraticPolynomial P ε G X t =
      coordinateQuadraticMean P ε G φ H τ t +
        fun p => ∑ l : RealModes.QuadraticLabel ι,
          QuadraticMean.displacement τ
            (RealModes.quadraticPhase (fun i => coordinatePhase (φ i)) l)
            (coordinateQuadraticCoefficient P ε G φ H τ t l) p := by
  dsimp only
  funext p k
  unfold coordinateQuadraticPolynomial
  rw [← real_oscillatorySum_coordinates τ φ H]
  rw [quadratic_zero_phase_expansion (P k) ε G φ H hφ hH τ t (planeCoordinateIsometry.symm p),
    quadraticOscillation_eq_family]
  simp only [Pi.add_apply, Finset.sum_apply, coordinateQuadraticMean]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  simp only [QuadraticMean.displacement, QuadraticMean.realMode, QuadraticMean.realPart,
    Pi.smul_apply, smul_eq_mul, coordinateQuadraticCoefficient]
  rw [← coordinate_quadratic_phase φ l p]
  exact congrArg Complex.re (congrArg (fun z : ℂ => z *
    quadraticFamilyCoefficient (P k) ε G φ H τ t l (planeCoordinateIsometry.symm p))
      (coordinate_phase_value τ (quadraticFamilyPhase φ l) (planeCoordinateIsometry.symm p))).symm

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
local instance coordinateFiberSpace_r10cde8_1 : NormedSpace ℝ TensorFiber := inferInstance
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
local instance symmetryModelComplete_r10cde8_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelSpace
local instance symmetryModelComplete_r10cde8_2 : CompleteSpace TensorFiber := inferInstance
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
local instance phaseFiberNormed_r10cde8_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance phaseFiberSpace_r10cde8_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance phaseDualAdd_r10cde8_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance phaseDualSmul_r10cde8_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance phaseSectionNormed_r10cde8_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance phaseSectionSpace_r10cde8_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
local instance chartReadSectionNormed_r10cde8_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance chartReadSectionSpace_r10cde8_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
local instance planeReadSectionSpace_r10cde8_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
local instance reconstructionFiberNormed_r10cde8_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance reconstructionFiberSpace_r10cde8_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance reconstructionDualSmul_r10cde8_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance reconstructionSectionNormed_r10cde8_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance reconstructionSectionSpace_r10cde8_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
local instance weightPlaneFiberNormed_r10cde8_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance weightPlaneFiberSpace_r10cde8_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance weightPlaneDualAdd_r10cde8_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance weightPlaneDualSmul_r10cde8_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance weightPlaneSectionNormed_r10cde8_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance weightPlaneSectionSpace_r10cde8_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasModeQuadraticExpansion
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The genuine quadratic polynomial of a global mode sum has the usual
mean and nonzero-phase expansion in each active chart. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem local_mode_polynomial_quadratic {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (i : A.centers)
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → JetPolynomial.Space)
    (τ : ℝ) (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ j, ContMDiff planeModel 𝓘(ℝ) ∞ (φ j))
    (hZ : ∀ j, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z j))
    {x : Base} (hx : A.chartWeight i x ≠ 0) :
    let φlocal := fun j => A.vectorChartRead i (φ j)
    let Zlocal := fun j => A.vectorChartRead i (Z j)
    coordinateQuadraticPolynomial P ε G
        (A.jetChartMap i (spaceCoordinates.symm ∘ ∑ j, surfaceMode τ (φ j) (Z j)) ∘
          planeCoordinateIsometry.symm) 0 (planeCoordinateIsometry x) =
      coordinateQuadraticMean P ε G φlocal Zlocal τ 0 (planeCoordinateIsometry x)+
        ∑ l : RealModes.QuadraticLabel ι,
          QuadraticMean.displacement τ
            (RealModes.quadraticPhase (fun j => coordinatePhase (φlocal j)) l)
            (coordinateQuadraticCoefficient P ε G φlocal Zlocal τ 0 l)
            (planeCoordinateIsometry x) := by
  dsimp only
  let V := QuadraticMean.sumDisplacement τ
    (fun j => coordinatePhase (A.vectorChartRead i (φ j)))
    (fun j => coordinateAmplitude (A.vectorChartRead i (Z j)))
  have hg :
      (A.jetChartMap i (spaceCoordinates.symm ∘ ∑ j, surfaceMode τ (φ j) (Z j)) ∘
        planeCoordinateIsometry.symm) ∘ planeCoordinateIsometry =ᶠ[𝓝 x]
          V ∘ planeCoordinateIsometry := by
    have hh := A.jetChartMap_modes_germ i τ φ Z hx
    simpa only [Function.comp_def,planeCoordinateIsometry.symm_apply_apply,V] using hh
  rw [coordinateQuadraticPolynomial_eq_of_eventuallyEq P ε G hg 0]
  exact congrFun (coordinate_quadratic_polynomial_expansion P ε G
    (fun j => A.vectorChartRead i (φ j)) (fun j => A.vectorChartRead i (Z j))
    (fun j => A.vectorChartRead_smooth i (hφ j))
    (fun j => A.vectorChartRead_smooth i (hZ j)) τ 0) (planeCoordinateIsometry x)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasModePolynomialQuadratic
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial part of the quadratic global mode interaction splits
into its zero-phase mean and all nonzero quadratic phases. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.modePolynomialDualAdd
local instance modePolynomialFiberNormed_r10cde8_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance modePolynomialFiberSpace_r10cde8_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance modePolynomialDualSmul_r10cde8_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance modePolynomialSectionNormed_r10cde8_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance modePolynomialSectionSpace_r10cde8_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem atlas_mode_polynomial_quadratic_oai {n : A.centers → ℕ} {m : ℕ}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (Q : A.centers → Fin 3 → Fin m → Expression)
    (hrep : A.PolynomialQuadraticRepresentation P Q)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F) (ε τ : ℝ)
    (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
    (hφ : ∀ j, ContMDiff planeModel 𝓘(ℝ) ∞ (φ j))
    (hZ : ∀ j, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z j)) :
    A.atlasPolynomialQuadratic P ε F
        (spaceCoordinates.symm ∘ ∑ j, surfaceMode τ (φ j) (Z j)) =
      A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 •
        coordinateQuadraticMean (Q i) ε (A.jetChartMap i F)
          (fun j => A.vectorChartRead i (φ j)) (fun j => A.vectorChartRead i (Z j)) τ 0 x)+
      A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 •
        ∑ l : RealModes.QuadraticLabel ι,
          QuadraticMean.displacement τ
            (RealModes.quadraticPhase (fun j => coordinatePhase (A.vectorChartRead i (φ j))) l)
            (coordinateQuadraticCoefficient (Q i) ε (A.jetChartMap i F)
              (fun j => A.vectorChartRead i (φ j)) (fun j => A.vectorChartRead i (Z j)) τ 0 l) x) := by
  let W : M → Space := spaceCoordinates.symm ∘ ∑ j, surfaceMode τ (φ j) (Z j)
  have hsum : ContMDiff planeModel 𝓘(ℝ,RealModes.RVec 4) ∞
      (∑ j, surfaceMode τ (φ j) (Z j)) := by
    convert ContMDiff.sum (t := Finset.univ) (fun j _ => surfaceMode_smooth τ (hφ j) (hZ j)) using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    simp only [Finset.sum_apply]
  have hW : ContMDiff planeModel spaceModel ∞ W :=
    spaceCoordinates.symm.contDiff.contMDiff.comp hsum
  have hsym : ∀ p v w, A.atlasPolynomialQuadratic P ε F W p v w =
      A.atlasPolynomialQuadratic P ε F W p w v := A.tensorPlaneRestore_symmetric _
  change A.atlasPolynomialQuadratic P ε F W = _
  rw [← A.tensorPlaneRestore_encode (A.atlasPolynomialQuadratic P ε F W) hsym,
    ← A.tensorPlaneRestore_add]
  congr 1
  funext i y
  rw [A.tensorPlaneEncode_weight]
  by_cases hz : A.planeWeight i y = 0
  · simp only [hz,zero_pow (by decide : 2 ≠ 0),zero_smul,Pi.add_apply,zero_add]
  · have hx : A.chartWeight i (planeCoordinateIsometry.symm y) ≠ 0 := hz
    have hs : planeCoordinateIsometry.symm y ∈ (A.chartWeightCompact i : Set Base) := by
      rw [← A.chartWeight_tsupport i]
      exact subset_tsupport (A.chartWeight i) hx
    have hr := hrep F W hF hW i (planeCoordinateIsometry.symm y) hs ε
    simp only [planeCoordinateIsometry.apply_symm_apply] at hr
    have he := A.local_mode_polynomial_quadratic i (Q i) ε (A.jetChartMap i F)
      τ φ Z hφ hZ hx
    simp only [planeCoordinateIsometry.apply_symm_apply] at he
    change (A.planeWeight i y)^2 • A.tensorChartRead i (A.atlasPolynomialQuadratic P ε F W)
      (planeCoordinateIsometry.symm y) = _
    rw [← hr,he,smul_add]
    rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_mode_polynomial_quadratic_oai.{u_1, u_2} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_mode_polynomial_quadratic_oai.{u_1, u_2}
