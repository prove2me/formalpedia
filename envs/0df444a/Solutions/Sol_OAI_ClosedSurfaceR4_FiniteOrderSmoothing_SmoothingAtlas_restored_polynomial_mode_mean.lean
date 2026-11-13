-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.restored_polynomial_mode_mean
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:34:59.104195+00:00
-- url     : https://prove2.me/submissions/b09aeaad-35b6-4e8b-a7c2-24bb1e6478eb

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
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_polynomial_mode_quadrature

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ForcedSolve
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (displacement)
open Set Filter

lemma contDiffOn_displacement {n : ℕ} {U : Set Base} {φ : Base → ℝ} {Z : Field n}
    (hφ : ContDiffOn ℝ ∞ φ U) (hZ : ContDiffOn ℝ ∞ Z U) (τ : ℝ) :
    ContDiffOn ℝ ∞ (displacement τ φ Z) U := by
  have he : ContDiffOn ℝ ∞ (fun p => QuadraticMean.phase (φ p / τ)) U := by
    exact ((Complex.ofRealCLM.contDiff.comp_contDiffOn
      (hφ.div_const τ)).mul contDiffOn_const).cexp
  exact (QuadraticMean.realPartCLM n).contDiff.comp_contDiffOn (he.smul hZ)



end ClosedSurfaceR4.RealModes

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
local instance coordinateFiberSpace_r68df98_1 : NormedSpace ℝ TensorFiber := inferInstance
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
local instance symmetryModelComplete_r68df98_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelSpace
local instance symmetryModelComplete_r68df98_2 : CompleteSpace TensorFiber := inferInstance
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
local instance phaseFiberNormed_r68df98_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance phaseFiberSpace_r68df98_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance phaseDualAdd_r68df98_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance phaseDualSmul_r68df98_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance phaseSectionNormed_r68df98_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance phaseSectionSpace_r68df98_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
local instance chartReadSectionNormed_r68df98_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance chartReadSectionSpace_r68df98_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorChartRead_on_weight (i : A.centers) (u : ∀ x : M, CovariantTwoTensor x)
    {p : M} (hp : p ∈ tsupport (A.weight i)) :
    A.tensorChartRead i u (chart (i : M) p) = fiberToThree (A.bundleComponent A.tensorTriv i u p) := by
  change fiberToThree (localize (i : M) (A.outer i)
    (A.bundleComponent A.tensorTriv i u) (chart (i : M) p)) = _
  rw [localize_chart _ _ _ (A.weight_support i hp), A.outer_one i p hp]
  simp only [one_pow, one_smul]

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
local instance planeReadSectionSpace_r68df98_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedAtlasRestore
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A displacement supported on an atlas weight's compact support is
restored exactly in that chart; the outer cutoff introduces no jet error. -/
noncomputable section
open Set
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Manifold
open JetPolynomial JetPolynomial.Perturbation
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma mem_weight_support_of_plane (i : A.centers) {p : M} (hp : p ∈ (chart (i : M)).source)
    (h : planeCoordinateIsometry (chart (i : M) p) ∈
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) : p ∈ tsupport (A.weight i) := by
  obtain ⟨y,hy,he⟩ := h
  have hyEq : y = chart (i : M) p := planeCoordinateIsometry.injective he
  subst y
  obtain ⟨q,hq,hqp⟩ := hy
  have hqEq : q = p := (chart (i : M)).injOn (A.weight_support i hq) hp hqp
  rwa [hqEq] at hq

lemma restore_plane_on_source (i : A.centers) (f : SmallModes.Base → V)
    (hf : tsupport f ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    {p : M} (hp : p ∈ (chart (i : M)).source) :
    restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry) p =
      f (planeCoordinateIsometry (chart (i : M) p)) := by
  rw [restore,indicator_of_mem hp]
  change A.outer i p • f (planeCoordinateIsometry (chart (i : M) p)) = _
  by_cases hz : f (planeCoordinateIsometry (chart (i : M) p)) = 0
  · rw [hz,smul_zero]
  · rw [A.outer_one i p (A.mem_weight_support_of_plane i hp (hf (subset_tsupport f hz))),one_smul]

lemma restore_plane_in_coordinates (i : A.centers) (f : SmallModes.Base → V)
    (hf : tsupport f ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    {x : JetPolynomial.Base} (hx : x ∈ (chart (i : M)).target) :
    restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry) ((chart (i : M)).symm x) =
      f (planeCoordinateIsometry x) := by
  rw [A.restore_plane_on_source i f hf ((chart (i : M)).map_target hx),(chart (i : M)).right_inv hx]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedAtlasDifferential
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Supported restoration commutes with all local derivatives, including
its actual manifold differential, and preserves the original atlas support. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma restore_plane_tsupport (i : A.centers) (f : SmallModes.Base → V)
    (hf : tsupport f ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    tsupport (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry)) ⊆
      tsupport (A.weight i) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro p hp
  by_cases hs : p ∈ (chart (i : M)).source
  · apply A.mem_weight_support_of_plane i hs
    apply hf
    apply subset_tsupport f
    intro hz
    apply hp
    rw [A.restore_plane_on_source i f hf hs,hz]
  · exfalso
    apply hp
    simp only [restore,indicator_of_notMem hs]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialSupport
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global polynomial variation is local in its varying field.
In particular, restoring the polynomial does not enlarge that support. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
local instance polynomialSupportFiberNormed_r68df98_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialSupportFiberSpace_r68df98_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance polynomialSupportDualAdd_r68df98_1 : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialSupportDualSmul_r68df98_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance polynomialSupportSectionNormed_r68df98_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialSupportSectionSpace_r68df98_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma jetChartMap_eventually_zero (i : A.centers) {X : M → Space} {p : M}
    (hp : p ∈ (chart (i : M)).source) (hX : X =ᶠ[𝓝 p] 0) :
    A.jetChartMap i X =ᶠ[𝓝 (chart (i : M) p)] 0 := by
  have ht := (chart (i : M)).map_source hp
  have hc : Tendsto (chart (i : M)).symm (𝓝 (chart (i : M) p)) (𝓝 p) := by
    simpa only [(chart (i : M)).left_inv hp] using
      ((chart (i : M)).continuousAt_symm ht).tendsto
  have he := hX.comp_tendsto hc
  filter_upwards [he,(chart (i : M)).open_target.mem_nhds ht] with y hy hyt
  change X ((chart (i : M)).symm y) = 0 at hy
  change spaceCoordinates (localize (i : M) (A.outer i) X y) = 0
  simp only [localize,indicator_of_mem hyt,hy,smul_zero,map_zero]

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

lemma realMode_zero {n : ℕ} (θ : ℝ) : realMode θ (0 : Fin n → ℂ) = 0 := by
  change realPartCLM n (QuadraticMean.phase θ • (0 : Fin n → ℂ)) = 0
  rw [smul_zero,map_zero]

lemma surfaceMode_tsupport {X : Type*} [TopologicalSpace X] {n : ℕ}
    (τ : ℝ) (φ : X → ℝ) (Z : X → Fin n → ℂ) :
    tsupport (surfaceMode τ φ Z) ⊆ tsupport Z := by
  apply closure_mono
  intro x hx
  change Z x ≠ 0
  intro hz
  exact hx (by simp only [surfaceMode,hz,realMode_zero])

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

variable [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma restore_displacement {n : ℕ} (i : A.centers) (τ : ℝ)
    (φ : SmallModes.Base → ℝ) (Z : SmallModes.Base → Fin n → ℂ)
    (hZ : tsupport Z ⊆ (JetPolynomial.Perturbation.modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    restore (i : M) (A.outer i) (QuadraticMean.displacement τ φ Z ∘ planeCoordinateIsometry) =
      surfaceMode τ (restore (i : M) (A.outer i) (φ ∘ planeCoordinateIsometry))
        (restore (i : M) (A.outer i) (Z ∘ planeCoordinateIsometry)) := by
  funext p
  by_cases hp : p ∈ (chart (i : M)).source
  · simp only [restore,indicator_of_mem hp,Function.comp_apply,surfaceMode,
      QuadraticMean.displacement]
    by_cases hz : Z (planeCoordinateIsometry (chart (i : M) p)) = 0
    · simp only [hz,realMode_zero,smul_zero]
    · rw [A.outer_one i p (A.mem_weight_support_of_plane i hp (hZ (subset_tsupport Z hz))),
        one_smul,one_smul,one_smul]
  · simp only [restore,indicator_of_notMem hp,surfaceMode,realMode_zero]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasSupportedPolynomialVariation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The variation of a globally defined polynomial in a chart-supported
direction is the restoration of that chart's actual local linearization. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.supportedVariationDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.supportedVariationFiberSpace
local instance supportedVariationDualSmul_r68df98_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.supportedVariationFiberNormed
local instance supportedVariationSectionNormed_r68df98_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance supportedVariationSectionSpace_r68df98_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma restore_chart_read_on_weight (i : A.centers) (u : ∀ p : M, CovariantTwoTensor p)
    {p : M} (hp : p ∈ tsupport (A.weight i)) (hu : ∀ v w, u p v w = u p w v) :
    A.bundleRestore A.tensorTriv i (fun x => fiberFromThree (A.tensorChartRead i u x)) p = u p := by
  have hsource := A.weight_support i hp
  have hc : ∀ v w, A.bundleComponent A.tensorTriv i u p v w =
      A.bundleComponent A.tensorTriv i u p w v := by
    intro v w
    rw [A.tensorComponent_apply i u hsource,A.tensorComponent_apply i u hsource]
    exact hu _ _
  change A.outer i p • (A.tensorTriv i).symmL ℝ p
    (fiberFromThree (A.tensorChartRead i u (chart (i : M) p))) = _
  rw [A.tensorChartRead_on_weight i u hp,fiberFromThree_toThree _ hc,
    A.outer_one i p hp,one_smul]
  exact (A.tensorTriv i).symmL_continuousLinearMapAt (A.tensorTriv_domain i hsource) _

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasRestoredPolynomialDirection
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A supported Euclidean field is restored with exactly its original
localized jet, so the local polynomial solver acts on the actual direction. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredDirectionDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredDirectionFiberSpace
local instance restoredDirectionDualSmul_r68df98_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredDirectionFiberNormed
local instance restoredDirectionSectionNormed_r68df98_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance restoredDirectionSectionSpace_r68df98_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma jetChartMap_restored_direction (i : A.centers) (X : RealModes.RField 4)
    (hX : tsupport X ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    A.jetChartMap i (restore (i : M) (A.outer i)
      ((spaceCoordinates.symm ∘ X) ∘ planeCoordinateIsometry)) = X ∘ planeCoordinateIsometry := by
  have hsp := (tsupport_comp_subset (g := spaceCoordinates.symm) (map_zero _) X).trans hX
  funext x
  by_cases hx : x ∈ (chart (i : M)).target
  · change spaceCoordinates (localize (i : M) (A.outer i)
      (restore (i : M) (A.outer i) ((spaceCoordinates.symm ∘ X) ∘ planeCoordinateIsometry)) x) = _
    rw [localize,indicator_of_mem hx,A.restore_plane_in_coordinates i _ hsp hx]
    simp only [Function.comp_apply,map_smul,ContinuousLinearEquiv.apply_symm_apply]
    by_cases hz : X (planeCoordinateIsometry x) = 0
    · rw [hz,smul_zero]
    · have hp : (chart (i : M)).symm x ∈ tsupport (A.weight i) := by
        apply A.mem_weight_support_of_plane i ((chart (i : M)).map_target hx)
        rw [(chart (i : M)).right_inv hx]
        exact hX (subset_tsupport X hz)
      rw [A.outer_one i _ hp,one_pow,one_smul]
  · have hz : X (planeCoordinateIsometry x) = 0 := by
      by_contra hn
      obtain ⟨y,hy,he⟩ := hX (subset_tsupport X hn)
      have hyx : y = x := planeCoordinateIsometry.injective he
      subst y
      obtain ⟨p,hp,rfl⟩ := hy
      exact hx ((chart (i : M)).map_source (A.weight_support i hp))
    change spaceCoordinates (localize (i : M) (A.outer i) _ x) = _
    rw [localize,indicator_of_notMem hx,map_zero]
    exact hz.symm

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasSupportedPolynomialQuadratic
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]


attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticSupportDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticSupportFiberSpace
local instance quadraticSupportDualSmul_r68df98_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
/-- A quadratic variation vanishes wherever its varying field vanishes as a germ. -/
lemma second_variation_zero_of_notMem (e : Expression) (G : Base → JetPolynomial.Space)
    {H : Base → JetPolynomial.Space} {p : Base} (hp : p ∉ tsupport H) (t : ℝ) :
    (e.variations 1).eval ![G,H,H,0] (p,t) = 0 := by
  let J : DirectionJets := fun w a p => (jet H w a p : ℂ)
  have hz : quadraticComplex e G J J (p,t) = 0 := by
    apply quadraticComplex_zero_at
    intro w a
    change (jet H w a p : ℂ) = 0
    rw [image_eq_zero_of_notMem_tsupport (fun h => hp (tsupport_jet H w a h))]
    rfl
  have he := quadraticComplex_real_fields e G H H (p,t)
  rw [show quadraticComplex e G (fun w a p => (jet H w a p : ℂ))
    (fun w a p => (jet H w a p : ℂ)) (p,t) = 0 from hz] at he
  exact Complex.ofReal_eq_zero.mp he.symm

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticSupportDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticSupportFiberSpace
local instance quadraticSupportDualSmul_r68df98_2 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticSupportFiberNormed
local instance quadraticSupportSectionNormed_r68df98_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance quadraticSupportSectionSpace_r68df98_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma atlasPolynomialQuadratic_zero_of_notMem {n : A.centers → ℕ}
    (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression) (ε : ℝ)
    (F X : M → Space) {p : M} (hp : p ∉ tsupport X) :
    A.atlasPolynomialQuadratic P ε F X p = 0 := by
  classical
  unfold atlasPolynomialQuadratic tensorPlaneRestore
  apply Finset.sum_eq_zero
  intro i _
  by_cases ho : A.outer i p = 0
  · simp only [bundleRestore,ho,zero_smul]
  · have hps := A.outer_support i (subset_tsupport (A.outer i) ho)
    have hz := A.jetChartMap_eventually_zero i hps (notMem_tsupport_iff_eventuallyEq.mp hp)
    have hn : chart (i : M) p ∉ tsupport (A.jetChartMap i X) :=
      notMem_tsupport_iff_eventuallyEq.mpr hz
    have hcomp : (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) ∘
        planeCoordinateIsometry = A.jetChartMap i X := by
      funext y
      simp only [Function.comp_apply,planeCoordinateIsometry.symm_apply_apply]
    have he : coordinateQuadraticPolynomial (P i) ε (A.jetChartMap i F)
        (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0
        (planeCoordinateIsometry (chart (i : M) p)) = 0 := by
      funext k
      simp only [coordinateQuadraticPolynomial,hcomp,
        planeCoordinateIsometry.symm_apply_apply,Pi.zero_apply]
      apply Finset.sum_eq_zero
      intro l _
      rw [second_variation_zero_of_notMem (P i k l) (A.jetChartMap i F) hn 0,mul_zero,mul_zero]
    simp only [bundleRestore,he,map_zero,smul_zero]


theorem supported_polynomial_quadratic {n : A.centers → ℕ} {m : ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (i : A.centers) (Q : Fin 3 → Fin m → Expression)
    (F X : M → Space)
    (hsp : tsupport X ⊆ tsupport (A.weight i)) (ε : ℝ)
    (hread : ∀ x ∈ (A.chartWeightCompact i : Set Base),
      coordinateQuadraticPolynomial Q ε (A.jetChartMap i F)
          (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0 (planeCoordinateIsometry x) =
        A.tensorChartRead i (A.atlasPolynomialQuadratic P ε F X) x) :
    A.atlasPolynomialQuadratic P ε F X = A.bundleRestore A.tensorTriv i
      (fun x => fiberFromThree (coordinateQuadraticPolynomial Q ε (A.jetChartMap i F)
        (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0 (planeCoordinateIsometry x))) := by
  funext p
  by_cases hp : p ∈ tsupport (A.weight i)
  · have he := A.restore_chart_read_on_weight i (A.atlasPolynomialQuadratic P ε F X) hp
      (A.tensorPlaneRestore_symmetric _ p)
    have hr := hread (chart (i : M) p) ⟨p,hp,rfl⟩
    change _ = A.outer i p • (A.tensorTriv i).symmL ℝ p (fiberFromThree _)
    rw [hr]
    exact he.symm
  · have hX : p ∉ tsupport X := fun hx => hp (hsp hx)
    rw [A.atlasPolynomialQuadratic_zero_of_notMem P ε F X hX]
    by_cases ho : A.outer i p = 0
    · simp only [bundleRestore,ho,zero_smul]
    · have hsource := A.outer_support i (subset_tsupport (A.outer i) ho)
      have hn : chart (i : M) p ∉ tsupport (A.jetChartMap i X) :=
        notMem_tsupport_iff_eventuallyEq.mpr
          (A.jetChartMap_eventually_zero i hsource (notMem_tsupport_iff_eventuallyEq.mp hX))
      have hcomp : (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) ∘
          planeCoordinateIsometry = A.jetChartMap i X := by
        funext y
        simp only [Function.comp_apply,planeCoordinateIsometry.symm_apply_apply]
      have hz : coordinateQuadraticPolynomial Q ε (A.jetChartMap i F)
          (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0
          (planeCoordinateIsometry (chart (i : M) p)) = 0 := by
        funext k
        simp only [coordinateQuadraticPolynomial,hcomp,
          planeCoordinateIsometry.symm_apply_apply,Pi.zero_apply]
        apply Finset.sum_eq_zero
        intro l _
        rw [second_variation_zero_of_notMem (Q k l) (A.jetChartMap i F) hn 0,mul_zero,mul_zero]
      simp only [bundleRestore,hz,map_zero,smul_zero]


theorem restored_polynomial_quadratic {n : A.centers → ℕ} {m : ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (i : A.centers) (Q : Fin 3 → Fin m → Expression)
    (F : M → Space) (X : RealModes.RField 4)
    (hsp : tsupport X ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) (ε : ℝ)
    (hread : ∀ x ∈ (A.chartWeightCompact i : Set Base),
      coordinateQuadraticPolynomial Q ε (A.jetChartMap i F) X 0 (planeCoordinateIsometry x) =
        A.tensorChartRead i (A.atlasPolynomialQuadratic P ε F
          (restore (i : M) (A.outer i) ((spaceCoordinates.symm ∘ X) ∘ planeCoordinateIsometry))) x) :
    A.atlasPolynomialQuadratic P ε F
      (restore (i : M) (A.outer i) ((spaceCoordinates.symm ∘ X) ∘ planeCoordinateIsometry)) =
      A.bundleRestore A.tensorTriv i (fun x => fiberFromThree
        (coordinateQuadraticPolynomial Q ε (A.jetChartMap i F) X 0 (planeCoordinateIsometry x))) := by
  have hs := A.restore_plane_tsupport i (spaceCoordinates.symm ∘ X)
    ((tsupport_comp_subset (g := spaceCoordinates.symm) (map_zero _) X).trans hsp)
  have he : A.jetChartMap i (restore (i : M) (A.outer i)
      ((spaceCoordinates.symm ∘ X) ∘ planeCoordinateIsometry)) ∘ planeCoordinateIsometry.symm = X := by
    rw [A.jetChartMap_restored_direction i X hsp]
    funext y
    simp only [Function.comp_apply,planeCoordinateIsometry.apply_symm_apply]
  have hh := A.supported_polynomial_quadratic P i Q F
    (restore (i : M) (A.outer i) ((spaceCoordinates.symm ∘ X) ∘ planeCoordinateIsometry)) hs ε
  simpa only [he] using hh (by simpa only [he] using hread)


end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_RestoredPolynomialModeMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredPolynomialMeanDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredPolynomialMeanFiberSpace
local instance restoredPolynomialMeanDualSmul_r68df98_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)




attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredPolynomialMeanFiberNormed
local instance restoredPolynomialMeanSectionNormed_r68df98_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance restoredPolynomialMeanSectionSpace_r68df98_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma real_restored_polynomial_quadratic {n : A.centers → ℕ} {m : ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (Q : A.centers → Fin 3 → Fin m → Expression)
    (hrep : A.PolynomialQuadraticRepresentation P Q)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F) (ε : ℝ)
    (i : A.centers) (X : RealModes.RField 4) (hX : ContDiff ℝ ∞ X)
    (hsp : tsupport X ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    A.atlasPolynomialQuadratic P ε F
      (spaceCoordinates.symm ∘ restore (i : M) (A.outer i) (X ∘ planeCoordinateIsometry)) =
      A.bundleRestore A.tensorTriv i (fun x => fiberFromThree
        (coordinateQuadraticPolynomial (Q i) ε (A.jetChartMap i F) X 0
          (planeCoordinateIsometry x))) := by
  let W := restore (i : M) (A.outer i)
    ((spaceCoordinates.symm ∘ X) ∘ planeCoordinateIsometry)
  have hW : ContMDiff planeModel spaceModel ∞ W := restore_smooth (i : M)
    (A.outer_smooth i) (A.outer_support i)
    ((spaceCoordinates.symm.contDiff.comp hX).comp planeCoordinateIsometry.contDiff)
  have he : W = spaceCoordinates.symm ∘
      restore (i : M) (A.outer i) (X ∘ planeCoordinateIsometry) := by
    funext p
    by_cases hp : p ∈ (chart (i : M)).source <;>
      simp [W,restore,hp,Function.comp_apply,map_smul]
  have hj : A.jetChartMap i W ∘ planeCoordinateIsometry.symm = X := by
    rw [A.jetChartMap_restored_direction i X hsp]
    funext x
    simp only [Function.comp_apply,planeCoordinateIsometry.apply_symm_apply]
  rw [← he]
  apply A.restored_polynomial_quadratic P i (Q i) F X hsp ε
  intro x hx
  have hr := hrep F W hF hW i x hx ε
  simpa only [hj] using hr

theorem restored_polynomial_mode_mean_oai {n : A.centers → ℕ} {m : ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (Q : A.centers → Fin 3 → Fin m → Expression)
    (hrep : A.PolynomialQuadraticRepresentation P Q)
    (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F) (ε τ : ℝ)
    (i : A.centers) (φ : SmallModes.Base → ℝ) (Z : SmallModes.Base → Fin 4 → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hZ : ContDiff ℝ ∞ Z)
    (hs : tsupport Z ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    let Φ := restore (i : M) (A.outer i) (φ ∘ planeCoordinateIsometry)
    let W := restore (i : M) (A.outer i) (Z ∘ planeCoordinateIsometry)
    A.polynomialModeMean Q F ε τ Φ W =
      A.bundleRestore A.tensorTriv i (fun y => fiberFromThree
        (fun k => quadraticMeanCoefficient (Q i k) ε (A.jetChartMap i F)
          (φ ∘ planeCoordinateIsometry) (Z ∘ planeCoordinateIsometry) τ 0 y)) := by
  dsimp only
  let Φ := restore (i : M) (A.outer i) (φ ∘ planeCoordinateIsometry)
  let W := restore (i : M) (A.outer i) (Z ∘ planeCoordinateIsometry)
  let ZI := fun x => Complex.I • Z x
  have hΦ : ContMDiff planeModel 𝓘(ℝ) ∞ Φ := restore_smooth (i : M)
    (A.outer_smooth i) (A.outer_support i) (hφ.comp planeCoordinateIsometry.contDiff)
  have hW : ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ W := restore_smooth (i : M)
    (A.outer_smooth i) (A.outer_support i) (hZ.comp planeCoordinateIsometry.contDiff)
  have hZI : ContDiff ℝ ∞ ZI := (contDiff_const (c := Complex.I)).smul hZ
  have hsI : tsupport ZI ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) :=
    (tsupport_smul_subset_right (fun _ => Complex.I) Z).trans hs
  have hWI : (fun p => Complex.I • W p) =
      restore (i : M) (A.outer i) (ZI ∘ planeCoordinateIsometry) := by
    funext p
    by_cases hp : p ∈ (chart (i : M)).source
    · simp only [W,ZI,restore,indicator_of_mem hp,Function.comp_apply]
      exact smul_comm _ _ _
    · simp only [W,restore,indicator_of_notMem hp,smul_zero]
  have hdisp := contDiffOn_univ.mp (RealModes.contDiffOn_displacement hφ.contDiffOn hZ.contDiffOn τ)
  have hdispI := contDiffOn_univ.mp (RealModes.contDiffOn_displacement hφ.contDiffOn hZI.contDiffOn τ)
  have hsdisp := (surfaceMode_tsupport τ φ Z).trans hs
  have hsdispI := (surfaceMode_tsupport τ φ ZI).trans hsI
  have he := A.polynomial_mode_quadrature P Q hrep F hF ε τ Φ W hΦ hW
  rw [hWI,← A.restore_displacement i τ φ Z hs,← A.restore_displacement i τ φ ZI hsI,
    A.real_restored_polynomial_quadratic P Q hrep F hF ε i _ hdisp hsdisp,
    A.real_restored_polynomial_quadratic P Q hrep F hF ε i _ hdispI hsdispI] at he
  have hc :
      (fun y => fiberFromThree (coordinateQuadraticPolynomial (Q i) ε (A.jetChartMap i F)
        (QuadraticMean.displacement τ φ Z) 0 (planeCoordinateIsometry y)))+
      (fun y => fiberFromThree (coordinateQuadraticPolynomial (Q i) ε (A.jetChartMap i F)
        (QuadraticMean.displacement τ φ ZI) 0 (planeCoordinateIsometry y))) =
      (2 : ℝ) • (fun y => fiberFromThree (fun k =>
        quadraticMeanCoefficient (Q i k) ε (A.jetChartMap i F)
          (φ ∘ planeCoordinateIsometry) (Z ∘ planeCoordinateIsometry) τ 0 y)) := by
    have hq := coordinate_polynomial_quadrature (Q i) ε (A.jetChartMap i F)
      (hφ.comp planeCoordinateIsometry.contDiff) (hZ.comp planeCoordinateIsometry.contDiff) τ 0
    have hφback : coordinatePhase (φ ∘ planeCoordinateIsometry) = φ := by
      funext x
      simp only [coordinatePhase,Function.comp_apply,planeCoordinateIsometry.apply_symm_apply]
    have hZback : coordinateAmplitude (Z ∘ planeCoordinateIsometry) = Z := by
      funext x
      simp only [coordinateAmplitude,Function.comp_apply,planeCoordinateIsometry.apply_symm_apply]
    have hZIback : coordinateAmplitude (fun p => Complex.I • (Z ∘ planeCoordinateIsometry) p) = ZI := by
      funext x
      simp only [coordinateAmplitude,Function.comp_apply,planeCoordinateIsometry.apply_symm_apply,ZI]
    rw [hφback,hZback,hZIback] at hq
    funext y
    change fiberFromThree _ + fiberFromThree _ = (2 : ℝ) • fiberFromThree _
    rw [← map_add]
    have hh := congrFun hq (planeCoordinateIsometry y)
    simp only [Pi.add_apply,Pi.smul_apply,planeCoordinateIsometry.symm_apply_apply] at hh
    rw [hh,map_smul]
  rw [← A.bundleRestore_add,hc,A.bundleRestore_smul] at he
  have hh := congrArg (fun X => (1/2 : ℝ) • X) he
  simpa only [smul_smul,show (1/2 : ℝ)*2 = 1 by norm_num,one_smul] using hh.symm

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.restored_polynomial_mode_mean_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.restored_polynomial_mode_mean_oai.{u_1}
