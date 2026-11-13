-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.full_linearized_representatives
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:36:47.325523+00:00
-- url     : https://prove2.me/submissions/e8211b57-b53e-4cb0-9f10-faab86051f6f

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
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_atlas_polynomial_representation_on_support
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_restored_polynomial_direction

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricTensors
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
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.PhaseMean (firstDirection secondDirection)

lemma realLinearizedTensor_apply {n : ℕ} (F U : RField n) (p : Base) (i : Fin 3) :
    realLinearizedTensor F U p i = realLinearized F U (firstDirection i) (secondDirection i) p := by
  fin_cases i <;> rfl

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_TensorCoordinates
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
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.PhaseMean

lemma evaluate_realLinearizedTensor {n : ℕ} (F X : RField n) (p v w : Base) :
    evaluate (realLinearizedTensor F X p) v w = realLinearized F X v w p := by
  simp only [realLinearized, derivative_base_decomposition F p v,
    derivative_base_decomposition F p w, derivative_base_decomposition X p v,
    derivative_base_decomposition X p w]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  unfold evaluate
  simp only [realLinearizedTensor_apply, firstDirection, secondDirection, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, realLinearized]
  ring



end ClosedSurfaceR4.RealModes

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

lemma localize_smul (p : M) (ψ : M → ℝ) (a : ℝ) (f : M → V) :
    localize p ψ (a • f) = a • localize p ψ f := by
  funext x
  by_cases hx : x ∈ (chart p).target <;> simp [localize, hx, smul_smul, mul_comm]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_JetVariations
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual variations of the ordered coordinate jets. The position entries
do not vary, and a second-jet variation costs at most two short-scale powers. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma lowJet_affine {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (t : ℝ) (p : Base) :
    lowJet (fun q => G q + t • H q) p = lowJet G p + t • variationLowJet H p := by
  funext i
  cases i with
  | inl i => simp [lowJet, variationLowJet]
  | inr i =>
    change jet (fun q => G q + t • H q) (lowWord i.1) i.2 p = _
    rw [jet_add (H := fun q => t • H q) hG (ContDiff.const_smul t hH), jet_smul hH]
    rfl

lemma lowJet_affine_hasDerivAt {G H : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (p : Base) (t : ℝ) :
    HasDerivAt (fun s : ℝ => lowJet (fun q => G q + s • H q) p) (variationLowJet H p) t := by
  have he : (fun s : ℝ => lowJet (fun q => G q + s • H q) p) =
      (fun s : ℝ => lowJet G p + s • variationLowJet H p) :=
    funext (fun s => lowJet_affine hG hH s p)
  rw [he]
  simpa only [one_smul, id_eq] using
    ((hasDerivAt_id t).smul_const (variationLowJet H p)).const_add (lowJet G p)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialVariation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first variation of an actual higher-jet polynomial, including the
variation of its smooth second-jet coefficients. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.Expression
open WeightedEstimates

theorem variation_hasDerivAt {O : Set LowJet} (hO : IsOpen O)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    {e : Expression} (he : e.SmoothCoeffs O) (z : Base × ℝ)
    (hQ : lowJet G z.1 ∈ O) :
    HasDerivAt (fun s : ℝ => e.eval (fun p => G p + s • H p) z) (e.variation G H z) 0 := by
  induction e with
  | coeff c =>
    have hmem : (lowJet G z.1, z.2) ∈ O ×ˢ Set.univ := ⟨hQ, Set.mem_univ z.2⟩
    have hc : DifferentiableAt ℝ c (lowJet G z.1, z.2) :=
      (he.contDiffAt ((hO.prod isOpen_univ).mem_nhds hmem)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    have hj := (lowJet_affine_hasDerivAt hG hH z.1 0).prodMk (hasDerivAt_const 0 z.2)
    have hd := hc.hasFDerivAt.comp_hasDerivAt_of_eq 0 hj (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    simpa only [Function.comp_def, zero_smul, add_zero, eval, variation] using hd
  | atom w a e ih =>
    have hj : HasDerivAt (fun s : ℝ => jet (fun p => G p + s • H p) w a z.1)
        (jet H w a z.1) 0 := by
      have hpath : (fun s : ℝ => jet (fun p => G p + s • H p) w a z.1) =
          (fun s : ℝ => jet G w a z.1 + s * jet H w a z.1) := by
        funext s
        rw [jet_add (H := fun p => s • H p) hG (ContDiff.const_smul s hH), jet_smul hH]
      rw [hpath]
      simpa only [one_mul, id_eq] using
        ((hasDerivAt_id (0 : ℝ)).mul_const (jet H w a z.1)).const_add (jet G w a z.1)
    have hzero : (fun p => G p + (0 : ℝ) • H p) = G := by funext p; simp
    simpa only [eval, variation, hzero, Pi.mul_apply] using hj.fun_mul (ih he)
  | add e f ihe ihf =>
    exact (ihe he.1).add (ihf he.2)

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_MixedJetPolynomial
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomials in the base-map jet and three independent variation jets.
Differentiating the base map increases the scale loss by at most two. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial

namespace MixedExpression

lemma ofExpression_eval (e : Expression) (G : Fin 4 → Base → Space) (z : Base × ℝ) :
    (ofExpression e).eval G z = e.eval (G 0) z := by
  induction e with
  | coeff => rfl
  | atom _ _ _ ih => simp only [ofExpression, eval, Expression.eval, ih]
  | add _ _ ihe ihf => simp only [ofExpression, eval, Expression.eval, ihe, ihf]

end MixedExpression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MixedJetCalculus
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coefficient part of the mixed polynomial variation is the actual
low-jet chain rule, with the position coordinates held fixed. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial

lemma variationLowJet_expansion (H : Base → Space) (p : Base) :
    variationLowJet H p = ∑ i : Fin 7 × Fin 4,
      jet H (lowWord i.1) i.2 p • lowBasis (.inr i) := by
  funext k
  cases k with
  | inl k => simp [variationLowJet, lowBasis]
  | inr k => simp [variationLowJet, lowBasis, Pi.single_apply]

lemma coefficient_variation_sum (c : LowJet × ℝ → ℝ) (G H : Base → Space) (z : Base × ℝ) :
    fderiv ℝ c (lowJet G z.1, z.2) (variationLowJet H z.1, 0) =
      ∑ i : Fin 7 × Fin 4, jet H (lowWord i.1) i.2 z.1 *
        fderiv ℝ c (lowJet G z.1, z.2) (lowBasis (.inr i), 0) := by
  let L : LowJet →L[ℝ] ℝ :=
    (fderiv ℝ c (lowJet G z.1, z.2)).comp (ContinuousLinearMap.inl ℝ LowJet ℝ)
  change L (variationLowJet H z.1) = _
  rw [variationLowJet_expansion, map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

namespace MixedExpression

lemma sumList_eval {ι : Type*} (l : List ι) (f : ι → MixedExpression)
    (G : Fin 4 → Base → Space) (z : Base × ℝ) :
    (sumList l f).eval G z = (l.map (fun i => (f i).eval G z)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [sumList, eval, List.map_cons, List.sum_cons, ih]

lemma differentiate_coeff_eval (c : LowJet × ℝ → ℝ) (j : Fin 3)
    (G : Fin 4 → Base → Space) (z : Base × ℝ) :
    ((coeff c).differentiate j).eval G z =
      fderiv ℝ c (lowJet (G 0) z.1, z.2) (variationLowJet (G j.succ) z.1, 0) := by
  rw [coefficient_variation_sum]
  simp only [differentiate, sumList_eval, eval, coefficientDerivative]
  exact Finset.sum_map_toList _ _

end MixedExpression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MixedJetDerivatives
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual differentiation of mixed jet polynomials in the base-map slot. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial

lemma jet_affine_hasDerivAt {G H : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (w : List (Fin 2)) (a : Fin 4) (p : Base) (t : ℝ) :
    HasDerivAt (fun s : ℝ => jet (fun q => G q + s • H q) w a p)
      (jet H w a p) t := by
  have hpath : (fun s : ℝ => jet (fun q => G q + s • H q) w a p) =
      (fun s : ℝ => jet G w a p + s * jet H w a p) := by
    funext s
    rw [jet_add (H := fun q => s • H q) hG (ContDiff.const_smul s hH), jet_smul hH]
  rw [hpath]
  simpa only [one_mul, id_eq] using
    ((hasDerivAt_id t).mul_const (jet H w a p)).const_add (jet G w a p)

namespace MixedExpression

lemma varyBase_zero (G : Fin 4 → Base → Space) (H : Base → Space) : varyBase G H 0 = G := by
  funext i p
  by_cases hi : i = 0 <;> simp [varyBase, hi]

lemma varyBase_base (G : Fin 4 → Base → Space) (H : Base → Space) (s : ℝ) :
    varyBase G H s 0 = fun p => G 0 p + s • H p := by
  funext p
  simp only [varyBase, ↓reduceIte]

lemma varyBase_other (G : Fin 4 → Base → Space) (H : Base → Space) (s : ℝ)
    {i : Fin 4} (hi : i ≠ 0) : varyBase G H s i = G i := by
  funext p
  simp only [varyBase, hi, ↓reduceIte]

/-- The syntactic derivative evaluates to the actual derivative, while the
three direction slots remain fixed. -/
theorem differentiate_hasDerivAt {O : Set LowJet} (hO : IsOpen O)
    {G : Fin 4 → Base → Space} (hG : ∀ i, ContDiff ℝ ∞ (G i))
    {e : MixedExpression} (he : e.SmoothCoeffs O) (j : Fin 3) (z : Base × ℝ)
    (hQ : lowJet (G 0) z.1 ∈ O) :
    HasDerivAt (fun s : ℝ => e.eval (varyBase G (G j.succ) s) z)
      ((e.differentiate j).eval G z) 0 := by
  induction e with
  | coeff c =>
    have hd := Expression.variation_hasDerivAt hO (hG 0) (hG j.succ)
      (e := .coeff c) he z hQ
    simpa only [eval, varyBase_base, Expression.eval, Expression.variation,
      differentiate_coeff_eval] using hd
  | atom i w a e ih =>
    by_cases hi : i = 0
    · subst i
      have hj := jet_affine_hasDerivAt (hG 0) (hG j.succ) w a z.1 0
      have hd := hj.fun_mul (ih he)
      simpa only [eval, varyBase_base, varyBase_zero, differentiate, ↓reduceIte,
        Pi.mul_apply, zero_smul, add_zero] using hd
    · have hj := (hasDerivAt_const (0 : ℝ) (jet (G i) w a z.1)).fun_mul (ih he)
      simpa only [eval, varyBase_other G (G j.succ) _ hi, varyBase_zero,
        differentiate, hi, ↓reduceIte, zero_mul, zero_add, Pi.mul_apply] using hj
  | add e f ihe ihf => exact (ihe he.1).add (ihf he.2)

end MixedExpression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialLinearModes
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recover the real polynomial linearization from the complex conjugated
operator. This is the realization identity needed by forced cancellation. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression ModulatedJets

namespace Perturbation

lemma linearized_add {n : ℕ} (P : Fin n → Expression) (ε : ℝ) (G : Base → Space)
    {H K : Base → Space} (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K)
    (t : ℝ) (p : Base) :
    linearized P ε G (fun x => H x + K x) t p =
      linearized P ε G H t p + linearized P ε G K t p := by
  simp only [linearized, Expression.variation_add _ G hH hK, mul_add, Finset.sum_add_distrib]

end Perturbation
end ClosedSurfaceR4.JetPolynomial

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
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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

lemma restore_plane_mfderiv (i : A.centers) (f : SmallModes.Base → V)
    (hf : tsupport f ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    {p : M} (hp : p ∈ (chart (i : M)).source)
    (hd : DifferentiableAt ℝ f (planeCoordinateIsometry (chart (i : M) p))) :
    mfderiv planeModel 𝓘(ℝ,V)
      (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry)) p =
    (fderiv ℝ f (planeCoordinateIsometry (chart (i : M) p))).comp
      (planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (mfderiv planeModel 𝓘(ℝ,JetPolynomial.Base) (chart (i : M)) p)) := by
  have he : restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry) =ᶠ[𝓝 p]
      (f ∘ planeCoordinateIsometry) ∘ chart (i : M) := by
    filter_upwards [(chart (i : M)).open_source.mem_nhds hp] with x hx
    exact A.restore_plane_on_source i f hf hx
  have hc := ((chart_smooth (i : M)) p hp).contMDiffAt
    ((chart (i : M)).open_source.mem_nhds hp)
  have hfc : DifferentiableAt ℝ (f ∘ planeCoordinateIsometry) (chart (i : M) p) :=
    hd.comp _ planeCoordinateIsometry.differentiableAt
  rw [he.mfderiv_eq]
  change mfderiv planeModel 𝓘(ℝ,V) ((f ∘ planeCoordinateIsometry) ∘ chart (i : M)) p = _
  rw [mfderiv_comp p hfc.mdifferentiableAt (hc.mdifferentiableAt (by simp))]
  rw [mfderiv_eq_fderiv]
  change (fderiv ℝ (f ∘ planeCoordinateIsometry) (chart (i : M) p)).comp
    (mfderiv planeModel 𝓘(ℝ,JetPolynomial.Base) (chart (i : M)) p) = _
  have heq : fderiv ℝ (f ∘ planeCoordinateIsometry) (chart (i : M) p) =
      (fderiv ℝ f (planeCoordinateIsometry (chart (i : M) p))).comp
        planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap := by
    exact (hd.hasFDerivAt.comp _ planeCoordinateIsometry.toContinuousLinearEquiv.hasFDerivAt).fderiv
  rw [heq]
  exact ContinuousLinearMap.comp_assoc _ _ _

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ManifoldMetricCalculus
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact metric identities for actual smooth maps on the surface. The
finite-sum identity retains every cross term between distinct chart modes. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma surfaceDifferential_add {F U : M → V} {p : M}
    (hF : MDifferentiableAt planeModel 𝓘(ℝ,V) F p)
    (hU : MDifferentiableAt planeModel 𝓘(ℝ,V) U p) :
    surfaceDifferential (F+U) p = surfaceDifferential F p + surfaceDifferential U p :=
  mfderiv_add hF hU

lemma mfderiv_finite_sum {ι : Type*} (s : Finset ι) (f : ι → M → V) {p : M}
    (hf : ∀ i ∈ s, MDifferentiableAt planeModel 𝓘(ℝ,V) (f i) p) :
    surfaceDifferential (∑ i ∈ s, f i) p =
      ∑ i ∈ s, surfaceDifferential (f i) p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact mfderiv_const
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 : MDifferentiableAt planeModel 𝓘(ℝ,V) (∑ i ∈ s, f i) p := by
      have key : ∀ t : Finset ι, (∀ i ∈ t, MDifferentiableAt planeModel 𝓘(ℝ,V) (f i) p) →
          MDifferentiableAt planeModel 𝓘(ℝ,V) (∑ i ∈ t, f i) p := by
        intro t
        induction t using Finset.induction_on with
        | empty =>
          intro _
          simp only [Finset.sum_empty]
          exact mdifferentiableAt_const
        | insert b t hb ih' =>
          intro hh
          rw [Finset.sum_insert hb]
          exact (hh b (Finset.mem_insert_self b t)).add
            (ih' (fun i hi => hh i (Finset.mem_insert_of_mem hi)))
      exact key s (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    rw [surfaceDifferential_add h1 h2, ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

lemma linearMetricForm_finite_sum {ι : Type*} [Fintype ι]
    (F : M → V) (f : ι → M → V) {p : M}
    (hf : ∀ i, MDifferentiableAt planeModel 𝓘(ℝ,V) (f i) p)
    (v w : TangentSpace planeModel p) :
    linearMetricForm F (∑ i, f i) p v w = ∑ i, linearMetricForm F (f i) p v w := by
  unfold linearMetricForm
  rw [mfderiv_finite_sum Finset.univ f (fun i _ => hf i)]
  simp only [sum_apply,inner_sum,sum_inner,Finset.sum_add_distrib]

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedAtlasMetric
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual metric and linearized metric of supported restored displacements
in the original atlas coordinates. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4
open FiniteOrderSmoothing JetPolynomial

lemma surfaceDifferential_zero_off_support
    {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (F : M → V) {p : M}
    (hp : p ∉ tsupport F) : surfaceDifferential F p = 0 := by
  have he : F =ᶠ[𝓝 p] (fun _ => (0 : V)) := notMem_tsupport_iff_eventuallyEq.mp hp
  unfold surfaceDifferential
  rw [he.mfderiv_eq, mfderiv_const]
  rfl

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ManifoldMetricTensor
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual metric tensors and cross tensors of manifold displacements.
Cross tensors vanish away from the intersection of the two supports. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

local instance metricTensorFiberNormed_rd4c706_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance metricTensorFiberSpace_rd4c706_1 : NormedSpace ℝ TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricTangentNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricTangentSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricTensorDualAdd
local instance metricTensorDualSmul_rd4c706_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance metricTensorSectionNormed_rd4c706_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricTensorSectionSpace_rd4c706_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma linearMetricTensor_apply (F U : M → Space) (p : M) (v w : TangentSpace planeModel p) :
    linearMetricTensor F U p v w = linearMetricForm F U p v w := rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasMetricExpansion
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The metric of the actual global oscillation, including every cross term
between different atlas patches. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance atlasMetricFiberNormed_rd4c706_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasMetricFiberSpace_rd4c706_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance atlasMetricDualAdd_rd4c706_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasMetricDualSmul_rd4c706_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance atlasMetricSectionNormed_rd4c706_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasMetricSectionSpace_rd4c706_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma euclidean_vectorPlaneRestore (f : A.centers → SmallModes.Base → RealModes.RVec 4) :
    spaceCoordinates.symm ∘ A.vectorPlaneRestore f =
      A.vectorPlaneRestore (fun i => spaceCoordinates.symm ∘ f i) := by
  funext p
  simp only [vectorPlaneRestore,Function.comp_apply,Finset.sum_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hp : p ∈ (chart (i : M)).source
  · simp only [restore,indicator_of_mem hp,Function.comp_apply,map_smul]
  · simp only [restore,indicator_of_notMem hp,map_zero]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasTensorDerivatives
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiation in a real parameter commutes with the actual finite
atlas restoration and chart reading. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base planeCoordinateIsometry)
open PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorDerivativeFiberSpace
local instance tensorDerivativeDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorDerivativeDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorDerivativeFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorDerivativeFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorDerivativeSectionNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorDerivativeSectionSpace
lemma tensorPlaneRestore_hasDerivAt
    {f : ℝ → A.centers → SmallModes.Base → Tensor}
    {f' : A.centers → SmallModes.Base → Tensor} {s : ℝ} (p : M)
    (hf : ∀ i, HasDerivAt (fun r => f r i (planeCoordinateIsometry (chart (i : M) p)))
      (f' i (planeCoordinateIsometry (chart (i : M) p))) s) :
    HasDerivAt (fun r => A.tensorPlaneRestore (f r) p) (A.tensorPlaneRestore f' p) s := by
  have hi (i : A.centers) :=
    (((A.tensorTriv i).symmL ℝ p).hasFDerivAt.comp_hasDerivAt s
      (fiberFromThree.hasFDerivAt.comp_hasDerivAt s (hf i))).const_smul (A.outer i p)
  exact HasDerivAt.fun_sum (fun i _ => hi i)

lemma tensorChartRead_hasDerivAt
    {f : ℝ → ∀ p : M, CovariantTwoTensor p}
    {f' : ∀ p : M, CovariantTwoTensor p} {s : ℝ} (i : A.centers) (x : Base)
    (hf : HasDerivAt (fun r => f r ((chart (i : M)).symm x))
      (f' ((chart (i : M)).symm x)) s) :
    HasDerivAt (fun r => A.tensorChartRead i (f r) x) (A.tensorChartRead i f' x) s := by
  by_cases hx : x ∈ (chart (i : M)).target
  · have hc := (((A.tensorTriv i).continuousLinearMapAt ℝ ((chart (i : M)).symm x)).hasFDerivAt).comp_hasDerivAt s hf
    have h := fiberToThree.hasFDerivAt.comp_hasDerivAt s
      (hc.const_smul ((A.outer i ((chart (i : M)).symm x))^2))
    simp only [tensorChartRead,Function.comp_apply,bundleCutoff,localize,
      indicator_of_mem hx,bundleComponent]
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext r
    rfl
  · simp only [tensorChartRead,Function.comp_apply,bundleCutoff,localize,
      indicator_of_notMem hx,map_zero]
    exact hasDerivAt_const s 0

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_RestoredLinearizedMetric
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact globalization of the actual metric linearization. The local
base map is the constructed smooth representative of the global map. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4

lemma euclidean_linearized_coordinate_value (F U : SmallModes.Base → Space)
    {y : SmallModes.Base} (hF : DifferentiableAt ℝ F y) (hU : DifferentiableAt ℝ U y)
    (v w : SmallModes.Base) :
    PhaseMean.evaluate (RealModes.realLinearizedTensor (spaceCoordinates ∘ F) (spaceCoordinates ∘ U) y) v w =
      inner ℝ (fderiv ℝ F y v) (fderiv ℝ U y w) +
        inner ℝ (fderiv ℝ U y v) (fderiv ℝ F y w) := by
  rw [RealModes.evaluate_realLinearizedTensor]
  simp only [RealModes.realLinearized,SmallModes.coordDeriv]
  rw [(spaceCoordinates.hasFDerivAt.comp y hF.hasFDerivAt).fderiv,
    (spaceCoordinates.hasFDerivAt.comp y hU.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  change spaceCoordinates (fderiv ℝ F y v) ⬝ᵥ spaceCoordinates (fderiv ℝ U y w) +
    spaceCoordinates (fderiv ℝ F y w) ⬝ᵥ spaceCoordinates (fderiv ℝ U y v) = _
  rw [spaceCoordinates_dot,spaceCoordinates_dot]
  congr 1
  exact real_inner_comm _ _

namespace FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredLinearDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredLinearFiberSpace
local instance restoredLinearDualSmul_rd4c706_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredLinearFiberNormed
local instance restoredLinearSectionNormed_rd4c706_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance restoredLinearSectionSpace_rd4c706_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem restored_linearized_metric (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (f : SmallModes.Base → Space)
    (hf : ContDiff ℝ ∞ f)
    (hsp : tsupport f ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    linearMetricTensor F (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry)) =
      A.bundleRestore A.tensorTriv i (fun y => fiberFromThree
        (RealModes.realLinearizedTensor (spaceCoordinates ∘ A.vectorPlaneRead i F)
          (spaceCoordinates ∘ f) (planeCoordinateIsometry y))) := by
  funext p
  ext v w
  by_cases hp : p ∈ (chart (i : M)).source
  · rw [linearMetricTensor_apply,A.tensorRestore_apply i _ hp,fiberFromThree_apply]
    have hd := A.plane_chart_differential i hp
    have hv := congrArg (fun L => L v) hd
    have hw := congrArg (fun L => L w) hd
    change planeCoordinateIsometry (surfaceDifferential (chart (i : M)) p v) = _ at hv
    change planeCoordinateIsometry (surfaceDifferential (chart (i : M)) p w) = _ at hw
    simp only [ContinuousLinearMap.comp_apply] at hv hw
    change planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap
      (surfaceDifferential (chart (i : M)) p v) = _ at hv
    change planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap
      (surfaceDifferential (chart (i : M)) p w) = _ at hw
    rw [euclidean_linearized_coordinate_value _ _
      ((A.vectorPlaneRead_smooth i hF).differentiable (by simp) _) (hf.differentiable (by simp) _)]
    have hu := A.restore_plane_mfderiv i f hsp hp (hf.differentiable (by simp) _)
    change surfaceDifferential (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry)) p =
      (fderiv ℝ f (planeCoordinateIsometry (chart (i : M) p))).comp
        (planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap.comp
          (surfaceDifferential (chart (i : M)) p)) at hu
    unfold linearMetricForm
    rw [hu]
    by_cases hs : p ∈ tsupport (A.weight i)
    · rw [A.vectorPlaneRead_differential i hF hs,A.outer_one i p hs,one_mul]
      simp only [ContinuousLinearMap.comp_apply,hv,hw]
      rfl
    · have hn : planeCoordinateIsometry (chart (i : M) p) ∉ tsupport f := by
        intro hh
        exact hs (A.mem_weight_support_of_plane i hp (hsp hh))
      rw [fderiv_of_notMem_tsupport ℝ hn]
      simp only [ContinuousLinearMap.zero_comp,zero_apply,inner_zero_left,inner_zero_right,add_zero,mul_zero]
  · have hs : p ∉ tsupport (A.weight i) := fun h => hp (A.weight_support i h)
    have hu := surfaceDifferential_zero_off_support
      (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry))
      (fun h => hs (A.restore_plane_tsupport i f hsp h))
    have ho : A.outer i p = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hp (A.outer_support i h))
    simp only [linearMetricTensor_apply,linearMetricForm,hu,zero_apply,inner_zero_left,
      inner_zero_right,add_zero,bundleRestore,ho,zero_smul]

end SmoothingAtlas
end FiniteOrderSmoothing
end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasLinearizedMetric
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport the actual local linear residuals to the global metric tensor. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

local instance atlasLinearFiberNormed_rd4c706_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasLinearFiberSpace_rd4c706_1 : NormedSpace ℝ TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasLinearDualAdd
local instance atlasLinearDualSmul_rd4c706_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance atlasLinearSectionNormed_rd4c706_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasLinearSectionSpace_rd4c706_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma linearMetricTensor_finite_sum {ι : Type*} [Fintype ι]
    (F : M → Space) (f : ι → M → Space) (hf : ∀ i, ContMDiff planeModel spaceModel ∞ (f i)) :
    linearMetricTensor F (∑ i, f i) = fun p => ∑ i, linearMetricTensor F (f i) p := by
  funext p
  ext v w
  simpa only [sum_apply,linearMetricTensor_apply] using
    linearMetricForm_finite_sum F f (fun i => ((hf i) p).mdifferentiableAt (by simp)) v w

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasLinearDualAdd
local instance atlasLinearFiberNormed_rd4c706_2 : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasLinearFiberSpace_rd4c706_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance atlasLinearDualSmul_rd4c706_2 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance atlasLinearSectionNormed_rd4c706_2 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasLinearSectionSpace_rd4c706_2 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem vectorPlaneRestore_linearized {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (f : A.centers → SmallModes.Base → Space) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hsp : ∀ i, tsupport (f i) ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    linearMetricTensor F (A.vectorPlaneRestore f) =
      A.tensorPlaneRestore (fun i => RealModes.realLinearizedTensor
        (spaceCoordinates ∘ A.vectorPlaneRead i F) (spaceCoordinates ∘ f i)) := by
  unfold vectorPlaneRestore
  rw [linearMetricTensor_finite_sum F
    (fun i : A.centers => restore (i : M) (A.outer i) (f i ∘ planeCoordinateIsometry))
    (fun i => restore_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
      ((hf i).comp planeCoordinateIsometry.contDiff))]
  funext p
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (A.restored_linearized_metric i hF (f i) (hf i) (hsp i)) p

theorem euclidean_vectorPlaneRestore_linearized {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (f : A.centers → SmallModes.Base → RealModes.RVec 4) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (hsp : ∀ i, tsupport (f i) ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    linearMetricTensor F (spaceCoordinates.symm ∘ A.vectorPlaneRestore f) =
      A.tensorPlaneRestore (fun i => RealModes.realLinearizedTensor
        (spaceCoordinates ∘ A.vectorPlaneRead i F) (f i)) := by
  rw [A.euclidean_vectorPlaneRestore]
  have hh := A.vectorPlaneRestore_linearized hF (fun i => spaceCoordinates.symm ∘ f i)
    (fun i => spaceCoordinates.symm.contDiff.comp (hf i))
    (fun i => (tsupport_comp_subset (g := spaceCoordinates.symm) (map_zero _) (f i)).trans (hsp i))
  have he (i : A.centers) : spaceCoordinates ∘ (spaceCoordinates.symm ∘ f i) = f i := by
    funext x
    simp only [Function.comp_apply,ContinuousLinearEquiv.apply_symm_apply]
  simpa only [he] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_LinearMetricChartReconstruction
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mixed metric is reconstructed from the genuine chart readings. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
local instance linearReadFiberNormed_rd4c706_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance linearReadFiberSpace_rd4c706_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance linearReadDualAdd_rd4c706_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance linearReadDualSmul_rd4c706_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.linearReadSectionNormed
local instance linearReadSectionSpace_rd4c706_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma vectorPlaneRead_add {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : A.centers) (F G : M → V) :
    A.vectorPlaneRead i (F+G) = A.vectorPlaneRead i F + A.vectorPlaneRead i G := by
  funext x
  by_cases hx : planeCoordinateIsometry.symm x ∈ (chart (i : M)).target <;>
    simp [vectorPlaneRead,vectorChartRead,localize,hx,smul_add]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialVariationDerivatives
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The second and third mixed polynomials differentiate the preceding actual
variation; these are not independent formal symbols. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression

lemma eval_differentiate_ofExpression (e : Expression) (j : Fin 3)
    (G : Fin 4 → Base → Space) (z : Base × ℝ) :
    ((ofExpression e).differentiate j).eval G z = e.variation (G 0) (G j.succ) z := by
  induction e with
  | coeff c => exact differentiate_coeff_eval c j G z
  | atom w a e ih =>
    simp only [ofExpression, differentiate, ↓reduceIte, eval, ofExpression_eval,
      Expression.variation, ih]
  | add e f ihe ihf => simp only [ofExpression, differentiate, eval, Expression.variation, ihe, ihf]

namespace Expression

theorem second_variation_hasDerivAt {O : Set LowJet} (hO : IsOpen O)
    {e : Expression} (he : e.SmoothCoeffs O) {G : Fin 4 → Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (z : Base × ℝ) (hQ : lowJet (G 0) z.1 ∈ O) :
    HasDerivAt (fun s : ℝ => e.variation (fun p => G 0 p + s • G 2 p) (G 1) z)
      ((e.variations 1).eval G z) 0 := by
  have hd := differentiate_hasDerivAt hO hG
    (e.variations_smoothCoeffs hO he 0) 1 z hQ
  simp only [show (1 : Fin 3).succ = (2 : Fin 4) by decide] at hd
  have heq : (fun s : ℝ => (e.variations 0).eval (varyBase G (G 2) s) z) =
      (fun s : ℝ => e.variation (fun p => G 0 p + s • G 2 p) (G 1) z) := by
    funext s
    change ((ofExpression e).differentiate 0).eval (varyBase G (G 2) s) z = _
    rw [eval_differentiate_ofExpression, varyBase_base, Fin.succ_zero_eq_one,
      varyBase_other _ _ _ (by decide : (1 : Fin 4) ≠ 0)]
  rw [heq] at hd
  exact hd

end Expression
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

theorem variation_hasDerivAt {O : Set LowJet} (hO : IsOpen O)
    {P : Fin n → Expression} (hP : ∀ l, (P l).SmoothCoeffs O) (ε : ℝ)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (z : Base × ℝ) (hQ : lowJet G z.1 ∈ O) :
    HasDerivAt (fun s : ℝ => eval P ε (fun p => G p + s • H p) z)
      (variation P ε G H z) 0 := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun l _ =>
    ((P l).variation_hasDerivAt hO hG hH (hP l) z hQ).const_mul (ε ^ (l.val + 1)))
  simpa only [eval, variation] using h

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialMetric
attribute [-instance] _root_.instVAddIntReal_solutions
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
local instance polynomialMetricSectionNormed_rd4c706_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialMetricSectionSpace_rd4c706_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma jetChartMap_add (i : A.centers) (G X : M → Space) :
    A.jetChartMap i (G+X) = A.jetChartMap i G+A.jetChartMap i X := by
  have h := A.vectorPlaneRead_add i G X
  funext x
  have hh := congrFun h (planeCoordinateIsometry x)
  change spaceCoordinates (A.vectorChartRead i (G+X) x) =
    spaceCoordinates (A.vectorChartRead i G x)+spaceCoordinates (A.vectorChartRead i X x)
  simpa only [vectorPlaneRead,Function.comp_apply,planeCoordinateIsometry.symm_apply_apply,
    Pi.add_apply,map_add] using congrArg spaceCoordinates hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CoordinatePolynomialCalculus
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual derivatives in the map variable of the coordinate polynomial. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

lemma coordinatePolynomialValue_hasDerivAt {n : ℕ}
    {P : Fin 3 → Fin n → Expression} (hP : ∀ k l, (P k l).SmoothCoeffs univ)
    (ε t : ℝ) {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (x : Base) :
    HasDerivAt (fun s : ℝ => coordinatePolynomialValue P ε (G+s • H) t
        (planeCoordinateIsometry x))
      (coordinateRealLinearized P ε G (H ∘ planeCoordinateIsometry.symm) t
        (planeCoordinateIsometry x)) 0 := by
  have hcomp : (H ∘ planeCoordinateIsometry.symm) ∘ planeCoordinateIsometry = H := by
    funext y
    simp only [Function.comp_apply,planeCoordinateIsometry.symm_apply_apply]
  apply hasDerivAt_pi.mpr
  intro k
  have hd := variation_hasDerivAt isOpen_univ (hP k) ε hG hH (x,t) (mem_univ _)
  simp only [coordinatePolynomialValue,coordinateRealLinearized,linearized,variation,
    eval,hcomp,planeCoordinateIsometry.symm_apply_apply] at hd ⊢
  convert hd using 1
  all_goals try with_reducible_and_instances rfl


lemma coordinateRealLinearized_hasDerivAt {n : ℕ}
    {P : Fin 3 → Fin n → Expression} (hP : ∀ k l, (P k l).SmoothCoeffs univ)
    (ε t : ℝ) {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (x : Base) :
    HasDerivAt (fun s : ℝ => coordinateRealLinearized P ε (G+s • H)
        (H ∘ planeCoordinateIsometry.symm) t (planeCoordinateIsometry x))
      ((2 : ℝ) • coordinateQuadraticPolynomial P ε G (H ∘ planeCoordinateIsometry.symm) t
        (planeCoordinateIsometry x)) 0 := by
  have hf : ∀ i : Fin 4, ContDiff ℝ ∞ (![G,H,H,0] i) := by
    intro i
    fin_cases i
    · exact hG
    · exact hH
    · exact hH
    · exact contDiff_const
  apply hasDerivAt_pi.mpr
  intro k
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun l _ =>
    ((P k l).second_variation_hasDerivAt isOpen_univ (hP k l) hf
      (x,t) (mem_univ _)).const_mul (ε^(l.val+1)))
  change HasDerivAt (fun s : ℝ => ∑ l, ε^(l.val+1) *
    (P k l).variation (G+s • H) H (x,t))
    (∑ l, ε^(l.val+1) * ((P k l).variations 1).eval ![G,H,H,0] (x,t)) 0 at hd
  have hcomp : (H ∘ planeCoordinateIsometry.symm) ∘ planeCoordinateIsometry = H := by
    funext y
    simp only [Function.comp_apply,planeCoordinateIsometry.symm_apply_apply]
  have hsecond : ((2 : ℝ) • coordinateQuadraticPolynomial P ε G
      (H ∘ planeCoordinateIsometry.symm) t (planeCoordinateIsometry x)) k =
      ∑ l, ε^(l.val+1) * ((P k l).variations 1).eval ![G,H,H,0] (x,t) := by
    simp only [coordinateQuadraticPolynomial,hcomp,
      planeCoordinateIsometry.symm_apply_apply,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hsecond]
  simpa only [coordinateRealLinearized,linearized,hcomp,
    planeCoordinateIsometry.symm_apply_apply] using hd

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialCalculus
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First and second derivatives of the globally restored polynomial
are the operators used in its exact Taylor identity. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance polynomialDerivativeFiberNormed_rd4c706_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialDerivativeFiberSpace_rd4c706_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance polynomialDerivativeDualAdd_rd4c706_1 : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialDerivativeDualSmul
variable (A : SmoothingAtlas M)

local instance polynomialDerivativeSectionNormed_rd4c706_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialDerivativeSectionSpace_rd4c706_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma jetChartMap_affine (i : A.centers) (F X : M → Space) (s : ℝ) :
    A.jetChartMap i (F+s • X) = A.jetChartMap i F+s • A.jetChartMap i X := by
  rw [A.jetChartMap_add]
  congr 1
  funext x
  change spaceCoordinates (localize (i : M) (A.outer i) (s • X) x) =
    s • spaceCoordinates (localize (i : M) (A.outer i) X x)
  rw [localize_smul]
  exact map_smul spaceCoordinates s _

lemma atlasPolynomialValue_hasDerivAt {n : A.centers → ℕ}
    {P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ) (ε : ℝ)
    {F X : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    (hX : ContMDiff planeModel spaceModel ∞ X) (p : M) :
    HasDerivAt (fun s : ℝ => A.atlasPolynomialValue P ε (F+s • X) p)
      (A.atlasPolynomialVariation P ε F X p) 0 := by
  unfold atlasPolynomialValue atlasPolynomialVariation
  apply A.tensorPlaneRestore_hasDerivAt
  intro i
  simp only [A.jetChartMap_affine]
  exact coordinatePolynomialValue_hasDerivAt (hP i) ε 0
    (A.jetChartMap_smooth i hF) (A.jetChartMap_smooth i hX) (chart (i : M) p)

lemma atlasPolynomialVariation_hasDerivAt {n : A.centers → ℕ}
    {P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ) (ε : ℝ)
    {F X : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    (hX : ContMDiff planeModel spaceModel ∞ X) (p : M) :
    HasDerivAt (fun s : ℝ => A.atlasPolynomialVariation P ε (F+s • X) X p)
      ((2 : ℝ) • A.atlasPolynomialQuadratic P ε F X p) 0 := by
  have hd := A.tensorPlaneRestore_hasDerivAt
    (f := fun s i => coordinateRealLinearized (P i) ε
      (A.jetChartMap i F+s • A.jetChartMap i X)
      (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0)
    (f' := fun i => (2 : ℝ) • coordinateQuadraticPolynomial (P i) ε (A.jetChartMap i F)
      (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0) p (fun i =>
    coordinateRealLinearized_hasDerivAt (hP i) ε 0
      (A.jetChartMap_smooth i hF) (A.jetChartMap_smooth i hX) (chart (i : M) p))
  change HasDerivAt _ (A.tensorPlaneRestore ((2 : ℝ) • fun i =>
    coordinateQuadraticPolynomial (P i) ε (A.jetChartMap i F)
      (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0) p) 0 at hd
  rw [A.tensorPlaneRestore_smul] at hd
  simpa only [atlasPolynomialVariation,atlasPolynomialQuadratic,A.jetChartMap_affine,
    Pi.smul_apply] using hd

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
local instance polynomialSupportFiberNormed_rd4c706_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialSupportFiberSpace_rd4c706_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance polynomialSupportDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))

namespace SmoothingAtlas
local instance polynomialSupportFiberNormed_rd4c706_2 : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialSupportFiberSpace_rd4c706_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance polynomialSupportDualSmul_rd4c706_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance polynomialSupportSectionNormed_rd4c706_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialSupportSectionSpace_rd4c706_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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

lemma atlasPolynomialVariation_zero_of_notMem {n : A.centers → ℕ}
    (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression) (ε : ℝ)
    (F X : M → Space) {p : M} (hp : p ∉ tsupport X) :
    A.atlasPolynomialVariation P ε F X p = 0 := by
  classical
  unfold atlasPolynomialVariation tensorPlaneRestore
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
    have he : coordinateRealLinearized (P i) ε (A.jetChartMap i F)
        (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0
        (planeCoordinateIsometry (chart (i : M) p)) = 0 := by
      funext k
      simp only [coordinateRealLinearized,linearized,hcomp,
        planeCoordinateIsometry.symm_apply_apply,Pi.zero_apply]
      apply Finset.sum_eq_zero
      intro l _
      rw [(P i k l).variation_zero_of_notMem (A.jetChartMap i F) hn 0,mul_zero]
    simp only [bundleRestore,he,map_zero,smul_zero]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialLinearity
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite linearity in the direction of the actual global polynomial. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Perturbation

lemma coordinateRealLinearized_add {n : ℕ} (P : Fin 3 → Fin n → Expression)
    (ε : ℝ) (G : Base → Space) {X Y : RealModes.RField 4}
    (hX : ContDiff ℝ ∞ X) (hY : ContDiff ℝ ∞ Y) (t : ℝ) :
    coordinateRealLinearized P ε G (X+Y) t =
      coordinateRealLinearized P ε G X t+coordinateRealLinearized P ε G Y t := by
  funext p k
  change linearized (P k) ε G (fun x => X (planeCoordinateIsometry x)+Y (planeCoordinateIsometry x))
    t (planeCoordinateIsometry.symm p) = _
  exact linearized_add (P k) ε G (hX.comp planeCoordinateIsometry.contDiff)
    (hY.comp planeCoordinateIsometry.contDiff) t (planeCoordinateIsometry.symm p)

end ClosedSurfaceR4.JetPolynomial.Perturbation

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialLinearDualAdd
local instance polynomialLinearFiberNormed_rd4c706_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialLinearFiberSpace_rd4c706_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance polynomialLinearDualSmul_rd4c706_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance polynomialLinearSectionNormed_rd4c706_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialLinearSectionSpace_rd4c706_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma atlasPolynomialVariation_add {n : A.centers → ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression) (ε : ℝ) (F : M → Space)
    {X Y : M → Space} (hX : ContMDiff planeModel spaceModel ∞ X)
    (hY : ContMDiff planeModel spaceModel ∞ Y) :
    A.atlasPolynomialVariation P ε F (X+Y) =
      A.atlasPolynomialVariation P ε F X+A.atlasPolynomialVariation P ε F Y := by
  unfold atlasPolynomialVariation
  rw [← A.tensorPlaneRestore_add]
  congr 1
  funext i
  have he : A.jetChartMap i (X+Y) ∘ planeCoordinateIsometry.symm =
      (A.jetChartMap i X ∘ planeCoordinateIsometry.symm)+
        (A.jetChartMap i Y ∘ planeCoordinateIsometry.symm) := by
    rw [A.jetChartMap_add]
    rfl
  rw [he,coordinateRealLinearized_add (P i) ε _
    ((A.jetChartMap_smooth i hX).comp planeCoordinateIsometry.symm.contDiff)
    ((A.jetChartMap_smooth i hY).comp planeCoordinateIsometry.symm.contDiff)]
  rfl

omit [CompactSpace M] in
lemma atlasPolynomialVariation_zero {n : A.centers → ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression) (ε : ℝ) (F : M → Space) :
    A.atlasPolynomialVariation P ε F 0 = 0 := by
  funext p
  exact A.atlasPolynomialVariation_zero_of_notMem P ε F 0 (by simp)

lemma atlasPolynomialVariation_sum {n : A.centers → ℕ} {ι : Type*}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression) (ε : ℝ) (F : M → Space)
    (S : Finset ι) (X : ι → M → Space) (hX : ∀ i, ContMDiff planeModel spaceModel ∞ (X i)) :
    A.atlasPolynomialVariation P ε F (∑ i ∈ S, X i) =
      ∑ i ∈ S, A.atlasPolynomialVariation P ε F (X i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,A.atlasPolynomialVariation_zero]
  | @insert i S hi ih =>
    have hs : ContMDiff planeModel spaceModel ∞ (∑ j ∈ S, X j) := by
      convert ContMDiff.sum (t := S) (fun j _ => hX j) using 1
      all_goals try with_reducible_and_instances rfl
      funext p
      simp only [Finset.sum_apply]
    rw [Finset.sum_insert hi,A.atlasPolynomialVariation_add P ε F (hX i) hs,ih,
      Finset.sum_insert hi]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_InitialInputBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite initial input estimates for the scalar-contracted map. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance initialBoundFiberNormed_rd4c706_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance initialBoundFiberSpace_rd4c706_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance initialBoundDualAdd_rd4c706_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance initialBoundDualSmul_rd4c706_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance initialBoundSectionNormed_rd4c706_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance initialBoundSectionSpace_rd4c706_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma space_smul_contMDiff {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (a : ℝ) :
    ContMDiff planeModel spaceModel ∞ (a • F) :=
  (a • ContinuousLinearMap.id ℝ Space).contDiff.contMDiff.comp hF

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialVariationRepresentation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local representatives differentiate to the same first and second
variations as the global polynomial tensor. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance variationRepFiberNormed_rd4c706_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance variationRepFiberSpace_rd4c706_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance variationRepDualAdd_rd4c706_1 : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance variationRepDualSmul_rd4c706_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance variationRepSectionNormed_rd4c706_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance variationRepSectionSpace_rd4c706_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma tensorChartRead_smul (i : A.centers) (c : ℝ) (u : ∀ p : M, CovariantTwoTensor p) :
    A.tensorChartRead i (c • u) = c • A.tensorChartRead i u := by
  funext x
  by_cases hx : x ∈ (chart (i : M)).target
  · simp only [tensorChartRead,Function.comp_apply,bundleCutoff,localize,
      indicator_of_mem hx,bundleComponent,Pi.smul_apply,map_smul]
    rw [smul_comm]
  · simp only [tensorChartRead,Function.comp_apply,bundleCutoff,localize,
      indicator_of_notMem hx,map_zero,Pi.smul_apply,smul_zero]

lemma polynomial_first_of_representation {n : A.centers → ℕ} {m : ℕ}
    {P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
    (i : A.centers) {Q : Fin 3 → Fin m → Expression}
    (hQ : ∀ k l, (Q k l).SmoothCoeffs univ)
    (x : Base)
    (hrep : ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F → ∀ ε : ℝ,
      coordinatePolynomialValue Q ε (A.jetChartMap i F) 0 (planeCoordinateIsometry x) =
        A.tensorChartRead i (A.atlasPolynomialValue P ε F) x)
    {F X : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    (hX : ContMDiff planeModel spaceModel ∞ X) (ε : ℝ) :
    coordinateRealLinearized Q ε (A.jetChartMap i F)
        (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0 (planeCoordinateIsometry x) =
      A.tensorChartRead i (A.atlasPolynomialVariation P ε F X) x := by
  have hl := coordinatePolynomialValue_hasDerivAt hQ ε 0
    (A.jetChartMap_smooth i hF) (A.jetChartMap_smooth i hX) x
  have hr := A.tensorChartRead_hasDerivAt i x
    (A.atlasPolynomialValue_hasDerivAt hP ε hF hX ((chart (i : M)).symm x))
  have he : (fun s : ℝ => coordinatePolynomialValue Q ε
      (A.jetChartMap i F+s • A.jetChartMap i X) 0 (planeCoordinateIsometry x)) =
      (fun s : ℝ => A.tensorChartRead i (A.atlasPolynomialValue P ε (F+s • X)) x) := by
    funext s
    rw [← A.jetChartMap_affine]
    exact hrep (F+s • X) (hF.add (space_smul_contMDiff hX s)) ε
  rw [he] at hl
  exact hl.unique hr

lemma polynomial_quadratic_of_representation {n : A.centers → ℕ} {m : ℕ}
    {P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
    (i : A.centers) {Q : Fin 3 → Fin m → Expression}
    (hQ : ∀ k l, (Q k l).SmoothCoeffs univ)
    (x : Base)
    (hrep : ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F → ∀ ε : ℝ,
      coordinatePolynomialValue Q ε (A.jetChartMap i F) 0 (planeCoordinateIsometry x) =
        A.tensorChartRead i (A.atlasPolynomialValue P ε F) x)
    {F X : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    (hX : ContMDiff planeModel spaceModel ∞ X) (ε : ℝ) :
    coordinateQuadraticPolynomial Q ε (A.jetChartMap i F)
        (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0 (planeCoordinateIsometry x) =
      A.tensorChartRead i (A.atlasPolynomialQuadratic P ε F X) x := by
  have hl := coordinateRealLinearized_hasDerivAt hQ ε 0
    (A.jetChartMap_smooth i hF) (A.jetChartMap_smooth i hX) x
  have hr := A.tensorChartRead_hasDerivAt
    (f := fun s => A.atlasPolynomialVariation P ε (F+s • X) X)
    (f' := (2 : ℝ) • A.atlasPolynomialQuadratic P ε F X) i x
    (A.atlasPolynomialVariation_hasDerivAt hP ε hF hX ((chart (i : M)).symm x))
  have he : (fun s : ℝ => coordinateRealLinearized Q ε
      (A.jetChartMap i F+s • A.jetChartMap i X)
      (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0 (planeCoordinateIsometry x)) =
      (fun s : ℝ => A.tensorChartRead i (A.atlasPolynomialVariation P ε (F+s • X) X) x) := by
    funext s
    rw [← A.jetChartMap_affine]
    exact A.polynomial_first_of_representation hP i hQ x hrep
      (hF.add (space_smul_contMDiff hX s)) hX ε
  rw [he] at hl
  have hh := hl.unique hr
  have hs := congrFun (A.tensorChartRead_smul i (2 : ℝ)
    (A.atlasPolynomialQuadratic P ε F X)) x
  rw [hs] at hh
  have hc := congrArg (fun t : Tensor => (1/2 : ℝ) • t) hh
  simpa only [Pi.smul_apply,smul_smul,show (1/2 : ℝ)*2 = 1 by norm_num,one_smul] using hc

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialLocalModel
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single local polynomial models the global perturbation, with its
first and second variations, on the entire compact chart support. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance localModelFiberNormed_rd4c706_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance localModelFiberSpace_rd4c706_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance localModelDualAdd_rd4c706_1 : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance localModelDualSmul_rd4c706_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance localModelSectionNormed_rd4c706_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance localModelSectionSpace_rd4c706_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem atlas_polynomial_local_model {n : A.centers → ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (hP : ∀ j k r, (P j k r).SmoothCoeffs univ) (i : A.centers) :
    ∃ Q : Fin 3 → Fin (polynomialFamilyDegree n) → Expression,
      (∀ k r, (Q k r).SmoothCoeffs univ) ∧
      (∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
        ∀ x ∈ (A.chartWeightCompact i : Set Base), ∀ ε : ℝ,
          coordinatePolynomialValue Q ε (A.jetChartMap i F) 0 (planeCoordinateIsometry x) =
            A.tensorChartRead i (A.atlasPolynomialValue P ε F) x) ∧
      (∀ (F X : M → Space), ContMDiff planeModel spaceModel ∞ F →
        ContMDiff planeModel spaceModel ∞ X →
        ∀ x ∈ (A.chartWeightCompact i : Set Base), ∀ ε : ℝ,
          coordinateRealLinearized Q ε (A.jetChartMap i F)
              (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0 (planeCoordinateIsometry x) =
            A.tensorChartRead i (A.atlasPolynomialVariation P ε F X) x) ∧
      (∀ (F X : M → Space), ContMDiff planeModel spaceModel ∞ F →
        ContMDiff planeModel spaceModel ∞ X →
        ∀ x ∈ (A.chartWeightCompact i : Set Base), ∀ ε : ℝ,
          coordinateQuadraticPolynomial Q ε (A.jetChartMap i F)
              (A.jetChartMap i X ∘ planeCoordinateIsometry.symm) 0 (planeCoordinateIsometry x) =
            A.tensorChartRead i (A.atlasPolynomialQuadratic P ε F X) x) := by
  obtain ⟨Q,hQ,hvalue⟩ := A.atlas_polynomial_representation_on_support P hP i
  refine ⟨Q,hQ,hvalue,?_,?_⟩
  · intro F X hF hX x hx ε
    exact A.polynomial_first_of_representation hP i hQ x
      (fun G hG ε => hvalue G hG x hx ε) hF hX ε
  · intro F X hF hX x hx ε
    exact A.polynomial_quadratic_of_representation hP i hQ x
      (fun G hG ε => hvalue G hG x hx ε) hF hX ε

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
local instance restoredDirectionDualSmul_rd4c706_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredDirectionFiberNormed
local instance restoredDirectionSectionNormed_rd4c706_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance restoredDirectionSectionSpace_rd4c706_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialLinearized
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual global polynomial linearization is assembled from the
constructed local representatives, for every supported family. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialAssemblyDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialAssemblyFiberSpace
local instance polynomialAssemblyDualSmul_rd4c706_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialAssemblyFiberNormed
local instance polynomialAssemblySectionNormed_rd4c706_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialAssemblySectionSpace_rd4c706_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem polynomial_linearized_representatives {n : A.centers → ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (hP : ∀ j k r, (P j k r).SmoothCoeffs univ) :
    ∃ Q : A.centers → Fin 3 → Fin (polynomialFamilyDegree n) → Expression,
      (∀ i k r, (Q i k r).SmoothCoeffs univ) ∧
      A.PolynomialQuadraticRepresentation P Q ∧
      ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
      ∀ (X : A.centers → RealModes.RField 4), (∀ i, ContDiff ℝ ∞ (X i)) →
      (∀ i, tsupport (X i) ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) →
      ∀ ε : ℝ,
        A.atlasPolynomialVariation P ε F (spaceCoordinates.symm ∘ A.vectorPlaneRestore X) =
          A.tensorPlaneRestore (fun i => coordinateRealLinearized (Q i) ε (A.jetChartMap i F) (X i) 0) := by
  classical
  choose Q hQ _ hfirst hsecond using fun i => A.atlas_polynomial_local_model P hP i
  refine ⟨Q,hQ,?_,?_⟩
  · intro F X hF hX i x hx ε
    exact hsecond i F X hF hX x hx ε
  · intro F hF X hX hsp ε
    let Y : A.centers → M → Space := fun i => restore (i : M) (A.outer i)
      ((spaceCoordinates.symm ∘ X i) ∘ planeCoordinateIsometry)
    have hY (i : A.centers) : ContMDiff planeModel spaceModel ∞ (Y i) :=
      restore_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
        ((spaceCoordinates.symm.contDiff.comp (hX i)).comp planeCoordinateIsometry.contDiff)
    have hdir (i : A.centers) : A.atlasPolynomialVariation P ε F (Y i) =
        A.bundleRestore A.tensorTriv i (fun x => fiberFromThree
          (coordinateRealLinearized (Q i) ε (A.jetChartMap i F) (X i) 0 (planeCoordinateIsometry x))) := by
      apply A.restored_polynomial_direction P i (Q i) F (X i) (hsp i) ε
      intro x hx
      have hh := hfirst i F (Y i) hF (hY i) x hx ε
      have he : A.jetChartMap i (Y i) ∘ planeCoordinateIsometry.symm = X i := by
        rw [show Y i = restore (i : M) (A.outer i)
          ((spaceCoordinates.symm ∘ X i) ∘ planeCoordinateIsometry) from rfl,
          A.jetChartMap_restored_direction i (X i) (hsp i)]
        funext y
        simp only [Function.comp_apply,planeCoordinateIsometry.apply_symm_apply]
      rwa [he] at hh
    have he : spaceCoordinates.symm ∘ A.vectorPlaneRestore X = ∑ i : A.centers, Y i :=
      A.euclidean_vectorPlaneRestore X
    rw [he,A.atlasPolynomialVariation_sum P ε F Finset.univ Y hY]
    funext p
    simp only [tensorPlaneRestore,Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    exact congrFun (hdir i) p

theorem full_linearized_representatives_oai {n : A.centers → ℕ}
    (P : ∀ j : A.centers, Fin 3 → Fin (n j) → Expression)
    (hP : ∀ j k r, (P j k r).SmoothCoeffs univ) :
    ∃ Q : A.centers → Fin 3 → Fin (polynomialFamilyDegree n) → Expression,
      (∀ i k r, (Q i k r).SmoothCoeffs univ) ∧
      A.PolynomialQuadraticRepresentation P Q ∧
      A.PolynomialLinearRepresentation P Q := by
  obtain ⟨Q,hQ,hquad,hpoly⟩ := A.polynomial_linearized_representatives P hP
  refine ⟨Q,hQ,hquad,?_⟩
  intro F hF X hX hsp ε
  rw [A.euclidean_vectorPlaneRestore_linearized hF X hX hsp,hpoly F hF X hX hsp ε,
    ← A.tensorPlaneRestore_add]
  congr 1

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.full_linearized_representatives_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.full_linearized_representatives_oai.{u_1}
