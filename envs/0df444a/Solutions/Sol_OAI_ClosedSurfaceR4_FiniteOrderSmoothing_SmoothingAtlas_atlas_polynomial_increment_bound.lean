-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_increment_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:32:17.630369+00:00
-- url     : https://prove2.me/submissions/9aea892a-d20b-4115-b145-1f00f7067f99

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI010
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_global_cubic_remainder_bound

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_OscillatoryModel
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.SmallModes

lemma partial_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : Base → E} {p : Base} (hF : DifferentiableAt ℝ F p)
    (hG : DifferentiableAt ℝ G p) (v : Base) :
    coordDeriv v (fun q => F q + G q) p = coordDeriv v F p + coordDeriv v G p := by
  simp only [coordDeriv, fderiv_fun_add hF hG, add_apply]

end ClosedSurfaceR4.SmallModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ForcedModes
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
open ClosedSurfaceR4.QuadraticMean (realPartCLM)

lemma realMetric_add {n : ℕ} {F U : RField n} {p : Base}
    (hF : DifferentiableAt ℝ F p) (hU : DifferentiableAt ℝ U p) (v w : Base) :
    realMetric (fun q => F q + U q) v w p =
      realMetric F v w p + realLinearized F U v w p + realMetric U v w p := by
  unfold realMetric realLinearized
  rw [partial_add hF hU v, partial_add hF hU w]
  simp only [add_dotProduct, dotProduct_add]
  rw [dotProduct_comm (coordDeriv v U p)]
  ring

end ClosedSurfaceR4.RealModes

end

end OAI
end

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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_DoubleModes
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

lemma realMetricTensor_add {n : ℕ} {F X : RField n} {p : Base}
    (hF : DifferentiableAt ℝ F p) (hX : DifferentiableAt ℝ X p) :
    realMetricTensor (fun q => F q + X q) p =
      realMetricTensor F p + realLinearizedTensor F X p + realMetricTensor X p := by
  ext i
  simp only [Pi.add_apply, realMetricTensor_apply, realLinearizedTensor_apply,
    realMetric_add hF hX]


end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_TensorBounds
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

lemma contDiffOn_realLinearizedTensor {n : ℕ} {U : Set Base} (hU : IsOpen U) {X Y : RField n}
    (hX : ContDiffOn ℝ ∞ X U) (hY : ContDiffOn ℝ ∞ Y U) :
    ContDiffOn ℝ ∞ (realLinearizedTensor X Y) U := by
  apply contDiffOn_pi.mpr
  intro i
  simp only [realLinearizedTensor_apply, realLinearized]
  exact (contDiffOn_realDot (contDiffOn_coordDeriv_vector hU hX _)
    (contDiffOn_coordDeriv_vector hU hY _)).add
    (contDiffOn_realDot (contDiffOn_coordDeriv_vector hU hX _)
      (contDiffOn_coordDeriv_vector hU hY _))

end ClosedSurfaceR4.RealModes

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
local instance planeReadSectionSpace_r8ced5e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorPlaneRestore_sub (f g : A.centers → SmallModes.Base → Tensor) :
    A.tensorPlaneRestore (f-g) = A.tensorPlaneRestore f - A.tensorPlaneRestore g := by
  funext p
  simp only [tensorPlaneRestore, Pi.sub_apply, map_sub, bundleRestore, smul_sub,
    Finset.sum_sub_distrib]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MixedJetRegularity
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spatial order and smoothness of mixed jet expressions. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MixedExpression

theorem eval_smooth {O : Set LowJet} {U : Set Base} {G : Fin 4 → Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (hQ : Set.MapsTo (lowJet (G 0)) U O)
    {e : MixedExpression} (he : e.SmoothCoeffs O) :
    ContDiffOn ℝ ∞ (e.eval G) (U ×ˢ Set.univ) := by
  induction e with
  | coeff c =>
    exact he.comp (((lowJet_smooth (hG 0)).comp contDiff_fst).prodMk contDiff_snd).contDiffOn
      (fun z hz => ⟨hQ hz.1, hz.2⟩)
  | atom i w a e ih =>
    exact (((jet_smooth (hG i) w a).comp contDiff_fst).contDiffOn.mul (ih he))
  | add e f ihe ihf => exact (ihe he.1).add (ihf he.2)

lemma parameter_smooth {O : Set LowJet} {U : Set Base} {G : Fin 4 → Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (hQ : Set.MapsTo (lowJet (G 0)) U O)
    {e : MixedExpression} (he : e.SmoothCoeffs O) (t : ℝ) :
    ContDiffOn ℝ ∞ (fun p => e.eval G (p, t)) U :=
  (eval_smooth hG hQ he).comp (contDiffOn_id.prodMk contDiffOn_const)
    (fun _ hp => ⟨hp, Set.mem_univ t⟩)

end ClosedSurfaceR4.JetPolynomial.MixedExpression

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MixedJetHomogeneity
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Homogeneity in each variation slot, including the zero polynomial. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MixedExpression

lemma scaleSlot_base (G : Fin 4 → Base → Space) (j : Fin 3) (c : ℝ) :
    scaleSlot G j c 0 = G 0 := by
  funext p
  simp only [scaleSlot, Ne.symm (Fin.succ_ne_zero j), ↓reduceIte]

theorem DegreeIn.eval_scaleSlot {j : Fin 3} {e : MixedExpression} {n : ℕ}
    (h : DegreeIn j e n) {G : Fin 4 → Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (c : ℝ) (z : Base × ℝ) :
    e.eval (scaleSlot G j c) z = c ^ n * e.eval G z := by
  induction h with
  | coeff d => simp only [eval, scaleSlot_base, pow_zero, one_mul]
  | zero n => simp only [eval, mul_zero]
  | other i w a hi h ih =>
    have he : scaleSlot G j c i = G i := by
      funext p
      simp only [scaleSlot, hi, ↓reduceIte]
    simp only [eval, he, ih]
    ring
  | same w a h ih =>
    have he : scaleSlot G j c j.succ = fun p => c • G j.succ p := by
      funext p
      simp only [scaleSlot, ↓reduceIte]
    simp only [eval, he, jet_smul (hG j.succ), ih, pow_succ]
    ring
  | add he hf ihe ihf => simp only [eval, ihe, ihf, mul_add]

end ClosedSurfaceR4.JetPolynomial.MixedExpression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialVariationBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first three actual polynomial variations have one fixed scale
exponent, the excess-jet loss plus six. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates MixedExpression

namespace Expression

lemma first_variation_eval {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) {G : Fin 4 → Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (z : Base × ℝ) (hQ : lowJet (G 0) z.1 ∈ O) :
    (e.variations 0).eval G z = e.variation (G 0) (G 1) z := by
  have ha := differentiate_hasDerivAt hO hG (smoothCoeffs_ofExpression he) 0 z hQ
  have hb := variation_hasDerivAt hO (hG 0) (hG 1) he z hQ
  have ha' : HasDerivAt (fun s : ℝ => e.eval (fun p => G 0 p + s • G 1 p) z)
      ((e.variations 0).eval G z) 0 := by
    change HasDerivAt _ (((ofExpression e).differentiate 0).eval G z) 0
    simpa only [ofExpression_eval, varyBase_base, Fin.succ_zero_eq_one] using ha
  exact ha'.unique hb

end Expression
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

lemma inducedForm_add {F U : M → V} {p : M}
    (hF : MDifferentiableAt planeModel 𝓘(ℝ,V) F p)
    (hU : MDifferentiableAt planeModel 𝓘(ℝ,V) U p) (v w : TangentSpace planeModel p) :
    inducedForm (F+U) p v w - inducedForm F p v w =
      linearMetricForm F U p v w + inducedForm U p v w := by
  unfold inducedForm linearMetricForm
  rw [surfaceDifferential_add hF hU]
  simp only [add_apply,inner_add_left,inner_add_right]
  ring

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ManifoldMetricTensor
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.Path.extend_div_self
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

local instance metricTensorFiberNormed_r8ced5e_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance metricTensorFiberSpace_r8ced5e_1 : NormedSpace ℝ TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricTangentNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricTangentSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricTensorDualAdd
local instance metricTensorDualSmul_r8ced5e_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance metricTensorSectionNormed_r8ced5e_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricTensorSectionSpace_r8ced5e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma linearMetricTensor_apply (F U : M → Space) (p : M) (v w : TangentSpace planeModel p) :
    linearMetricTensor F U p v w = linearMetricForm F U p v w := rfl

lemma inducedTensor_add {F U : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hU : ContMDiff planeModel spaceModel ∞ U) :
    inducedTensor (F+U) = inducedTensor F + linearMetricTensor F U + inducedTensor U := by
  funext p
  ext v w
  have h := inducedForm_add ((hF p).mdifferentiableAt (by simp))
    ((hU p).mdifferentiableAt (by simp)) v w
  change inducedForm (F+U) p v w = inducedForm F p v w +
    linearMetricForm F U p v w + inducedForm U p v w
  linarith

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasLinearizedMetric
attribute [-instance] _root_.instVAddIntReal_solutions
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

local instance atlasLinearFiberNormed_r8ced5e_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasLinearFiberSpace_r8ced5e_1 : NormedSpace ℝ TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasLinearDualAdd
local instance atlasLinearDualSmul_r8ced5e_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance atlasLinearSectionNormed_r8ced5e_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasLinearSectionSpace_r8ced5e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma linearMetricTensor_finite_sum {ι : Type*} [Fintype ι]
    (F : M → Space) (f : ι → M → Space) (hf : ∀ i, ContMDiff planeModel spaceModel ∞ (f i)) :
    linearMetricTensor F (∑ i, f i) = fun p => ∑ i, linearMetricTensor F (f i) p := by
  funext p
  ext v w
  simpa only [sum_apply,linearMetricTensor_apply] using
    linearMetricForm_finite_sum F f (fun i => ((hf i) p).mdifferentiableAt (by simp)) v w

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_LinearMetricChartReconstruction
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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
local instance linearReadFiberNormed_r8ced5e_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance linearReadFiberSpace_r8ced5e_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance linearReadDualAdd_r8ced5e_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance linearReadDualSmul_r8ced5e_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.linearReadSectionNormed
local instance linearReadSectionSpace_r8ced5e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma vectorPlaneRead_add {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : A.centers) (F G : M → V) :
    A.vectorPlaneRead i (F+G) = A.vectorPlaneRead i F + A.vectorPlaneRead i G := by
  funext x
  by_cases hx : planeCoordinateIsometry.symm x ∈ (chart (i : M)).target <;>
    simp [vectorPlaneRead,vectorChartRead,localize,hx,smul_add]

theorem linearMetric_from_chart_reads {F G : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hG : ContMDiff planeModel spaceModel ∞ G) :
    A.tensorPlaneRestore (fun i y => (A.planeWeight i y)^2 •
      RealModes.realLinearizedTensor (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (spaceCoordinates ∘ A.vectorPlaneRead i G) y) = linearMetricTensor F G := by
  have he := A.metric_from_chart_reads (hF.add hG)
  rw [inducedTensor_add hF hG] at he
  have hlocal : (fun i y => (A.planeWeight i y)^2 •
      RealModes.realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i (F+G)) y) =
      (fun i y => (A.planeWeight i y)^2 •
        RealModes.realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) y) +
      (fun i y => (A.planeWeight i y)^2 •
        RealModes.realLinearizedTensor (spaceCoordinates ∘ A.vectorPlaneRead i F)
          (spaceCoordinates ∘ A.vectorPlaneRead i G) y) +
      (fun i y => (A.planeWeight i y)^2 •
        RealModes.realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i G) y) := by
    funext i y
    rw [A.vectorPlaneRead_add]
    have hc : spaceCoordinates ∘ (A.vectorPlaneRead i F + A.vectorPlaneRead i G) =
        fun x => (spaceCoordinates ∘ A.vectorPlaneRead i F) x +
          (spaceCoordinates ∘ A.vectorPlaneRead i G) x := by
      funext x
      exact map_add spaceCoordinates _ _
    rw [hc,RealModes.realMetricTensor_add
      ((spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) y)
      ((spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hG)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) y)]
    simp only [smul_add,Pi.add_apply]
  rw [hlocal,A.tensorPlaneRestore_add,A.tensorPlaneRestore_add,
    A.metric_from_chart_reads hF,A.metric_from_chart_reads hG] at he
  exact add_left_cancel (add_right_cancel he)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasMetricBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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
local instance metricBoundSectionNormed_r8ced5e_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricBoundSectionSpace_r8ced5e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma linearMetricTensor_smooth {F G : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hG : ContMDiff planeModel spaceModel ∞ G) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (linearMetricTensor F G p)) := by
  rw [← A.linearMetric_from_chart_reads hF hG]
  apply A.tensorPlaneRestore_smooth
  intro i
  apply ((A.planeWeight_smooth i).pow 2).smul
  exact contDiffOn_univ.mp (RealModes.contDiffOn_realLinearizedTensor isOpen_univ
    (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)).contDiffOn
    (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hG)).contDiffOn)

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialAffineFamily
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Joint smoothness in position and a variation parameter for actual
higher-jet polynomial expressions. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression

lemma jet_affine_joint_smooth {G H : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (w : List (Fin 2)) (a : Fin 4) :
    ContDiff ℝ ∞ (fun z : Base × ℝ => jet (fun p => G p + z.2 • H p) w a z.1) := by
  have he : (fun z : Base × ℝ => jet (fun p => G p + z.2 • H p) w a z.1) =
      fun z => jet G w a z.1 + z.2 * jet H w a z.1 := by
    funext z
    rw [jet_add hG (hH.const_smul z.2), jet_smul hH]
  rw [he]
  exact ((jet_smooth hG w a).comp contDiff_fst).add
    (contDiff_snd.mul ((jet_smooth hH w a).comp contDiff_fst))

lemma lowJet_affine_joint_smooth {G H : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fun z : Base × ℝ => lowJet (fun p => G p + z.2 • H p) z.1) := by
  have he : (fun z : Base × ℝ => lowJet (fun p => G p + z.2 • H p) z.1) =
      fun z => lowJet G z.1 + z.2 • variationLowJet H z.1 := by
    funext z
    exact lowJet_affine hG hH z.2 z.1
  rw [he]
  exact ((lowJet_smooth hG).comp contDiff_fst).add
    (contDiff_snd.smul ((variationLowJet_smooth hH).comp contDiff_fst))

namespace MixedExpression

lemma jet_varyBase_joint_smooth {G : Fin 4 → Base → Space} {H : Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (hH : ContDiff ℝ ∞ H)
    (i : Fin 4) (w : List (Fin 2)) (a : Fin 4) :
    ContDiff ℝ ∞ (fun z : Base × ℝ => jet (varyBase G H z.2 i) w a z.1) := by
  by_cases hi : i = 0
  · subst i
    simpa only [varyBase_base] using jet_affine_joint_smooth (hG 0) hH w a
  · simpa only [varyBase_other G H _ hi, Function.comp_def] using (jet_smooth (hG i) w a).comp contDiff_fst

/-- Global coefficient smoothness is obtained on the application compact set
by `Expression.exists_global_extension`. -/
theorem eval_varyBase_joint_smooth {G : Fin 4 → Base → Space} {H : Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (hH : ContDiff ℝ ∞ H)
    {e : MixedExpression} (he : e.SmoothCoeffs Set.univ) (θ : ℝ) :
    ContDiff ℝ ∞ (fun z : Base × ℝ => e.eval (varyBase G H z.2) (z.1, θ)) := by
  induction e with
  | coeff c =>
    have hc : ContDiff ℝ ∞ c := contDiffOn_univ.mp (by simpa only [SmoothCoeffs, Set.univ_prod_univ] using he)
    have hh := hc.comp ((lowJet_affine_joint_smooth (hG 0) hH).prodMk (contDiff_const (c := θ)))
    simpa only [eval, varyBase_base, Function.comp_def] using hh
  | atom i w a e ih =>
    exact (jet_varyBase_joint_smooth hG hH i w a).mul (ih he)
  | add e f ihe ihf => exact (ihe he.1).add (ihf he.2)

end MixedExpression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialAffineDerivative
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual polynomial variations at every point of an affine path, rather
than only at the parameter origin. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MixedExpression

lemma varyBase_smooth {G : Fin 4 → Base → Space} {H : Base → Space}
    (hG : ∀ i, ContDiff ℝ ∞ (G i)) (hH : ContDiff ℝ ∞ H) (t : ℝ) :
    ∀ i, ContDiff ℝ ∞ (varyBase G H t i) := by
  intro i
  by_cases hi : i = 0
  · subst i
    rw [varyBase_base]
    exact (hG 0).add (hH.const_smul t)
  · rw [varyBase_other G H t hi]
    exact hG i

lemma varyBase_add (G : Fin 4 → Base → Space) (H : Base → Space) (t s : ℝ) :
    varyBase (varyBase G H t) H s = varyBase G H (t + s) := by
  funext i p
  by_cases hi : i = 0
  · simp only [varyBase, hi, ↓reduceIte, add_smul]
    abel
  · simp only [varyBase, hi, ↓reduceIte]

theorem differentiate_hasDerivAt_at {O : Set LowJet} (hO : IsOpen O)
    {G : Fin 4 → Base → Space} (hG : ∀ i, ContDiff ℝ ∞ (G i))
    {e : MixedExpression} (he : e.SmoothCoeffs O) (j : Fin 3) (t : ℝ) (z : Base × ℝ)
    (hQ : lowJet (varyBase G (G j.succ) t 0) z.1 ∈ O) :
    HasDerivAt (fun s : ℝ => e.eval (varyBase G (G j.succ) s) z)
      ((e.differentiate j).eval (varyBase G (G j.succ) t) z) t := by
  have hd := differentiate_hasDerivAt hO (varyBase_smooth hG (hG j.succ) t) he j z hQ
  rw [varyBase_other G (G j.succ) t (Fin.succ_ne_zero j)] at hd
  have hd' : HasDerivAt
      (fun s : ℝ => e.eval (varyBase (varyBase G (G j.succ) t) (G j.succ) s) z)
      ((e.differentiate j).eval (varyBase G (G j.succ) t) z) (t - t) := by
    simpa only [sub_self] using hd
  have hs := hd'.comp_sub_const t t
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  funext s
  rw [varyBase_add]
  congr 2
  ring

end ClosedSurfaceR4.JetPolynomial.MixedExpression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ParameterTaylorRemainder
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cubic Taylor remainders retain all weighted spatial derivative bounds
under integration in the variation parameter. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff

universe u
namespace ClosedSurfaceR4.ParameterTaylor
open SmoothPeriodicCalculus SmoothParameterIntegral WeightedEstimates

variable {A E : Type u} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma parameterJet_smooth {F : A × ℝ → E} (hF : ContDiff ℝ ∞ F) (j : ℕ) :
    ContDiff ℝ ∞ (parameterJet j F) := by
  induction j with
  | zero => exact hF
  | succ j ih => exact contDiff_angleDerivative ih

lemma cubicRemainder_smooth {F : A × ℝ → E} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (cubicRemainder F) :=
  (((hF.comp (contDiff_id.prodMk contDiff_const)).sub
    (hF.comp (contDiff_id.prodMk contDiff_const))).sub
    ((parameterJet_smooth hF 1).comp (contDiff_id.prodMk contDiff_const))).sub
    (((parameterJet_smooth hF 2).comp (contDiff_id.prodMk contDiff_const)).const_smul (1 / 2 : ℝ))

end ClosedSurfaceR4.ParameterTaylor

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialDiagonalVariations
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first three actual parameter derivatives of a polynomial along a
map variation are its mixed variations with all directions equal. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression ParameterTaylor SmoothPeriodicCalculus

lemma diagonalFamily_smooth {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) :
    ∀ i, ContDiff ℝ ∞ (diagonalFamily G H i) := by
  intro i
  refine Fin.cases hG (fun _ => hH) i

lemma diagonalFamily_succ (G H : Base → Space) (j : Fin 3) : diagonalFamily G H j.succ = H := rfl

lemma diagonal_angleDerivative {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    {e : MixedExpression} (he : e.SmoothCoeffs Set.univ) (j : Fin 3) (θ : ℝ) (z : Base × ℝ) :
    angleDerivative (fun x : Base × ℝ => e.eval (varyBase (diagonalFamily G H) H x.2) (x.1, θ)) z =
      (e.differentiate j).eval (varyBase (diagonalFamily G H) H z.2) (z.1, θ) := by
  have hs := eval_varyBase_joint_smooth (diagonalFamily_smooth hG hH) hH he θ
  have hd := differentiate_hasDerivAt_at isOpen_univ (diagonalFamily_smooth hG hH) he j z.2
    (z.1, θ) (Set.mem_univ _)
  simp only [diagonalFamily_succ] at hd
  exact (angle_hasDerivAt hs z.1 z.2).unique hd

namespace Expression

lemma affinePolynomial_smooth {e : Expression} (he : e.SmoothCoeffs Set.univ)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (θ : ℝ) :
    ContDiff ℝ ∞ (e.affinePolynomial G H θ) :=
  eval_varyBase_joint_smooth (diagonalFamily_smooth hG hH) hH (smoothCoeffs_ofExpression he) θ

lemma affinePolynomial_first {e : Expression} (he : e.SmoothCoeffs Set.univ)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (θ : ℝ) :
    parameterJet 1 (e.affinePolynomial G H θ) =
      fun z => (e.variations 0).eval (varyBase (diagonalFamily G H) H z.2) (z.1, θ) := by
  funext z
  exact diagonal_angleDerivative hG hH (smoothCoeffs_ofExpression he) 0 θ z

lemma affinePolynomial_second {e : Expression} (he : e.SmoothCoeffs Set.univ)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (θ : ℝ) :
    parameterJet 2 (e.affinePolynomial G H θ) =
      fun z => (e.variations 1).eval (varyBase (diagonalFamily G H) H z.2) (z.1, θ) := by
  change angleDerivative (parameterJet 1 (e.affinePolynomial G H θ)) = _
  rw [affinePolynomial_first he hG hH]
  funext z
  exact diagonal_angleDerivative hG hH (e.variations_smoothCoeffs isOpen_univ he 0) 1 θ z

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialTaylorRemainder
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The weighted cubic estimate for the actual higher-jet polynomial map. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.Expression
open MixedExpression ParameterTaylor SmoothParameterIntegral WeightedEstimates

lemma affinePolynomial_apply (e : Expression) (G H : Base → Space) (θ : ℝ) (z : Base × ℝ) :
    e.affinePolynomial G H θ z = e.eval (fun p => G p + z.2 • H p) (z.1, θ) := by
  rw [affinePolynomial, ofExpression_eval, varyBase_base]
  rfl

lemma cubicRemainder_affine {e : Expression} (he : e.SmoothCoeffs Set.univ)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (θ : ℝ) :
    cubicRemainder (e.affinePolynomial G H θ) = e.taylorRemainder G H θ := by
  funext p
  unfold cubicRemainder taylorRemainder
  rw [affinePolynomial_first he hG hH, affinePolynomial_second he hG hH]
  simp only [affinePolynomial_apply, one_smul, zero_smul, add_zero, varyBase_zero]
  rw [e.first_variation_eval isOpen_univ he (diagonalFamily_smooth hG hH) (p, θ) (Set.mem_univ _)]
  rfl

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SecondVariationAlgebra
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact algebra of the real second variation, including its unused
third direction slot. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open MixedExpression

lemma second_diagonal_eq_pair (e : Expression) {G H : Base → Space}
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (z : Base × ℝ) :
    (e.variations 1).eval (diagonalFamily G H) z =
      (e.variations 1).eval ![G,H,H,0] z := by
  have hd : DegreeIn 2 (e.variations 1) 0 := by simpa using e.variations_degree 1 2
  have hh := hd.eval_scaleSlot (diagonalFamily_smooth hG hH) 0 z
  have hf : scaleSlot (diagonalFamily G H) 2 0 = ![G,H,H,0] := by
    funext i p
    fin_cases i
    · rfl
    · rfl
    · rfl
    · simp [scaleSlot]
  rw [hf, pow_zero, one_mul] at hh
  exact hh.symm

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PerturbationTaylorBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite polynomial perturbation has a cubic nonlinear remainder with
one fixed scale loss. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open MixedExpression ParameterTaylor WeightedEstimates

variable {n : ℕ}

lemma expression_taylorRemainder_smooth {e : Expression} (he : e.SmoothCoeffs Set.univ)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (θ : ℝ) :
    ContDiff ℝ ∞ (e.taylorRemainder G H θ) := by
  rw [← Expression.cubicRemainder_affine he hG hH θ]
  exact cubicRemainder_smooth (Expression.affinePolynomial_smooth he hG hH θ)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_RealPolynomialQuadraticBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bilinear bounds for the mixed polynomial contribution of the free and
forced displacements. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates MixedExpression

lemma pairFamily_smooth {G H K : Base → Space} (hG : ContDiff ℝ ∞ G)
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) :
    ∀ i, ContDiff ℝ ∞ (![G,H,K,0] i) := by
  intro i
  fin_cases i
  · exact hG
  · exact hH
  · exact hK
  · exact contDiff_const

lemma realVariation_smooth {n : ℕ} {P : Fin n → Expression}
    {U : Set Base} {O : Set LowJet} (hO : IsOpen O) (hP : ∀ l, (P l).SmoothCoeffs O)
    {G : Fin 4 → Base → Space} (hG : ∀ j, ContDiff ℝ ∞ (G j))
    (hQ : Set.MapsTo (lowJet (G 0)) U O) (ε : ℝ) (i : Fin 3) (t : ℝ) :
    ContDiffOn ℝ ∞ (realVariation P ε G i t) U :=
  ContDiffOn.sum fun l _ => contDiffOn_const.mul
    (MixedExpression.parameter_smooth hG hQ ((P l).variations_smoothCoeffs hO (hP l) i) t)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorRealVariationBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common tensor bounds for the actual mixed quadratic term and cubic
Taylor remainder. The exponent does not depend on the correction depth. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

lemma tensorQuadraticCross_smooth {n : ℕ} {P : Fin 3 → Fin n → Expression}
    (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ)
    {G H K : Base → Space} (hG : ContDiff ℝ ∞ G)
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) (ε t : ℝ) :
    ContDiff ℝ ∞ (tensorQuadraticCross P ε G H K t) := by
  apply contDiff_pi.mpr
  intro k
  apply contDiffOn_univ.mp
  exact contDiffOn_const.mul
    ((realVariation_smooth isOpen_univ (hP k) (pairFamily_smooth hG hH hK)
      (fun _ _ => Set.mem_univ _) ε 1 t).add
    (realVariation_smooth isOpen_univ (hP k) (pairFamily_smooth hG hK hH)
      (fun _ _ => Set.mem_univ _) ε 1 t))

lemma tensorTaylorRemainder_smooth {n : ℕ} {P : Fin 3 → Fin n → Expression}
    (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H) (ε t : ℝ) :
    ContDiff ℝ ∞ (tensorTaylorRemainder P ε G H t) := by
  apply contDiff_pi.mpr
  intro k
  change ContDiff ℝ ∞ (fun p => ∑ l, ε ^ (l.val + 1) * (P k l).taylorRemainder G H t p)
  exact ContDiff.sum fun l _ => contDiff_const.mul
    (expression_taylorRemainder_smooth (hP k l) hG hH t)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CoordinateNonlinearBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate realizations of the actual bilinear and cubic polynomial
terms in the nonlinear increment identity. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

lemma coordinateQuadraticPolynomial_eq_cross {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space)
    (X : RealModes.RField 4) (t : ℝ) :
    coordinateQuadraticPolynomial P ε G X t = fun p => (1 / 2 : ℝ) •
      tensorQuadraticCross P ε G (X ∘ planeCoordinateIsometry) (X ∘ planeCoordinateIsometry) t
        (planeCoordinateIsometry.symm p) := by
  funext p k
  simp only [coordinateQuadraticPolynomial, tensorQuadraticCross, quadraticCross,
    realVariation, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_add, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  ring

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
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

lemma coordinate_polynomial_taylor_identity {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) {G : Base → Space}
    {X : RealModes.RField 4} (hG : ContDiff ℝ ∞ G) (hX : ContDiff ℝ ∞ X) :
    coordinatePolynomialValue P ε (fun x => G x+X (planeCoordinateIsometry x)) 0-
      coordinatePolynomialValue P ε G 0 =
      coordinateRealLinearized P ε G X 0 + coordinateQuadraticPolynomial P ε G X 0 +
        coordinateTaylorRemainder P ε G X := by
  funext p k
  simp only [coordinateRealLinearized,coordinateQuadraticPolynomial,coordinatePolynomialValue,
    coordinateTaylorRemainder,linearized,Pi.add_apply,Pi.sub_apply,Expression.taylorRemainder]
  simp only [second_diagonal_eq_pair _ hG (hX.comp planeCoordinateIsometry.contDiff),
    mul_sub,Finset.sum_sub_distrib,Function.comp_apply]
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

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
local instance polynomialMetricSectionNormed_r8ced5e_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialMetricSectionSpace_r8ced5e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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

lemma atlas_polynomial_taylor_identity
    (P : (i : A.centers) → Fin 3 → Fin (n i) → Expression) (ε : ℝ)
    {G X : M → Space} (hG : ContMDiff planeModel spaceModel ∞ G)
    (hX : ContMDiff planeModel spaceModel ∞ X) :
    A.atlasPolynomialValue P ε (G+X)-A.atlasPolynomialValue P ε G =
      A.atlasPolynomialVariation P ε G X+A.atlasPolynomialQuadratic P ε G X+
        A.atlasPolynomialRemainder P ε G X := by
  unfold atlasPolynomialValue atlasPolynomialVariation atlasPolynomialQuadratic atlasPolynomialRemainder
  rw [← A.tensorPlaneRestore_sub,← A.tensorPlaneRestore_add,← A.tensorPlaneRestore_add]
  congr 1
  funext i
  simp only [Pi.sub_apply,Pi.add_apply]
  rw [A.jetChartMap_add]
  have hh := coordinate_polynomial_taylor_identity (P i) ε (A.jetChartMap_smooth i hG)
    ((A.jetChartMap_smooth i hX).comp planeCoordinateIsometry.symm.contDiff)
  change coordinatePolynomialValue (P i) ε (fun x => A.jetChartMap i G x+A.jetChartMap i X x) 0-
    coordinatePolynomialValue (P i) ε (A.jetChartMap i G) 0 = _
  simpa only [Function.comp_apply,planeCoordinateIsometry.symm_apply_apply] using hh

lemma atlas_polynomial_metric_taylor_identity
    (P : (i : A.centers) → Fin 3 → Fin (n i) → Expression) (ε : ℝ)
    {G X : M → Space} (hG : ContMDiff planeModel spaceModel ∞ G)
    (hX : ContMDiff planeModel spaceModel ∞ X) :
    A.atlasPolynomialMetric P ε (G+X)-A.atlasPolynomialMetric P ε G =
      (linearMetricTensor G X+A.atlasPolynomialVariation P ε G X)+
      (inducedTensor X+A.atlasPolynomialQuadratic P ε G X)+
        A.atlasPolynomialRemainder P ε G X := by
  have hp := A.atlas_polynomial_taylor_identity P ε hG hX
  have hm := inducedTensor_add hG hX
  unfold atlasPolynomialMetric
  rw [hm]
  have hi : (inducedTensor G+linearMetricTensor G X+inducedTensor X+
      A.atlasPolynomialValue P ε (G+X))-(inducedTensor G+A.atlasPolynomialValue P ε G) =
      linearMetricTensor G X+inducedTensor X+
        (A.atlasPolynomialValue P ε (G+X)-A.atlasPolynomialValue P ε G) := by abel
  rw [hi,hp]
  abel

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialLinearity
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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
local instance polynomialLinearFiberNormed_r8ced5e_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialLinearFiberSpace_r8ced5e_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance polynomialLinearDualSmul_r8ced5e_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance polynomialLinearSectionNormed_r8ced5e_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialLinearSectionSpace_r8ced5e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ScaledNonlinearBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual mixed and cubic nonlinear errors at the scales of the small
increment construction. -/
noncomputable section
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates

lemma coordinateQuadraticPolynomial_smooth {n : ℕ} {P : Fin 3 → Fin n → Expression}
    (hP : ∀ k l, (P k l).SmoothCoeffs Set.univ) {G : Base → Space}
    {X : RealModes.RField 4} (hG : ContDiff ℝ ∞ G) (hX : ContDiff ℝ ∞ X) (ε t : ℝ) :
    ContDiff ℝ ∞ (coordinateQuadraticPolynomial P ε G X t) := by
  rw [coordinateQuadraticPolynomial_eq_cross]
  exact ((tensorQuadraticCross_smooth hP hG (hX.comp planeCoordinateIsometry.contDiff)
    (hX.comp planeCoordinateIsometry.contDiff) ε t).comp
    planeCoordinateIsometry.symm.contDiff).const_smul (1 / 2 : ℝ)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialSmooth
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The restored polynomial value has one fixed finite loss. Compact local
jet ranges suffice: a fixed cutoff removes the irrelevant values away from
the outer atlas supports before applying the restoration estimate. -/
noncomputable section
open Set Manifold Bundle TopologicalSpace
open scoped ContDiff Manifold Topology BigOperators NNReal

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialSmoothFiberSpace
local instance polynomialSmoothDualAdd_r8ced5e_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialSmoothDualSmul
variable (A : SmoothingAtlas M)




attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialSmoothFiberNormed
local instance polynomialSmoothSectionNormed_r8ced5e_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialSmoothSectionSpace_r8ced5e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma atlasPolynomialVariation_smooth {n : A.centers → ℕ}
    {P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ) {F X : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hX : ContMDiff planeModel spaceModel ∞ X)
    (ε : ℝ) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (A.atlasPolynomialVariation P ε F X p)) := by
  apply A.tensorPlaneRestore_smooth
  intro i
  apply contDiff_pi.mpr
  intro k
  change ContDiff ℝ ∞ (fun p => ∑ l, ε^(l.val+1) *
    (P i k l).variation (A.jetChartMap i F)
      ((A.jetChartMap i X ∘ planeCoordinateIsometry.symm) ∘ planeCoordinateIsometry)
      (planeCoordinateIsometry.symm p,0))
  apply ContDiff.sum
  intro l _
  apply contDiff_const.mul
  have hs := (P i k l).variation_smooth (U := univ) isOpen_univ
    (A.jetChartMap_smooth i hF)
    (((A.jetChartMap_smooth i hX).comp planeCoordinateIsometry.symm.contDiff).comp
      planeCoordinateIsometry.contDiff) (fun _ _ => mem_univ _) (hP i k l)
  have hs' : ContDiff ℝ ∞ ((P i k l).variation (A.jetChartMap i F)
      ((A.jetChartMap i X ∘ planeCoordinateIsometry.symm) ∘ planeCoordinateIsometry)) := by
    apply contDiffOn_univ.mp
    simpa only [univ_prod_univ] using hs
  exact hs'.comp (planeCoordinateIsometry.symm.contDiff.prodMk contDiff_const)

lemma atlasPolynomialQuadratic_smooth {n : A.centers → ℕ}
    {P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ) {F X : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hX : ContMDiff planeModel spaceModel ∞ X)
    (ε : ℝ) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (A.atlasPolynomialQuadratic P ε F X p)) :=
  A.tensorPlaneRestore_smooth (fun i => coordinateQuadraticPolynomial_smooth (hP i)
    (A.jetChartMap_smooth i hF)
    ((A.jetChartMap_smooth i hX).comp planeCoordinateIsometry.symm.contDiff) ε 0)

lemma atlasPolynomialRemainder_smooth {n : A.centers → ℕ}
    {P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k l, (P i k l).SmoothCoeffs univ) {F X : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hX : ContMDiff planeModel spaceModel ∞ X)
    (ε : ℝ) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (A.atlasPolynomialRemainder P ε F X p)) :=
  A.tensorPlaneRestore_smooth (fun i =>
    (tensorTaylorRemainder_smooth (hP i) (A.jetChartMap_smooth i hF)
      (((A.jetChartMap_smooth i hX).comp planeCoordinateIsometry.symm.contDiff).comp
        planeCoordinateIsometry.contDiff) ε 0).comp planeCoordinateIsometry.symm.contDiff)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialIncrementBound
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The restored polynomial value has one fixed finite loss. Compact local
jet ranges suffice: a fixed cutoff removes the irrelevant values away from
the outer atlas supports before applying the restoration estimate. -/
noncomputable section
open Set Manifold Bundle TopologicalSpace
open scoped ContDiff Manifold Topology BigOperators NNReal

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialIncrementDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialIncrementDualSmul
variable (A : SmoothingAtlas M)





attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialIncrementFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialIncrementFiberSpace
local instance polynomialIncrementSectionNormed_r8ced5e_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialIncrementSectionSpace_r8ced5e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- Combine the actual free, forced and mean residuals, with the derived
mixed-polynomial and Taylor bounds, into a bound for the changed metric. -/
theorem atlas_polynomial_increment_bound_oai (m : ℕ) (A₀ B₀ : ℝ)
    (hA : 0 ≤ A₀) (hB : 0 ≤ B₀) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {n : A.centers → ℕ}
      (P : ∀ i : A.centers, Fin 3 → Fin (n i) → Expression)
      (_hP : ∀ i k l, (P i k l).SmoothCoeffs univ)
      (F U V : M → Space), ContMDiff planeModel spaceModel ∞ F →
      ContMDiff planeModel spaceModel ∞ U → ContMDiff planeModel spaceModel ∞ V →
      ∀ (T H : ∀ p : M, CovariantTwoTensor p),
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun p => TotalSpace.mk' TensorFiber p (T p)) →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun p => TotalSpace.mk' TensorFiber p (H p)) →
      ∀ (τ ε δ C₁ C₂ C₃ E₁ E₂ : ℝ), 0 < τ → τ ≤ 1 → 0 ≤ δ → δ ≤ τ →
      A.WeightedBound τ (m+1) (A₀*(δ*τ)) U →
      A.WeightedBound τ (m+1) (B₀*δ^2) V →
      A.TensorWeightedBound τ m C₁
        (linearMetricTensor F U+A.atlasPolynomialVariation P ε F U) →
      A.TensorWeightedBound τ m C₂
        (linearMetricTensor F V+A.atlasPolynomialVariation P ε F V+
          (inducedTensor U+A.atlasPolynomialQuadratic P ε F U)-H) →
      A.TensorWeightedBound τ m C₃ (H-T) →
      A.TensorWeightedBound τ m (E₁*(δ^3/τ))
        (A.atlasPolynomialQuadratic P ε F (U+V)-A.atlasPolynomialQuadratic P ε F U) →
      A.TensorWeightedBound τ m (E₂*(δ^3/τ)) (A.atlasPolynomialRemainder P ε F (U+V)) →
      A.TensorWeightedBound τ m (C₁+C₂+C₃+(D+E₁+E₂)*(δ^3/τ))
        (A.atlasPolynomialMetric P ε (F+(U+V))-A.atlasPolynomialMetric P ε F-T) := by
  obtain ⟨D,hD,hd⟩ := A.global_cubic_remainder_bound m A₀ B₀ hA hB
  refine ⟨D,hD,?_⟩
  intro n P hP F U V hF hU hV T H hT hH τ ε δ C₁ C₂ C₃ E₁ E₂
    hτ hτ1 hδ hδτ hbU hbV h₁ h₂ h₃ h₄ h₅
  have hUV := hU.add hV
  have hLU := (A.linearMetricTensor_smooth hF hU).add_section
    (A.atlasPolynomialVariation_smooth hP hF hU ε)
  have hLV := (A.linearMetricTensor_smooth hF hV).add_section
    (A.atlasPolynomialVariation_smooth hP hF hV ε)
  have hQU := (A.inducedTensor_smooth hU).add_section
    (A.atlasPolynomialQuadratic_smooth hP hF hU ε)
  have hs₂ := (hLV.add_section hQU).sub_section hH
  have hs₃ := hH.sub_section hT
  have hM := (A.linearMetricTensor_smooth hU hV).add_section (A.inducedTensor_smooth hV)
  have hPol := (A.atlasPolynomialQuadratic_smooth hP hF hUV ε).sub_section
    (A.atlasPolynomialQuadratic_smooth hP hF hU ε)
  have hRem := A.atlasPolynomialRemainder_smooth hP hF hUV ε
  have hb₁ := A.tensorWeightedBound_add hLU hs₂ hτ.le h₁ h₂
  have hb₂ := A.tensorWeightedBound_add (hLU.add_section hs₂) hs₃ hτ.le hb₁ h₃
  have hb₃ := A.tensorWeightedBound_add ((hLU.add_section hs₂).add_section hs₃) hM hτ.le hb₂
    (hd τ δ hτ hτ1 hδ hδτ U V hU hV hbU hbV)
  have hb₄ := A.tensorWeightedBound_add
    (((hLU.add_section hs₂).add_section hs₃).add_section hM) hPol hτ.le hb₃ h₄
  have hb₅ := A.tensorWeightedBound_add
    ((((hLU.add_section hs₂).add_section hs₃).add_section hM).add_section hPol) hRem hτ.le hb₄ h₅
  have hlin : linearMetricTensor F (U+V) = linearMetricTensor F U+linearMetricTensor F V := by
    have hh := linearMetricTensor_finite_sum F ![U,V] (by
      intro j
      fin_cases j
      · exact hU
      · exact hV)
    convert hh using 1
    · simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]
    · funext p
      simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Pi.add_apply]
  have herr : A.atlasPolynomialMetric P ε (F+(U+V))-A.atlasPolynomialMetric P ε F-T =
      (((((linearMetricTensor F U+A.atlasPolynomialVariation P ε F U)+
        (linearMetricTensor F V+A.atlasPolynomialVariation P ε F V+
          (inducedTensor U+A.atlasPolynomialQuadratic P ε F U)-H))+(H-T))+
        (linearMetricTensor U V+inducedTensor V))+
        (A.atlasPolynomialQuadratic P ε F (U+V)-A.atlasPolynomialQuadratic P ε F U))+
        A.atlasPolynomialRemainder P ε F (U+V) := by
    rw [A.atlas_polynomial_metric_taylor_identity P ε hF hUV,
      A.atlasPolynomialVariation_add P ε F hU hV,hlin,inducedTensor_add hU hV]
    abel
  rw [herr]
  convert hb₅ using 1
  all_goals try with_reducible_and_instances rfl
  ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_increment_bound_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_increment_bound_oai.{u_1}
