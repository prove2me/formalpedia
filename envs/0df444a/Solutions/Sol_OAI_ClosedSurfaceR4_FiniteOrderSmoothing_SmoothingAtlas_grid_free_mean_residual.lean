-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_free_mean_residual
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:42:55.219186+00:00
-- url     : https://prove2.me/submissions/80cc590b-8e0f-4f1a-ac33-f918135b0b5d

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_finite_atlas_free_metric
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_finite_atlas_metric_split

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_WeightedBounds
attribute [-instance] _root_.instVAddIntReal_solutions
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

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasPhases
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]


lemma phaseLinear_apply (ξ x : SmallModes.Base) : phaseLinear ξ x = ξ.1*x.1+ξ.2*x.2 := rfl

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GridPartition
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGrid
open Set Function WeightedEstimates
attribute [local instance] Classical.propDecidable


lemma normalizedCutoff_squares {s : Finset Index} {h : ℝ} {x : Base}
    (hp : 0 < squareSum s h x) : ∑ a ∈ s, (normalizedCutoff s h a x)^2 = 1 := by
  calc
    _ = squareSum s h x / (Real.sqrt (squareSum s h x))^2 := by
      simp only [normalizedCutoff,div_pow,Finset.sum_div,squareSum]
    _ = 1 := by rw [Real.sq_sqrt hp.le,div_self hp.ne']

end ClosedSurfaceR4.PhaseGrid

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ChartedTrialAmplitude
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Cutoff square-root trial amplitudes on the actual transported support.
These use the original tensor field and the inverse of its phase chart. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData
open PhaseMean RealModes RootMean WeightedEstimates FiniteMean
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (ψ : SupportedField (F := ℝ) c.chartCompact)
    (Q : SmallModes.Base → Tensor →L[ℝ] ℝ)
    (h : LocalBounds c.e.source c.e.target s r ρ R reference c.realMap ψ Q c.e c.e.symm)

lemma trialAmplitude_apply (hρ : 0 < ρ) {A : SmallModes.Base → Tensor}
    (hA : ContDiffOn ℝ ∞ A c.e.source) (hball : InTrialBall c.e.source reference r A)
    (y : SmallModes.Base) :
    c.trialAmplitude ψ Q h hρ A y = phaseAmplitude ψ (coefficient Q c.e.symm A) y := by
  classical
  simp only [trialAmplitude, dite_eq_left (show ContDiffOn ℝ ∞ A c.e.source ∧
    InTrialBall c.e.source reference r A from ⟨hA,hball⟩)]
  rfl

end ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ChartedLeadingTensor
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The leading tensors of the actual charted amplitudes are the prescribed
cutoff squares times phase-covector squares. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes RootMean WeightedEstimates FiniteMean

lemma chartLeadingTensor_apply (b : SmallModes.Base → ℝ) (e : SmallModes.Base → SmallModes.Base)
    (x : SmallModes.Base) (k : Fin 3) :
    chartLeadingTensor b e x k = b (e x) ^ 2 *
      (fderiv ℝ e x (firstDirection k)).1 * (fderiv ℝ e x (secondDirection k)).1 := by
  change evaluate (fun i => b (e x) ^ 2 * (firstDirection i).1 * (secondDirection i).1)
    (fderiv ℝ e x (firstDirection k)) (fderiv ℝ e x (secondDirection k)) = _
  simp [evaluate, firstDirection, secondDirection, SmallModes.dx, SmallModes.dy]

namespace PolynomialSolveData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} (c : PolynomialSolveData P ε G hG φ K τ s)

lemma phase_derivative {x : SmallModes.Base} (hx : x ∈ c.e.source) (v : SmallModes.Base) :
    (fderiv ℝ c.e x v).1 = fderiv ℝ (coordinatePhase φ) x v := by
  have he : (fun y => (c.e y).1) =ᶠ[nhds x] coordinatePhase φ := by
    filter_upwards [c.e.open_source.mem_nhds hx] with y hy using c.phase y hy
  have hd := (c.smoothForward.contDiffAt (c.e.open_source.mem_nhds hx)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [← he.fderiv_eq, fderiv.fst hd]
  rfl

lemma leadingField_apply (b : SupportedField (F := ℝ) c.chartCompact) (x : SmallModes.Base) :
    c.leadingField b x = c.e.source.indicator (fun y k => b (c.e y) ^ 2 *
      fderiv ℝ (coordinatePhase φ) y (firstDirection k) *
      fderiv ℝ (coordinatePhase φ) y (secondDirection k)) x := by
  by_cases hx : x ∈ c.e.source
  · simp only [leadingField, realTensorChartPull_apply, Set.indicator_of_mem hx]
    change chartLeadingTensor b c.e x = _
    ext k
    rw [chartLeadingTensor_apply, c.phase_derivative hx, c.phase_derivative hx]
  · simp only [leadingField, realTensorChartPull_apply, Set.indicator_of_notMem hx]

end PolynomialSolveData

namespace ChartedMeanData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} {c : PolynomialSolveData P ε G hG φ K τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (d : ChartedMeanData c r ρ R reference)

lemma leading_apply (hρ : 0 < ρ) {A : SmallModes.Base → Tensor}
    (hA : ContDiff ℝ ∞ A) (hball : InTrialBall Set.univ reference r A) (x : SmallModes.Base) :
    d.leading hρ A x = c.e.source.indicator (fun y k => d.cutoff (c.e y) ^ 2 *
      d.form (c.e y) (A y) * fderiv ℝ (coordinatePhase φ) y (firstDirection k) *
      fderiv ℝ (coordinatePhase φ) y (secondDirection k)) x := by
  change c.leadingField (d.amplitude hρ A) x = _
  rw [c.leadingField_apply]
  by_cases hx : x ∈ c.e.source
  · simp only [Set.indicator_of_mem hx]
    have ha := c.trialAmplitude_apply d.cutoff d.form d.localBounds hρ hA.contDiffOn
      (fun y _ => hball y (Set.mem_univ y)) (c.e x)
    have hpos := coefficient_trial_range d.localBounds.invInto d.localBounds.margin
      (fun y _ => hball y (Set.mem_univ y)) (c.e.map_source hx)
    have hn : 0 ≤ coefficient d.form c.e.symm A (c.e x) := hρ.le.trans hpos.1
    have hn' : 0 ≤ d.form (c.e x) (A x) := by
      simpa only [coefficient, c.e.left_inv hx] using hn
    ext k
    change c.trialAmplitude d.cutoff d.form d.localBounds hρ A (c.e x) ^ 2 * _ * _ = _
    rw [ha]
    simp only [phaseAmplitude, mul_pow, coefficient, c.e.left_inv hx, Real.sq_sqrt hn']
  · simp only [Set.indicator_of_notMem hx]

end ChartedMeanData
end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ChartedPartitionLeading
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedCellCutoff_apply _root_.OAI.ClosedSurfaceR4.PhaseGrid.supportedNormalizedCutoff_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A supported phase family has leading tensor equal to the cutoff square
 times its input tensor. This is the local identity used by the global atlas. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes RootMean WeightedEstimates FiniteMean PhaseGeometry

lemma covectorSquare_directions (ξ : SmallModes.Base) (k : Fin 3) :
    covectorSquare ξ k = phaseLinear ξ (firstDirection k) * phaseLinear ξ (secondDirection k) := by
  fin_cases k <;> simp [covectorSquare, firstDirection, secondDirection, phaseLinear_apply,
    SmallModes.dx, SmallModes.dy] <;> ring

theorem charted_cutoff_leading {n : ℕ} {P : Fin 3 → Fin n → Expression}
    {ε τ : ℝ} {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0} {c : PolynomialSolveData P ε G hG φ K τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (d : ChartedMeanData c r ρ R reference) (hρ : 0 < ρ)
    (χ : SmallModes.Base → ℝ) (Q : Tensor →L[ℝ] ℝ) (ξ : SmallModes.Base) (w : ℝ)
    (hw : w ≠ 0) (hphase : coordinatePhase φ = phaseLinear (w • ξ))
    (hcutoff : ∀ x ∈ c.e.source, d.cutoff (c.e x) = χ x / w)
    (hform : ∀ x ∈ c.e.source, d.form (c.e x) = Q)
    (hsupport : tsupport χ ⊆ c.e.source) {A : SmallModes.Base → Tensor}
    (hA : ContDiff ℝ ∞ A) (hball : InTrialBall Set.univ reference r A) (x : SmallModes.Base) :
    d.leading hρ A x = (χ x)^2 • (Q (A x) • covectorSquare ξ) := by
  rw [d.leading_apply hρ hA hball]
  by_cases hx : x ∈ c.e.source
  · rw [Set.indicator_of_mem hx]
    have hd (v : SmallModes.Base) : fderiv ℝ (coordinatePhase φ) x v = w * phaseLinear ξ v := by
      rw [hphase, (phaseLinear (w • ξ)).fderiv]
      simp only [phaseLinear_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      ring
    ext k
    simp only [hcutoff x hx, hform x hx, hd, Pi.smul_apply, smul_eq_mul,
      covectorSquare_directions]
    field_simp [hw]
  · have hz : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hsupport h))
    simp only [Set.indicator_of_notMem hx, hz, zero_pow (by decide : 2 ≠ 0), zero_smul]

theorem charted_partition_leading {n : ℕ} {P : Fin 3 → Fin n → Expression}
    {ε τ : ℝ} {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Fin 3 → Base → ℝ}
    {K : Fin 3 → Compacts Base} {s : ℝ≥0}
    {c : ∀ j, PolynomialSolveData P ε G hG (φ j) (K j) τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (d : ∀ j, ChartedMeanData (c j) r ρ R reference) (hρ : 0 < ρ)
    (χ : SmallModes.Base → ℝ) (Q : PhaseBasis) (w : Fin 3 → ℝ)
    (hw : ∀ j, w j ≠ 0) (hphase : ∀ j, coordinatePhase (φ j) = phaseLinear (w j • Q.ξ j))
    (hcutoff : ∀ j x, x ∈ (c j).e.source → (d j).cutoff ((c j).e x) = χ x / w j)
    (hform : ∀ j x, x ∈ (c j).e.source → (d j).form ((c j).e x) = Q.Q j)
    (hsupport : ∀ j, tsupport χ ⊆ (c j).e.source) {A : SmallModes.Base → Tensor}
    (hA : ContDiff ℝ ∞ A) (hball : InTrialBall Set.univ reference r A) :
    chartedFamilyLeading d hρ A = fun x => (χ x)^2 • A x := by
  funext x
  change (∑ j : Fin 3, (d j).leading hρ A x) = _
  simp_rw [charted_cutoff_leading _ hρ χ _ _ _ (hw _) (hphase _) (hcutoff _) (hform _)
    (hsupport _) hA hball]
  rw [← Finset.smul_sum, Q.decomposition]

end ClosedSurfaceR4.JetPolynomial.Perturbation

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
local instance coordinateFiberSpace_r29f3ad_1 : NormedSpace ℝ TensorFiber := inferInstance
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
local instance symmetryModelComplete_r29f3ad_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.symmetryModelSpace
local instance symmetryModelComplete_r29f3ad_2 : CompleteSpace TensorFiber := inferInstance
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
local instance phaseFiberNormed_r29f3ad_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance phaseFiberSpace_r29f3ad_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance phaseDualAdd_r29f3ad_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance phaseDualSmul_r29f3ad_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance phaseSectionNormed_r29f3ad_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance phaseSectionSpace_r29f3ad_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
local instance chartReadSectionNormed_r29f3ad_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance chartReadSectionSpace_r29f3ad_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
attribute [-instance] _root_.instVAddIntReal_solutions
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
local instance planeReadSectionSpace_r29f3ad_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorPlaneRead_smooth (i : A.centers) {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p))) :
    ContDiff ℝ ∞ (A.tensorPlaneRead i u) :=
  (A.tensorChartRead_smooth i hu).comp planeCoordinateIsometry.symm.contDiff

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
local instance reconstructionFiberNormed_r29f3ad_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance reconstructionFiberSpace_r29f3ad_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance reconstructionDualSmul_r29f3ad_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance reconstructionSectionNormed_r29f3ad_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance reconstructionSectionSpace_r29f3ad_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
local instance weightPlaneFiberNormed_r29f3ad_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance weightPlaneFiberSpace_r29f3ad_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance weightPlaneDualAdd_r29f3ad_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance weightPlaneDualSmul_r29f3ad_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance weightPlaneSectionNormed_r29f3ad_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance weightPlaneSectionSpace_r29f3ad_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedAdjustedMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual original-coordinate quadratic mean after finite substitution.
The threshold in this statement still concerns fixed scale data. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates FiniteMean
variable {n : ℕ} {ι : Type*} [Fintype ι]
    {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : ι → Base → ℝ}
    {K : ι → Compacts Base} {s : ℝ≥0}
    {c : ∀ i, PolynomialSolveData P ε G hG (φ i) (K i) τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (d : ∀ i, ChartedMeanData (c i) r ρ R reference)

lemma chartedFamilyMean_smooth (hρ : 0 < ρ) (δ : ℝ) (q : ℕ)
    (A : SmallModes.Base → Tensor) : ContDiff ℝ ∞ (chartedFamilyMean d hρ δ q A) :=
  ContDiff.sum (fun i _ => ((c i).combinedMeanField δ q ((d i).amplitude hρ A)).contDiff)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GridMeanReconstruction
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The leading tensor of all cell phases is exactly the original chart
weight squared times the input tensor. No cardinality-dependent loss occurs. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal BigOperators
namespace ClosedSurfaceR4.PhaseGrid
open JetPolynomial

lemma supportedCellCutoff_square_sum {K : Compacts Base}
    (f : SupportedField (F := ℝ) K) {a : Finset Index} {h : ℝ}
    (hh : 0 < h) (hK : (K : Set Base) ⊆ coverRegion a h) (x : Base) :
    (∑ k : a, (supportedCellCutoff f hh hK k.val x)^2) = (f x)^2 := by
  classical
  by_cases hf : f x = 0
  · simp [supportedCellCutoff_apply,hf]
  have hxK : x ∈ (K : Set Base) := by
    by_contra hx
    exact hf (by simpa only [Pi.zero_apply] using f.zero_on_compl hx)
  have hsum := normalizedCutoff_squares
    (zero_lt_one.trans_le (squareSum_ge_one hh (coverRegion_covers a h (hK hxK))))
  have hco : (∑ k : a, (normalizedCutoff a h k.val x)^2) =
      ∑ k ∈ a, (normalizedCutoff a h k x)^2 :=
    Finset.sum_coe_sort a (fun k => (normalizedCutoff a h k x)^2)
  simp only [supportedCellCutoff_apply,mul_pow]
  rw [← Finset.mul_sum,hco,hsum,mul_one]

end ClosedSurfaceR4.PhaseGrid

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean PhaseGeometry RealModes FiniteMean PhaseGrid

theorem charted_grid_partition_leading {n : ℕ} {P : Fin 3 → Fin n → Expression}
    {ε τ : ℝ} {G : Base → Space} {hG : ContDiff ℝ ∞ G}
    {a : Finset Index} {h : ℝ} {K₀ : Compacts SmallModes.Base}
    (χ : SupportedField (F := ℝ) K₀) (hh : 0 < h)
    (hK₀ : (K₀ : Set SmallModes.Base) ⊆ coverRegion a h)
    {φ : a → Fin 3 → Base → ℝ} {K : a → Fin 3 → Compacts Base} {s : ℝ≥0}
    {c : ∀ k j, PolynomialSolveData P ε G hG (φ k j) (K k j) τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (d : ∀ k j, ChartedMeanData (c k j) r ρ R reference) (hρ : 0 < ρ)
    (Q : a → PhaseBasis) (w : a → Fin 3 → ℝ)
    (hw : ∀ k j, w k j ≠ 0)
    (hphase : ∀ k j, coordinatePhase (φ k j) = phaseLinear (w k j • (Q k).ξ j))
    (hcutoff : ∀ k j x, x ∈ (c k j).e.source →
      (d k j).cutoff ((c k j).e x) = supportedCellCutoff χ hh hK₀ k.val x / w k j)
    (hform : ∀ k j x, x ∈ (c k j).e.source → (d k j).form ((c k j).e x) = (Q k).Q j)
    (hsupport : ∀ k j, tsupport (supportedCellCutoff χ hh hK₀ k.val) ⊆ (c k j).e.source)
    {A : SmallModes.Base → Tensor} (hA : ContDiff ℝ ∞ A)
    (hball : InTrialBall univ reference r A) :
    chartedFamilyLeading (fun t : a × Fin 3 => d t.1 t.2) hρ A =
      fun x => (χ x)^2 • A x := by
  classical
  have hcell (k : a) := charted_partition_leading (d k) hρ
    (supportedCellCutoff χ hh hK₀ k.val) (Q k) (w k) (hw k) (hphase k)
    (hcutoff k) (hform k) (hsupport k) hA hball
  funext x
  change (∑ t : a × Fin 3, (d t.1 t.2).leading hρ A x) = _
  rw [Fintype.sum_prod_type]
  simp_rw [show ∀ k : a, (∑ j : Fin 3, (d k j).leading hρ A x) =
    (supportedCellCutoff χ hh hK₀ k.val x)^2 • A x from fun k => congrFun (hcell k) x]
  rw [← Finset.sum_smul,supportedCellCutoff_square_sum]

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GridAtlasMetric
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact metric expansion for the variable grid of phases in a fixed atlas. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry
open PhaseGrid (Index coverRegion supportedCellCutoff)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridAtlasDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridAtlasDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridAtlasFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridAtlasFiberSpace
local instance gridAtlasSectionNormed_r29f3ad_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance gridAtlasSectionSpace_r29f3ad_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.instDecidableEqSigmaSubtypeMemFinsetCentersProdIndexFinOfNatNat
/-- The actual grid phases reconstruct the complete tensor in the fixed atlas. -/
theorem grid_atlas_free_metric
    {a : A.centers → Finset Index} {h : ℝ} (hh : 0 < h)
    (hcover : ∀ i, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆
      coverRegion (a i) h)
    {n : A.centers → ℕ} {P : ∀ i, Fin 3 → Fin (n i) → Expression}
    {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
    {φ : ∀ i, ((a i) × Fin 3) → Base → ℝ}
    {K : ∀ i, ((a i) × Fin 3) → TopologicalSpace.Compacts Base}
    {τ : ℝ} {s : ℝ≥0}
    {c : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) τ s}
    {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}
    (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i)) (hρ : 0 < ρ)
    (Q : ∀ i, (a i) → PhaseBasis) (w : ∀ i, (a i) → Fin 3 → ℝ)
    (hw : ∀ i k j, w i k j ≠ 0)
    (hphase : ∀ i k j, coordinatePhase (φ i (k,j)) = phaseLinear (w i k j • (Q i k).ξ j))
    (hcutoff : ∀ i k j x, x ∈ (c i (k,j)).e.source →
      (d i (k,j)).cutoff ((c i (k,j)).e x) =
        supportedCellCutoff (A.supportedPlaneWeight i) hh (hcover i) k.val x / w i k j)
    (hform : ∀ i k j x, x ∈ (c i (k,j)).e.source →
      (d i (k,j)).form ((c i (k,j)).e x) = (Q i k).Q j)
    (hsupport : ∀ i k j, tsupport (supportedCellCutoff
      (A.supportedPlaneWeight i) hh (hcover i) k.val) ⊆ (c i (k,j)).e.source)
    (hK : ∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    (u : ∀ x : M, CovariantTwoTensor x)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (u x)))
    (hsym : ∀ p v v', u p v v' = u p v' v)
    (hball : ∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u))
    {δ : ℝ} (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ) :
    inducedTensor (spaceCoordinates.symm ∘ A.finiteAtlasFreeOscillation d hρ δ q u) =
      δ^2 • (u + A.tensorPlaneRestore (fun i =>
        chartedFamilyMean (d i) hρ δ q (A.tensorPlaneRead i u))) +
      A.tensorPlaneRestore (fun k x => (A.planeWeight k x)^2 • RealModes.nonzeroPhaseSum τ
        (fun b : Σ i, ((a i) × Fin 3) => A.vectorPlaneRead k (A.finiteGlobalPhase (φ := φ) b.1 b.2))
        (fun b : Σ i, ((a i) × Fin 3) => A.vectorPlaneRead k
          (A.finiteGlobalAmplitude d hρ δ q u b.1 b.2)) x) := by
  classical
  have hleading (i : A.centers) :
      chartedFamilyLeading (d i) hρ (A.tensorPlaneRead i u) = A.tensorPlaneEncode u i := by
    have hi := charted_grid_partition_leading (A.supportedPlaneWeight i) hh (hcover i)
      (fun k j => d i (k,j)) hρ (Q i) (w i) (hw i) (hphase i) (hcutoff i)
      (hform i) (hsupport i) (A.tensorPlaneRead_smooth i hu) (hball i)
    rw [hi]
    funext x
    exact (A.tensorPlaneEncode_weight i u x).symm
  have he : (fun i => chartedFamilyLeading (d i) hρ (A.tensorPlaneRead i u) +
      chartedFamilyMean (d i) hρ δ q (A.tensorPlaneRead i u)) =
      A.tensorPlaneEncode u + (fun i => chartedFamilyMean (d i) hρ δ q (A.tensorPlaneRead i u)) := by
    funext i
    rw [hleading]
    rfl
  rw [A.finite_atlas_free_metric d hρ hδ hτ q u hK,he,
    A.tensorPlaneRestore_add,A.tensorPlaneRestore_encode u hsym]

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
local instance quadraticAtlasSectionSpace_r29f3ad_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GridFreeMeanIdentity
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact metric expansion for the variable grid of phases in a fixed atlas. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry
open PhaseGrid (Index coverRegion supportedCellCutoff)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridFreeMeanDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridFreeMeanDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridFreeMeanFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridFreeMeanFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.gridFreeMeanSectionNormed
local instance gridFreeMeanSectionSpace_r29f3ad_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
local instance instDecidableEqSigmaSubtypeMemFinsetCentersProdIndexFinOfNatNat_1_r29f3ad_1 {a : A.centers → Finset Index} : DecidableEq (Σ i, ((a i) × Fin 3)) :=
  Classical.decEq _
theorem grid_free_mean_identity
    {a : A.centers → Finset Index} {h : ℝ} (hh : 0 < h)
    (hcover : ∀ i, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆
      coverRegion (a i) h)
    {n : A.centers → ℕ} {P : ∀ i, Fin 3 → Fin (n i) → Expression}
    {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
    {φ : ∀ i, ((a i) × Fin 3) → Base → ℝ}
    {K : ∀ i, ((a i) × Fin 3) → TopologicalSpace.Compacts Base}
    {τ : ℝ} {s : ℝ≥0}
    {c : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) τ s}
    {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}
    (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i)) (hρ : 0 < ρ)
    (Q : ∀ i, (a i) → PhaseBasis) (w : ∀ i, (a i) → Fin 3 → ℝ)
    (hw : ∀ i k j, w i k j ≠ 0)
    (hphase : ∀ i k j, coordinatePhase (φ i (k,j)) = phaseLinear (w i k j • (Q i k).ξ j))
    (hcutoff : ∀ i k j x, x ∈ (c i (k,j)).e.source →
      (d i (k,j)).cutoff ((c i (k,j)).e x) =
        supportedCellCutoff (A.supportedPlaneWeight i) hh (hcover i) k.val x / w i k j)
    (hform : ∀ i k j x, x ∈ (c i (k,j)).e.source →
      (d i (k,j)).form ((c i (k,j)).e x) = (Q i k).Q j)
    (hsupport : ∀ i k j, tsupport (supportedCellCutoff
      (A.supportedPlaneWeight i) hh (hcover i) k.val) ⊆ (c i (k,j)).e.source)
    (hK : ∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    (u : ∀ x : M, CovariantTwoTensor x)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (u x)))
    (hsym : ∀ p v v', u p v v' = u p v' v)
    (hball : ∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u))
    {δ : ℝ} (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ) :
    A.finiteAtlasFreeMean d hρ δ q u =
      δ^2 • (u+A.atlasMean (fun i => chartedFamilyMean (d i) hρ δ q) u) := by
  have hg := A.grid_atlas_free_metric hh hcover d hρ Q w hw hphase hcutoff hform
    hsupport hK u hu hsym hball hδ hτ q
  have hs := A.finite_atlas_metric_split d hρ hδ hτ q u hK
  change inducedTensor (spaceCoordinates.symm ∘ A.finiteAtlasFreeOscillation d hρ δ q u) =
    δ^2 • (u+A.atlasMean (fun i => chartedFamilyMean (d i) hρ δ q) u) +
      A.finiteAtlasNonzero d hρ δ q u at hg
  exact add_right_cancel (hs.symm.trans hg)

theorem grid_free_mean_residual_oai
    {a : A.centers → Finset Index} {h : ℝ} (hh : 0 < h)
    (hcover : ∀ i, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆
      coverRegion (a i) h)
    {n : A.centers → ℕ} {P : ∀ i, Fin 3 → Fin (n i) → Expression}
    {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
    {φ : ∀ i, ((a i) × Fin 3) → Base → ℝ}
    {K : ∀ i, ((a i) × Fin 3) → TopologicalSpace.Compacts Base}
    {τ : ℝ} {s : ℝ≥0}
    {c : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) τ s}
    {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}
    (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i)) (hρ : 0 < ρ)
    (Q : ∀ i, (a i) → PhaseBasis) (w : ∀ i, (a i) → Fin 3 → ℝ)
    (hw : ∀ i k j, w i k j ≠ 0)
    (hphase : ∀ i k j, coordinatePhase (φ i (k,j)) = phaseLinear (w i k j • (Q i k).ξ j))
    (hcutoff : ∀ i k j x, x ∈ (c i (k,j)).e.source →
      (d i (k,j)).cutoff ((c i (k,j)).e x) =
        supportedCellCutoff (A.supportedPlaneWeight i) hh (hcover i) k.val x / w i k j)
    (hform : ∀ i k j x, x ∈ (c i (k,j)).e.source →
      (d i (k,j)).form ((c i (k,j)).e x) = (Q i k).Q j)
    (hsupport : ∀ i k j, tsupport (supportedCellCutoff
      (A.supportedPlaneWeight i) hh (hcover i) k.val) ⊆ (c i (k,j)).e.source)
    (hK : ∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    (u : ∀ x : M, CovariantTwoTensor x)
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (u x)))
    (hsym : ∀ p v v', u p v v' = u p v' v)
    (hball : ∀ i, FiniteMean.InTrialBall univ (reference i) (r i) (A.tensorPlaneRead i u))
    {δ : ℝ} (hδ : δ ≠ 0) (hτ : τ ≠ 0) (q : ℕ)
    (f : ∀ x : M, CovariantTwoTensor x)
    (hf : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (f x)))
    {m : ℕ} {C : ℝ} (hτpos : 0 < τ) (hτs : τ ≤ s)
    (hres : A.TensorWeightedBound s m C
      (u+A.atlasMean (fun i => chartedFamilyMean (d i) hρ δ q) u-f)) :

    A.TensorWeightedBound τ m (δ^2*C) (A.finiteAtlasFreeMean d hρ δ q u-δ^2 • f) := by
  have hmean := A.grid_free_mean_identity hh hcover d hρ Q w hw hphase hcutoff hform
    hsupport hK u hu hsym hball hδ hτ q
  have hμ := A.tensorPlaneRestore_smooth
    (fun i => chartedFamilyMean_smooth (d i) hρ δ q (A.tensorPlaneRead i u))
  have hr := (hu.add_section hμ).sub_section hf
  have hb : A.TensorWeightedBound τ m C
      (u+A.atlasMean (fun i => chartedFamilyMean (d i) hρ δ q) u-f) :=
    fun i => (hres i).shrink_scale hτpos.le hτs
  have hh := A.tensorWeightedBound_const_smul hr hb (δ^2)
  rw [abs_of_nonneg (sq_nonneg δ)] at hh
  rw [hmean,← smul_sub]
  exact hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_free_mean_residual_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.grid_free_mean_residual_oai.{u_1}
