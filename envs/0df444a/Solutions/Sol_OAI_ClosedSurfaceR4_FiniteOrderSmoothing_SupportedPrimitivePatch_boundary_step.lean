-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SupportedPrimitivePatch.boundary_step
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:45:49.154001+00:00
-- url     : https://prove2.me/submissions/d12f9a41-3939-4e8e-8425-8e8ba230669c

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Data.Fintype.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_independent_circular_primitive_boundary_step

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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ChartModel
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes Set Bundle Manifold


variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma coordinateDomain_open (p : M) : IsOpen (coordinateDomain p) := by
  apply IsOpen.preimage planeCoordinates.symm.continuous
  simpa [extChartAt_target, planeModel] using (chartAt Plane p).open_target

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_NormalProjection
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.NormalFrame

lemma gramDet_change_basis (X Y : RVec 4) (a b c d : ℝ) :
    NormalFrame.gramDet (a • X + b • Y) (c • X + d • Y) =
      (a*d-b*c)^2 * NormalFrame.gramDet X Y := by
  simp only [NormalFrame.gramDet, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, dotProduct_comm Y X]
  ring

lemma realNormalPart_linear (X Y : RVec 4) :
    IsLinearMap ℝ (realNormalPart X Y) := by
  constructor
  · intro W Z
    ext i
    simp [realNormalPart, dotProduct_add, Pi.add_apply]
    ring
  · intro s W
    ext i
    simp [realNormalPart, dotProduct_smul, Pi.smul_apply]
    ring

lemma realNormalPart_of_perp (X Y W : RVec 4) (hX : X ⬝ᵥ W = 0) (hY : Y ⬝ᵥ W = 0) :
    realNormalPart X Y W = W := by simp [realNormalPart, hX, hY]

lemma realNormalPart_self_left (X Y : RVec 4) (hD : NormalFrame.gramDet X Y ≠ 0) :
    realNormalPart X Y X = 0 := by
  have hxy : Y ⬝ᵥ X = X ⬝ᵥ Y := dotProduct_comm _ _
  have ha : ((Y ⬝ᵥ Y) * (X ⬝ᵥ X) - (X ⬝ᵥ Y) * (Y ⬝ᵥ X)) /
      NormalFrame.gramDet X Y = 1 := by
    rw [hxy]
    convert div_self hD using 1
    all_goals try with_reducible_and_instances rfl
    unfold NormalFrame.gramDet
    ring
  have hb : (X ⬝ᵥ X) * (Y ⬝ᵥ X) - (X ⬝ᵥ Y) * (X ⬝ᵥ X) = 0 := by rw [hxy]; ring
  simp [realNormalPart, ha, hb]

lemma realNormalPart_self_right (X Y : RVec 4) (hD : NormalFrame.gramDet X Y ≠ 0) :
    realNormalPart X Y Y = 0 := by
  have ha : (Y ⬝ᵥ Y) * (X ⬝ᵥ Y) - (X ⬝ᵥ Y) * (Y ⬝ᵥ Y) = 0 := by ring
  have hb : ((X ⬝ᵥ X) * (Y ⬝ᵥ Y) - (X ⬝ᵥ Y) * (X ⬝ᵥ Y)) /
      NormalFrame.gramDet X Y = 1 := by
    convert div_self hD using 1
    all_goals try with_reducible_and_instances rfl
    unfold NormalFrame.gramDet
    ring
  simp [realNormalPart, ha, hb]



lemma realNormalPart_change_basis (X Y W : RVec 4) (a b c d : ℝ)
    (hD : NormalFrame.gramDet X Y ≠ 0) (hdet : a*d-b*c ≠ 0) :
    realNormalPart (a • X + b • Y) (c • X + d • Y) W = realNormalPart X Y W := by
  let Z := realNormalPart (a • X + b • Y) (c • X + d • Y) W
  have hD' : NormalFrame.gramDet (a • X + b • Y) (c • X + d • Y) ≠ 0 := by
    rw [gramDet_change_basis]
    exact mul_ne_zero (pow_ne_zero 2 hdet) hD
  obtain ⟨hAZ, hBZ⟩ := realNormalPart_perp (a • X + b • Y) (c • X + d • Y) W hD'
  change (a • X + b • Y) ⬝ᵥ Z = 0 at hAZ
  change (c • X + d • Y) ⬝ᵥ Z = 0 at hBZ
  simp only [add_dotProduct, smul_dotProduct, smul_eq_mul] at hAZ hBZ
  have hXZ : X ⬝ᵥ Z = 0 := by
    apply (mul_eq_zero.mp (show (a*d-b*c) * (X ⬝ᵥ Z) = 0 by
      linear_combination d * hAZ - b * hBZ)).resolve_left hdet
  have hYZ : Y ⬝ᵥ Z = 0 := by
    apply (mul_eq_zero.mp (show (a*d-b*c) * (Y ⬝ᵥ Z) = 0 by
      linear_combination a * hBZ - c * hAZ)).resolve_left hdet
  have hlin := realNormalPart_linear X Y
  have hA : realNormalPart X Y (a • X + b • Y) = 0 := by
    rw [hlin.map_add, hlin.map_smul, hlin.map_smul, realNormalPart_self_left _ _ hD,
      realNormalPart_self_right _ _ hD, smul_zero, smul_zero, add_zero]
  have hB : realNormalPart X Y (c • X + d • Y) = 0 := by
    rw [hlin.map_add, hlin.map_smul, hlin.map_smul, realNormalPart_self_left _ _ hD,
      realNormalPart_self_right _ _ hD, smul_zero, smul_zero, add_zero]
  have he : realNormalPart X Y Z = realNormalPart X Y W := by
    dsimp [Z]
    conv_lhs => arg 3; unfold realNormalPart
    rw [hlin.map_sub, hlin.map_sub, hlin.map_smul, hlin.map_smul, hA, hB]
    simp
  exact (realNormalPart_of_perp X Y Z hXZ hYZ).symm.trans he

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SecondForms
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseGeometry Set

lemma real_second_coordDeriv {n : ℕ} {F : RField n} {p : Base}
    (hF : DifferentiableAt ℝ (fderiv ℝ F) p) (v w : Base) :
    coordDeriv v (coordDeriv w F) p = fderiv ℝ (fderiv ℝ F) p v w := by
  have h := (hF.hasFDerivAt.clm_apply (hasFDerivAt_const w p)).fderiv
  change (fderiv ℝ (fun q => (fderiv ℝ F q) w) p) v = _
  rw [h]
  simp

lemma real_second_coordDeriv_comm {n : ℕ} {F : RField n} (hF : ContDiff ℝ ∞ F)
    (p v w : Base) : coordDeriv v (coordDeriv w F) p = coordDeriv w (coordDeriv v F) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    ((hF.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt
  rw [real_second_coordDeriv hd, real_second_coordDeriv hd]
  exact second_derivative_symmetric
    (fun q => (hF.differentiable (by simp) q).hasFDerivAt) hd.hasFDerivAt v w

lemma base_eq_basis (v : Base) : v = v.1 • dx + v.2 • dy := by ext <;> simp [dx,dy]

lemma coordDeriv_eq_basis {n : ℕ} (F : RField n) (v p : Base) :
    coordDeriv v F p = v.1 • coordDeriv dx F p + v.2 • coordDeriv dy F p := by
  conv_lhs => arg 1; rw [base_eq_basis v]
  simp [coordDeriv]

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseGeometry Set

lemma second_coordDeriv_bilinear {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (v w p : Base) : coordDeriv v (coordDeriv w F) p =
      (v.1*w.1) • coordDeriv dx (coordDeriv dx F) p +
      (v.1*w.2+v.2*w.1) • coordDeriv dx (coordDeriv dy F) p +
      (v.2*w.2) • coordDeriv dy (coordDeriv dy F) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
  have hsym := real_second_coordDeriv_comm hF p dy dx
  simp only [real_second_coordDeriv hd] at hsym ⊢
  conv_lhs => arg 2; rw [base_eq_basis w]
  conv_lhs => arg 1; arg 2; rw [base_eq_basis v]
  simp only [map_add, map_smul, add_apply, smul_apply,
    hsym]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma realSecondForm_bilinear {F : RField 4} (hF : ContDiff ℝ ∞ F) (v w p : Base) :
    realSecondForm F v w p =
      (v.1*w.1) • realSecondTensor F p 0 +
      (v.1*w.2+v.2*w.1) • realSecondTensor F p 1 +
      (v.2*w.2) • realSecondTensor F p 2 := by
  unfold realSecondForm
  rw [second_coordDeriv_bilinear hF]
  have hlin := realNormalPart_linear (coordDeriv dx F p) (coordDeriv dy F p)
  rw [hlin.map_add, hlin.map_add, hlin.map_smul, hlin.map_smul, hlin.map_smul]
  simp [realSecondTensor, realSecondForm]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SmoothCoordinates
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry

lemma coordDeriv_comp_smooth {n : ℕ} {F : RField n} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (w p : Base) :
    coordDeriv w (F ∘ φ) p = fderiv ℝ F (φ p) (coordDeriv w φ p) := by
  simp only [coordDeriv,fderiv_comp p (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _) (hφ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _),
    ContinuousLinearMap.comp_apply]

lemma second_coordDeriv_comp_smooth {n : ℕ} {F : RField n} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (v w p : Base) :
    coordDeriv v (coordDeriv w (F ∘ φ)) p =
      coordDeriv (fderiv ℝ φ p v) (coordDeriv (fderiv ℝ φ p w) F) (φ p) +
      fderiv ℝ F (φ p) (coordDeriv v (coordDeriv w φ) p) := by
  have hDF : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hD1 := ((hDF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (φ p)).hasFDerivAt.comp p
    ((hφ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) p).hasFDerivAt
  have hD2 := ((contDiffAt_coordDeriv (p := p) hφ.contDiffAt w).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).hasFDerivAt
  have hp := hD1.clm_apply hD2
  have he : (fun q => (fderiv ℝ F ∘ φ) q (coordDeriv w φ q)) = coordDeriv w (F ∘ φ) := by
    funext q
    exact (coordDeriv_comp_smooth hF hφ w q).symm
  rw [he] at hp
  have heval := congrArg (fun L => L v) hp.fderiv
  rw [real_second_coordDeriv ((hDF.differentiable (by simp)) (φ p))]
  simpa only [coordDeriv,add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply,Function.comp_apply,add_comm] using heval

lemma realNormalPart_fderiv {F : RField 4} (p v : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0) :
    realNormalPart (coordDeriv dx F p) (coordDeriv dy F p) (fderiv ℝ F p v) = 0 := by
  change realNormalPart (coordDeriv dx F p) (coordDeriv dy F p) (coordDeriv v F p) = 0
  conv_lhs => arg 3; rw [coordDeriv_eq_basis F v p]
  have hl := realNormalPart_linear (coordDeriv dx F p) (coordDeriv dy F p)
  rw [hl.map_add,hl.map_smul,hl.map_smul,realNormalPart_self_left _ _ hD,
    realNormalPart_self_right _ _ hD,smul_zero,smul_zero,add_zero]



lemma realSecondForm_comp_smooth {F : RField 4} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (v w p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : (fderiv ℝ φ p dx).1*(fderiv ℝ φ p dy).2-
      (fderiv ℝ φ p dx).2*(fderiv ℝ φ p dy).1 ≠ 0) :
    realSecondForm (F ∘ φ) v w p =
      realSecondForm F (fderiv ℝ φ p v) (fderiv ℝ φ p w) (φ p) := by
  unfold realSecondForm
  rw [coordDeriv_comp_smooth hF hφ,coordDeriv_comp_smooth hF hφ,
    second_coordDeriv_comp_smooth hF hφ]
  change realNormalPart (coordDeriv (fderiv ℝ φ p dx) F (φ p))
    (coordDeriv (fderiv ℝ φ p dy) F (φ p)) _ = _
  rw [coordDeriv_eq_basis F (fderiv ℝ φ p dx),coordDeriv_eq_basis F (fderiv ℝ φ p dy),
    realNormalPart_change_basis _ _ _ _ _ _ _ hD hdet]
  rw [(realNormalPart_linear _ _).map_add,realNormalPart_fderiv _ _ hD,add_zero]

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry

lemma linear_apply_basis (A : Base →L[ℝ] Base) (v : Base) :
    A v = v.1 • A dx + v.2 • A dy := by
  calc A v = A (v.1 • dx + v.2 • dy) := congrArg A (base_eq_basis v)
       _ = _ := by simp

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_JacobianBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry Set Filter

lemma coordDet_comp (A B : Base →L[ℝ] Base) :
    coordDet (A.comp B) = coordDet A * coordDet B := by
  simp only [coordDet,ContinuousLinearMap.comp_apply]
  rw [linear_apply_basis A (B dx),linear_apply_basis A (B dy)]
  simp
  ring

lemma coordDet_id : coordDet (ContinuousLinearMap.id ℝ Base) = 1 := by
  simp [coordDet,dx,dy]

lemma coordDet_fderiv_ne_zero_of_local_inverse {φ ψ : Base → Base} {U V : Set Base}
    (hU : IsOpen U) (hV : IsOpen V) (hφ : ContDiffOn ℝ ∞ φ U)
    (hψ : ContDiffOn ℝ ∞ ψ V) (hmap : MapsTo φ U V)
    (hinv : EqOn (ψ ∘ φ) id U) {p : Base} (hp : p ∈ U) :
    coordDet (fderiv ℝ φ p) ≠ 0 := by
  have hφp := ((hφ p hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hψp := ((hψ (φ p) (hmap hp)).contDiffAt (hV.mem_nhds (hmap hp))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he : ψ ∘ φ =ᶠ[𝓝 p] id := by
    filter_upwards [hU.mem_nhds hp] with q hq
    exact hinv hq
  have hcomp : (fderiv ℝ ψ (φ p)).comp (fderiv ℝ φ p) = ContinuousLinearMap.id ℝ Base := by
    rw [← fderiv_comp p hψp hφp,he.fderiv_eq,fderiv_id]
  have hdet := congrArg coordDet hcomp
  rw [coordDet_comp,coordDet_id] at hdet
  intro hz
  simp [hz] at hdet



end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricPullback
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes Set Bundle Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma metricPullback_pos (g : SmoothMetric M) {φ : Base → M} {x : Base}
    (hi : Function.Injective (mfderiv 𝓘(ℝ, Base) planeModel φ x)) {v : Base} (hv : v ≠ 0) :
    0 < metricPullback g φ x v v := by
  apply g.pos
  intro hz
  apply hv
  apply hi
  exact hz.trans (map_zero _).symm

lemma coordinateMetric_evaluate (g : SmoothMetric M) (p : M) (x v w : Base) :
    PhaseMean.evaluate (coordinateMetric g p x) v w =
      metricPullback g (coordinateInverse p) x v w := by
  let D : Base →L[ℝ] TangentSpace planeModel (coordinateInverse p x) :=
    mfderiv 𝓘(ℝ, Base) planeModel (coordinateInverse p) x
  change PhaseMean.evaluate (fun i => g.inner (coordinateInverse p x)
      (D (PhaseMean.firstDirection i)) (D (PhaseMean.secondDirection i))) v w =
    g.inner (coordinateInverse p x) (D v) (D w)
  have he (v : Base) : v = v.1 • dx + v.2 • dy := by
    ext <;> simp [dx,dy]
  conv_rhs => rw [he v, he w]
  simp only [PhaseMean.evaluate,
    PhaseMean.firstDirection, PhaseMean.secondDirection, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecTail, Matrix.vecHead, Function.comp_apply,
    map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul]
  rw [g.symm _
    (D dy) (D dx)]
  dsimp
  ring

lemma tensor_positive_iff (H : PhaseMean.Tensor) :
    (∀ v : Base, v ≠ 0 → 0 < PhaseMean.evaluate H v v) ↔
      0 < H 0 ∧ 0 < H 0 * H 2 - (H 1)^2 := by
  constructor
  · intro h
    have h₀ : 0 < H 0 := by
      simpa [PhaseMean.evaluate] using h (1, 0) (by simp)
    have hv : (-H 1, H 0) ≠ (0 : Base) := by
      intro he
      have he' := congrArg Prod.snd he
      exact h₀.ne' he'
    have hh := h (-H 1, H 0) hv
    have he : PhaseMean.evaluate H (-H 1, H 0) (-H 1, H 0) = H 0 * (H 0 * H 2 - (H 1)^2) := by
      simp only [PhaseMean.evaluate]
      ring
    rw [he] at hh
    exact ⟨h₀, (mul_pos_iff_of_pos_left h₀).mp hh⟩
  · rintro ⟨h₀, hd⟩ v hv
    have he : H 0 * PhaseMean.evaluate H v v =
        (H 0 * v.1 + H 1 * v.2)^2 + (H 0 * H 2 - (H 1)^2) * v.2^2 := by
      simp only [PhaseMean.evaluate]
      ring
    apply (mul_pos_iff_of_pos_left h₀).mp
    rw [he]
    by_cases hv₂ : v.2 = 0
    · have hv₁ : v.1 ≠ 0 := by
        intro hz
        apply hv
        exact Prod.ext hz hv₂
      simp only [hv₂, mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0)]
      exact sq_pos_of_ne_zero (mul_ne_zero h₀.ne' hv₁)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _)
        (mul_pos hd (sq_pos_of_ne_zero hv₂))


end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_LocalPhaseData
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open Set Function Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]




theorem smooth_extension_near {F : M → V} {U : Set M} (hU : IsOpen U)
    (hF : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ F U) {p : M} (hp : p ∈ U) :
    ∃ G : M → V, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ G ∧
      HasCompactSupport G ∧ tsupport G ⊆ U ∧ G =ᶠ[𝓝 p] F := by
  obtain ⟨b, _, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) p).mem_iff.mp
    (hU.mem_nhds hp)
  let G : M → V := fun q => b q • F q
  have hs : tsupport G ⊆ tsupport b := tsupport_smul_subset_left _ _
  refine ⟨G, ?_, ?_, hs.trans hb, ?_⟩
  · apply contMDiff_of_tsupport
    intro q hq
    exact b.contMDiffAt.smul ((hF q (hb (hs hq))).contMDiffAt
      (hU.mem_nhds (hb (hs hq))))
  · exact b.hasCompactSupport.of_isClosed_subset (isClosed_tsupport G) hs
  · filter_upwards [b.eventuallyEq_one] with q hq
    simp only [G, hq, Pi.one_apply, one_smul]

end ClosedSurfaceR4.PhaseGeometry

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseGeometry Set Filter

lemma coordDeriv_eventuallyEq {n : ℕ} {F G : RField n} {p : Base}
    (h : F =ᶠ[𝓝 p] G) (v : Base) : coordDeriv v F =ᶠ[𝓝 p] coordDeriv v G := by
  filter_upwards [h.fderiv (𝕜 := ℝ)] with q hq
  exact congrArg (fun A : Base →L[ℝ] RVec n => A v) hq

lemma realSecondForm_eventuallyEq {F G : RField 4} {p : Base}
    (h : F =ᶠ[𝓝 p] G) (v w : Base) :
    (fun q => realSecondForm F v w q) =ᶠ[𝓝 p] (fun q => realSecondForm G v w q) := by
  filter_upwards [coordDeriv_eventuallyEq h dx, coordDeriv_eventuallyEq h dy,
    coordDeriv_eventuallyEq (coordDeriv_eventuallyEq h w) v] with q hx hy hxy
  simp only [realSecondForm, hx, hy, hxy]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ChartTransition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
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

variable [IsManifold planeModel ∞ M]

lemma coordinateChart_smoothOn (p : M) :
    ContMDiffOn planeModel 𝓘(ℝ,SmallModes.Base) ∞ (coordinateChart p) (coordinateChart p).source := by
  rw [coordinateChart_source]
  exact planeCoordinates.contDiff.contMDiff.comp_contMDiffOn contMDiffOn_chart

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_CoordinateMargins
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry Set Filter

theorem realSecondForm_comp_on {F : RField 4} {φ : Base → Base}
    {U V : Set Base} (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℝ ∞ F V) (hφ : ContDiffOn ℝ ∞ φ U)
    {p : Base} (hp : p ∈ U) (hφp : φ p ∈ V) (v w : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : (fderiv ℝ φ p dx).1*(fderiv ℝ φ p dy).2-
      (fderiv ℝ φ p dx).2*(fderiv ℝ φ p dy).1 ≠ 0) :
    realSecondForm (F ∘ φ) v w p =
      realSecondForm F (fderiv ℝ φ p v) (fderiv ℝ φ p w) (φ p) := by
  obtain ⟨G,hG,_,_,heG⟩ := smooth_extension_near hV hF.contMDiffOn hφp
  obtain ⟨Φ,hΦ,_,_,heΦ⟩ := smooth_extension_near hU hφ.contMDiffOn hp
  have ep := heΦ.eq_of_nhds
  have eD := heΦ.fderiv_eq (𝕜 := ℝ)
  have hc : ContinuousAt φ p := (hφ p hp).contDiffAt (hU.mem_nhds hp) |>.continuousAt
  have hecomp : G ∘ Φ =ᶠ[𝓝 p] F ∘ φ := by
    filter_upwards [heΦ,heG.comp_tendsto hc] with q hqΦ hqG
    simpa only [Function.comp_apply,hqΦ] using hqG
  have hDG : NormalFrame.gramDet (coordDeriv dx G (Φ p)) (coordDeriv dy G (Φ p)) ≠ 0 := by
    rw [ep,(coordDeriv_eventuallyEq heG dx).eq_of_nhds,
      (coordDeriv_eventuallyEq heG dy).eq_of_nhds]
    exact hD
  have hdetΦ : (fderiv ℝ Φ p dx).1*(fderiv ℝ Φ p dy).2-
      (fderiv ℝ Φ p dx).2*(fderiv ℝ Φ p dy).1 ≠ 0 := by rwa [eD]
  have h := realSecondForm_comp_smooth hG.contDiff hΦ.contDiff v w p hDG hdetΦ
  rw [(realSecondForm_eventuallyEq hecomp v w).eq_of_nhds,eD,ep] at h
  rw [(realSecondForm_eventuallyEq heG _ _).eq_of_nhds] at h
  exact h

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricBounds
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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

lemma coordinateInverse_mfderiv_injective (p : M) {x : SmallModes.Base}
    (hx : x ∈ coordinateDomain p) :
    Function.Injective (mfderiv 𝓘(ℝ,SmallModes.Base) planeModel (coordinateInverse p) x) := by
  have hxt : x ∈ (coordinateChart p).target := by rwa [coordinateChart_target]
  have hs : coordinateInverse p x ∈ (coordinateChart p).source := by
    rw [← coordinateChart_symm_apply]
    exact (coordinateChart p).map_target hxt
  have hi := ((coordinateInverse_smoothOn p) x hx).contMDiffAt
    ((coordinateDomain_open p).mem_nhds hx)
  have hc := ((coordinateChart_smoothOn p) (coordinateInverse p x) hs).contMDiffAt
    ((coordinateChart p).open_source.mem_nhds hs)
  have he : coordinateChart p ∘ coordinateInverse p =ᶠ[𝓝 x] id := by
    filter_upwards [(coordinateDomain_open p).mem_nhds hx] with y hy
    change coordinateChart p (coordinateInverse p y) = y
    rw [← coordinateChart_symm_apply]
    exact (coordinateChart p).right_inv (by rwa [coordinateChart_target])
  have hd : (mfderiv planeModel 𝓘(ℝ,SmallModes.Base) (coordinateChart p) (coordinateInverse p x)).comp
      (mfderiv 𝓘(ℝ,SmallModes.Base) planeModel (coordinateInverse p) x) =
      ContinuousLinearMap.id ℝ SmallModes.Base := by
    rw [← mfderiv_comp x (hc.mdifferentiableAt (by simp)) (hi.mdifferentiableAt (by simp)),
      he.mfderiv_eq,mfderiv_id]
    rfl
  intro v w hv
  have hvw := congrArg (mfderiv planeModel 𝓘(ℝ,SmallModes.Base)
    (coordinateChart p) (coordinateInverse p x)) hv
  have hdv := congrArg (fun L : SmallModes.Base →L[ℝ] SmallModes.Base => L v) hd
  have hdw := congrArg (fun L : SmallModes.Base →L[ℝ] SmallModes.Base => L w) hd
  exact hdv.symm.trans (hvw.trans hdw)

lemma coordinateMetric_positive (g : SmoothMetric M) (p : M) {x : SmallModes.Base}
    (hx : x ∈ coordinateDomain p) :
    0 < coordinateMetric g p x 0 ∧
      0 < coordinateMetric g p x 0 * coordinateMetric g p x 2 - (coordinateMetric g p x 1)^2 := by
  apply (tensor_positive_iff _).mp
  intro v hv
  rw [coordinateMetric_evaluate]
  exact metricPullback_pos g (coordinateInverse_mfderiv_injective p hx) hv



end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricCoordinates
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter Bundle Manifold
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] in
lemma coordinateInverse_mfderiv_right (p : M) {q : M}
    (hq : q ∈ (coordinateChart p).source) :
    (mfderiv 𝓘(ℝ,SmallModes.Base) planeModel (coordinateInverse p) (coordinateChart p q)).comp
      (mfderiv planeModel 𝓘(ℝ,SmallModes.Base) (coordinateChart p) q) =
    ContinuousLinearMap.id ℝ (TangentSpace planeModel q) := by
  have hx : coordinateChart p q ∈ coordinateDomain p := by
    rw [← coordinateChart_target]
    exact (coordinateChart p).map_source hq
  have hi := ((coordinateInverse_smoothOn p) _ hx).contMDiffAt
    ((coordinateDomain_open p).mem_nhds hx)
  have hc := ((coordinateChart_smoothOn p) q hq).contMDiffAt
    ((coordinateChart p).open_source.mem_nhds hq)
  have he : coordinateInverse p ∘ coordinateChart p =ᶠ[𝓝 q] id := by
    filter_upwards [(coordinateChart p).open_source.mem_nhds hq] with a ha
    change coordinateInverse p (coordinateChart p a) = a
    rw [← coordinateChart_symm_apply]
    exact (coordinateChart p).left_inv ha
  rw [← mfderiv_comp q (hi.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp)),
    he.mfderiv_eq,mfderiv_id]
  try rfl

omit [T2Space M] [SecondCountableTopology M] [CompactSpace M] in
lemma coordinateMetric_pullback_chart (g : SmoothMetric M) (p : M) {q : M}
    (hq : q ∈ (coordinateChart p).source) (v w : TangentSpace planeModel q) :
    PhaseMean.evaluate (coordinateMetric g p (coordinateChart p q))
      (mfderiv planeModel 𝓘(ℝ,SmallModes.Base) (coordinateChart p) q v)
      (mfderiv planeModel 𝓘(ℝ,SmallModes.Base) (coordinateChart p) q w) = g.inner q v w := by
  let D : TangentSpace planeModel q →L[ℝ] SmallModes.Base :=
    mfderiv planeModel 𝓘(ℝ,SmallModes.Base) (coordinateChart p) q
  change PhaseMean.evaluate (coordinateMetric g p (coordinateChart p q)) (D v) (D w) =
    g.inner q v w
  rw [coordinateMetric_evaluate]
  have hinv : coordinateInverse p (coordinateChart p q) = q := by
    rw [← coordinateChart_symm_apply]
    exact (coordinateChart p).left_inv hq
  let I : SmallModes.Base →L[ℝ] TangentSpace planeModel q :=
    mfderiv 𝓘(ℝ,SmallModes.Base) planeModel (coordinateInverse p) (coordinateChart p q)
  have hcomp : I.comp D = ContinuousLinearMap.id ℝ (TangentSpace planeModel q) :=
    coordinateInverse_mfderiv_right p hq
  have hv : I (D v) = v := congrArg (fun L => L v) hcomp
  have hw : I (D w) = w := congrArg (fun L => L w) hcomp
  change g.inner (coordinateInverse p (coordinateChart p q)) (I (D v)) (I (D w)) =
    g.inner q v w
  calc
    _ = g.inner (coordinateInverse p (coordinateChart p q)) v w :=
      congrArg₂ (fun a b : TangentSpace planeModel q =>
        g.inner (coordinateInverse p (coordinateChart p q)) a b) hv hw
    _ = g.inner q v w := congrArg (fun r => g.inner r v w) hinv

end ClosedSurfaceR4

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



lemma realMetricTensor_comp {n : ℕ} {F : RField n} {χ : Base → Base} {p : Base}
    (hF : DifferentiableAt ℝ F (χ p)) (hχ : DifferentiableAt ℝ χ p) :
    realMetricTensor (F ∘ χ) p = pullbackField χ p (realMetricTensor F (χ p)) := by
  ext i
  rw [realMetricTensor_apply]
  change realMetric (F ∘ χ) (firstDirection i) (secondDirection i) p =
    evaluate (realMetricTensor F (χ p))
      (fderiv ℝ χ p (firstDirection i)) (fderiv ℝ χ p (secondDirection i))
  rw [evaluate_realMetricTensor]
  simp only [realMetric, coordDeriv, fderiv_comp p hF hχ, ContinuousLinearMap.comp_apply]

end ClosedSurfaceR4.RealModes

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
local instance coordinateFiberSpace_r47cad9_1 : NormedSpace ℝ TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDualSmul
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateFiberGroup
lemma fiberToThree_apply (B : TensorFiber) (k : Fin 3) :
    fiberToThree B k = B (planeCoordinates.symm (firstDirection k))
      (planeCoordinates.symm (secondDirection k)) := rfl

lemma fiberToThree_fromThree (H : Tensor) : fiberToThree (fiberFromThree H) = H := by
  ext k
  change fiberFromThree H (planeCoordinates.symm (firstDirection k))
    (planeCoordinates.symm (secondDirection k)) = H k
  rw [fiberFromThree_apply]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  fin_cases k <;> simp [evaluate, firstDirection, secondDirection, SmallModes.dx, SmallModes.dy]

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
local instance chartReadSectionNormed_r47cad9_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance chartReadSectionSpace_r47cad9_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasJetCoordinateRelation
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual localized atlas maps on a coordinate overlap.  The transition
scalar is the square of the outer cutoff.  A nonzero partition weight gives
the needed equality of germs without any extra plateau hypothesis. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma outer_eventually_one_of_weight_ne_zero (i : A.centers) {p : M}
    (hp : A.weight i p ≠ 0) :
    A.outer i =ᶠ[𝓝 p] (fun _ => 1) := by
  have hn : ∀ᶠ q in 𝓝 p, A.weight i q ≠ 0 :=
    (isOpen_ne.preimage (A.weight_smooth i).continuous).mem_nhds hp
  filter_upwards [hn] with q hq
  exact A.outer_one i q (subset_tsupport (A.weight i) hq)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_MetricAtlasReference
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smooth metric section gives the reference tensor used by
the compact good-phase construction. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean
open JetPolynomial (planeCoordinateIsometry)
open JetPolynomial.Perturbation (modeSupport)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceFiberSpace
local instance metricReferenceSectionNormed_r47cad9_1 (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricReferenceSectionSpace_r47cad9_1 (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorComponent_metric (g : SmoothMetric M) (i : A.centers)
    {p : M} (hp : p ∈ (chart (i : M)).source) (v w : Plane) :
    A.bundleComponent A.tensorTriv i g.inner p v w =
      evaluate (coordinateMetric g (i : M) (coordinateChart (i : M) p))
        (planeCoordinates v) (planeCoordinates w) := by
  have ht : p ∈ (trivializationAt Plane (TangentSpace planeModel) (i : M)).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet, chart_source] using hp
  have hp' : p ∈ (coordinateChart (i : M)).source := by
    simpa only [coordinateChart_source, chart_source] using hp
  have hc := A.tensorComponent_tangentCoordinates i g.inner hp
    ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p v)
    ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p w)
  simp only [Trivialization.continuousLinearMapAt_symmL _ ht] at hc
  have hm := coordinateMetric_pullback_chart g (i : M) hp'
    ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p v)
    ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p w)
  rw [A.coordinateChart_tangentCoordinates i hp] at hm
  change evaluate (coordinateMetric g (i : M) (coordinateChart (i : M) p))
      (planeCoordinates
        ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p
          ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p v)))
      (planeCoordinates
        ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p
          ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p w))) =
      g.inner p
        ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p v)
        ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p w) at hm
  simp only [Trivialization.continuousLinearMapAt_symmL _ ht] at hm
  exact hc.trans hm.symm

lemma tensorPlaneRead_metric_on_weight (g : SmoothMetric M) (i : A.centers)
    {p : M} (hp : p ∈ tsupport (A.weight i)) :
    A.tensorPlaneRead i g.inner (planeCoordinateIsometry (chart (i : M) p)) =
      coordinateMetric g (i : M) (coordinateChart (i : M) p) := by
  change A.tensorChartRead i g.inner
    (planeCoordinateIsometry.symm (planeCoordinateIsometry (chart (i : M) p))) = _
  rw [LinearIsometryEquiv.symm_apply_apply, A.tensorChartRead_on_weight i g.inner hp]
  ext k
  rw [fiberToThree_apply, A.tensorComponent_metric g i (A.weight_support i hp)]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  fin_cases k <;> simp [evaluate, firstDirection, secondDirection, SmallModes.dx, SmallModes.dy]

variable [CompactSpace M]

lemma tensorPlaneRead_metric (g : SmoothMetric M) (i : A.centers)
    {x : SmallModes.Base} (hx : x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    A.tensorPlaneRead i g.inner x = coordinateMetric g (i : M) x := by
  change x ∈ planeCoordinateIsometry '' ((chart (i : M)) '' tsupport (A.weight i)) at hx
  rcases hx with ⟨y, ⟨p, hp, rfl⟩, rfl⟩
  exact A.tensorPlaneRead_metric_on_weight g i hp

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasMetricRead
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On the active chart locus the local metric is exactly the chart read
of the induced global metric. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReadExactDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReadExactFiberSpace
local instance metricReadExactDualSmul_r47cad9_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReadExactFiberNormed
local instance metricReadExactSectionNormed_r47cad9_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricReadExactSectionSpace_r47cad9_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma metric_component_on_weight (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {p : M}
    (hp : p ∈ tsupport (A.weight i)) :
    A.bundleComponent A.tensorTriv i (inducedTensor F) p =
      fiberFromThree (RealModes.realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p))) := by
  have hsource := A.weight_support i hp
  let f : Base → TensorFiber := fun y => fiberFromThree
    (RealModes.realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i F)
      (planeCoordinateIsometry y))
  have he : A.bundleRestore A.tensorTriv i f p = inducedTensor F p := by
    ext v w
    rw [A.tensorRestore_apply i f hsource,A.outer_one i p hp,one_mul]
    change fiberFromThree
      (RealModes.realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p)))
      ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p v)
      ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p w) =
        inducedForm F p v w
    rw [fiberFromThree_apply]
    have hd := A.vectorPlaneRead_differential i hF hp
    rw [A.plane_chart_differential i hsource] at hd
    have hv := congrArg (fun L => L v) hd
    have hw := congrArg (fun L => L w) hd
    simp only [ContinuousLinearMap.comp_apply] at hv hw
    rw [euclidean_metric_coordinate_value (A.vectorPlaneRead i F)
      ((A.vectorPlaneRead_smooth i hF).differentiable (by simp) _)]
    exact congrArg₂ (inner ℝ) hv.symm hw.symm
  have hc := congrArg ((A.tensorTriv i).continuousLinearMapAt ℝ p) he
  simp only [bundleRestore,A.outer_one i p hp,one_smul,
    (A.tensorTriv i).continuousLinearMapAt_symmL (A.tensorTriv_domain i hsource)] at hc
  exact hc.symm

lemma metric_read_on_weight (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {x : Base}
    (hx : A.chartWeight i x ≠ 0) :
    RealModes.realMetricTensor (A.jetChartMap i F ∘ planeCoordinateIsometry.symm)
        (planeCoordinateIsometry x) = A.tensorChartRead i (inducedTensor F) x := by
  have hxt : x ∈ (chart (i : M)).target := by
    by_contra hn
    exact hx (by simp only [chartWeight,indicator_of_notMem hn])
  have hw : A.weight i ((chart (i : M)).symm x) ≠ 0 := by
    simpa only [chartWeight,indicator_of_mem hxt] using hx
  have hp := subset_tsupport (A.weight i) hw
  have hread := A.tensorChartRead_on_weight i (inducedTensor F) hp
  rw [(chart (i : M)).right_inv hxt,A.metric_component_on_weight i hF hp,
    fiberToThree_fromThree,(chart (i : M)).right_inv hxt] at hread
  exact hread.symm

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasMetricJetMargins
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform first-jet geometry of approximate isometries in a fixed atlas. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
local instance metricJetsFiberNormed_r47cad9_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance metricJetsFiberSpace_r47cad9_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance metricJetsDualAdd_r47cad9_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance metricJetsDualSmul_r47cad9_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance metricJetsSectionNormed_r47cad9_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricJetsSectionSpace_r47cad9_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma modeSupport_subset_coordinateDomain (i : A.centers) :
    (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ coordinateDomain (i : M) := by
  rintro x ⟨y,⟨p,hp,rfl⟩,rfl⟩
  have hs : p ∈ (coordinateChart (i : M)).source := by
    simpa only [coordinateChart_source,chart_source] using A.weight_support i hp
  rw [← coordinateChart_target]
  exact (coordinateChart (i : M)).map_source hs

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RealMetricDerivatives
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate metric derivatives needed for the intrinsic Gauss expression.
The third derivatives cancel before any estimate is made. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.RealModes
open SmallModes

lemma real_partial_dot {n : ℕ} {F G : RField n} {p : Base}
    (hF : DifferentiableAt ℝ F p) (hG : DifferentiableAt ℝ G p) (v : Base) :
    coordDeriv v (fun q => F q ⬝ᵥ G q) p =
      coordDeriv v F p ⬝ᵥ G p+F p ⬝ᵥ coordDeriv v G p := by
  have hf (i : Fin n) := ((ContinuousLinearMap.proj i : RVec n →L[ℝ] ℝ).hasFDerivAt.comp p
    hF.hasFDerivAt)
  have hg (i : Fin n) := ((ContinuousLinearMap.proj i : RVec n →L[ℝ] ℝ).hasFDerivAt.comp p
    hG.hasFDerivAt)
  have hs := (HasFDerivAt.fun_sum fun i (_ : i ∈ Finset.univ) => (hf i).fun_mul (hg i)).fderiv
  simp only [Function.comp_def,ContinuousLinearMap.proj_apply] at hs
  unfold coordDeriv dotProduct
  rw [hs]
  simp only [sum_apply,add_apply,smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma real_dot_smooth {n : ℕ} {F G : RField n}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun q => F q ⬝ᵥ G q) :=
  ContDiff.sum (fun i _ => (contDiff_pi.mp hF i).mul (contDiff_pi.mp hG i))

lemma realMetric_partial {F : RField 4} (hF : ContDiff ℝ ∞ F) (p d v w : Base) :
    coordDeriv d (realMetric F v w) p =
      coordDeriv d (coordDeriv v F) p ⬝ᵥ coordDeriv w F p+
      coordDeriv v F p ⬝ᵥ coordDeriv d (coordDeriv w F) p :=
  real_partial_dot ((contDiff_real_coordDeriv hF v).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p)
    ((contDiff_real_coordDeriv hF w).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p) d

lemma realMetric_second_partial {F : RField 4} (hF : ContDiff ℝ ∞ F) (p d e v w : Base) :
    coordDeriv d (coordDeriv e (realMetric F v w)) p =
      coordDeriv d (coordDeriv e (coordDeriv v F)) p ⬝ᵥ coordDeriv w F p+
      coordDeriv e (coordDeriv v F) p ⬝ᵥ coordDeriv d (coordDeriv w F) p+
      (coordDeriv d (coordDeriv v F) p ⬝ᵥ coordDeriv e (coordDeriv w F) p+
      coordDeriv v F p ⬝ᵥ coordDeriv d (coordDeriv e (coordDeriv w F)) p) := by
  have hv := contDiff_real_coordDeriv hF v
  have hw := contDiff_real_coordDeriv hF w
  have hev := contDiff_real_coordDeriv hv e
  have hew := contDiff_real_coordDeriv hw e
  have he : coordDeriv e (realMetric F v w) = fun q =>
      coordDeriv e (coordDeriv v F) q ⬝ᵥ coordDeriv w F q+
      coordDeriv v F q ⬝ᵥ coordDeriv e (coordDeriv w F) q :=
    funext fun q => realMetric_partial hF q e v w
  rw [he,partial_add ((real_dot_smooth hev hw).differentiable (by simp) p)
    ((real_dot_smooth hv hew).differentiable (by simp) p),
    real_partial_dot (hev.differentiable (by simp) p) (hw.differentiable (by simp) p),
    real_partial_dot (hv.differentiable (by simp) p) (hew.differentiable (by simp) p)]

/-- The raw second-derivative Gauss expression only uses second metric jets. -/
theorem raw_gauss_metric_identity {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : Base) :
    coordDeriv dx (coordDeriv dx F) p ⬝ᵥ coordDeriv dy (coordDeriv dy F) p-
      coordDeriv dx (coordDeriv dy F) p ⬝ᵥ coordDeriv dx (coordDeriv dy F) p =
    (2*coordDeriv dx (coordDeriv dy (realMetric F dx dy)) p-
      coordDeriv dy (coordDeriv dy (realMetric F dx dx)) p-
      coordDeriv dx (coordDeriv dx (realMetric F dy dy)) p)/2 := by
  have hcomm : coordDeriv dy (coordDeriv dx F) = coordDeriv dx (coordDeriv dy F) :=
    funext fun q => real_second_coordDeriv_comm hF q dy dx
  have hthird : coordDeriv dy (coordDeriv dx (coordDeriv dy F)) =
      coordDeriv dx (coordDeriv dy (coordDeriv dy F)) :=
    funext fun q => real_second_coordDeriv_comm (contDiff_real_coordDeriv hF dy) q dy dx
  simp only [realMetric_second_partial hF,hcomm,hthird]
  rw [dotProduct_comm (coordDeriv dx (coordDeriv dx (coordDeriv dy F)) p),
    dotProduct_comm (coordDeriv dx (coordDeriv dy (coordDeriv dy F)) p)]
  ring

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CoordinateGauss
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate Gauss identity, proved from Euclidean derivatives and the
explicit normal projection.  Its right side depends only on the metric. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.RealModes
open SmallModes NormalFrame

lemma normalPart_dot_normalPart (X Y U V : RVec 4) (hD : gramDet X Y ≠ 0) :
    realNormalPart X Y U ⬝ᵥ realNormalPart X Y V = U ⬝ᵥ V-
      inverseMetricPair (X ⬝ᵥ X) (X ⬝ᵥ Y) (Y ⬝ᵥ Y)
        (X ⬝ᵥ U) (Y ⬝ᵥ U) (X ⬝ᵥ V) (Y ⬝ᵥ V) := by
  have hperp := realNormalPart_perp X Y U hD
  have hX : realNormalPart X Y U ⬝ᵥ X = 0 := (dotProduct_comm _ _).trans hperp.1
  have hY : realNormalPart X Y U ⬝ᵥ Y = 0 := (dotProduct_comm _ _).trans hperp.2
  have hcut : realNormalPart X Y U ⬝ᵥ realNormalPart X Y V =
      realNormalPart X Y U ⬝ᵥ V := by
    conv_lhs => arg 2; unfold realNormalPart
    simp only [dotProduct_sub,dotProduct_smul,hX,hY,smul_eq_mul,mul_zero,sub_zero]
  rw [hcut]
  simp only [realNormalPart,inverseMetricPair,NormalFrame.gramDet,sub_dotProduct,smul_dotProduct,
    smul_eq_mul]
  ring

theorem gauss_metric_identity {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : Base)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0) :
    realSecondForm F dx dx p ⬝ᵥ realSecondForm F dy dy p-
      realSecondForm F dx dy p ⬝ᵥ realSecondForm F dx dy p =
    coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p := by
  have hcomm : coordDeriv dy (coordDeriv dx F) = coordDeriv dx (coordDeriv dy F) :=
    funext fun q => real_second_coordDeriv_comm hF q dy dx
  unfold realSecondForm
  rw [normalPart_dot_normalPart _ _ _ _ hD,normalPart_dot_normalPart _ _ _ _ hD]
  unfold coordinateGauss
  rw [← raw_gauss_metric_identity hF p]
  simp only [realMetric_partial hF,hcomm,realMetric,inverseMetricPair,dotProduct_comm]
  ring

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PhaseBoundaryProfile
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Read the exact immersion's five profiles in the real coordinate chart
used by the Gauss and boundary calculations. -/
noncomputable section
open Set Manifold
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes SurfaceJetCoordinates GeometryPreservation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phaseRealChartMap_smooth (i : A.centers)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) :
    ContDiff ℝ ∞ (A.phaseRealChartMap i T F) :=
  (A.jetChartMap_smooth i hF).comp (hT.comp baseEquiv.symm.contDiff)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SurfacePhaseCharts
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual surface chart associated with a nonlinear phase. It is
independent of the correction atlas and supplies the chart transitions for later curves. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4
open SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
lemma surfacePhaseChart_apply (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (p : M) :
    surfacePhaseChart q e p = baseEquiv (e (FiniteOrderSmoothing.chart q p)) := rfl

omit [IsManifold planeModel ∞ M] in
lemma surfacePhaseChart_symm_apply (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (x : SmallModes.Base) :
    (surfacePhaseChart q e).symm x =
      (FiniteOrderSmoothing.chart q).symm (e.symm (baseEquiv.symm x)) := rfl

lemma surfacePhaseChart_smooth (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) :
    ContMDiffOn planeModel 𝓘(ℝ,SmallModes.Base) ∞ (surfacePhaseChart q e)
      (surfacePhaseChart q e).source := by
  exact (baseEquiv.contDiff.comp he).contMDiff.comp_contMDiffOn
    ((FiniteOrderSmoothing.chart_smooth q).mono (fun _ hx => hx.1))

lemma surfacePhaseChart_symm_smooth (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) :
    ContMDiffOn 𝓘(ℝ,SmallModes.Base) planeModel ∞ (surfacePhaseChart q e).symm
      (surfacePhaseChart q e).target := by
  exact (FiniteOrderSmoothing.chart_symm_smooth q).comp
    (hi.comp baseEquiv.symm.contDiff).contMDiff.contMDiffOn (fun _ hx => hx.2)

lemma surfacePhaseTransition_smooth (p : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) (q : M)
    (f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hf : ContDiff ℝ ∞ f) :
    ContDiffOn ℝ ∞ (surfacePhaseTransition p e q f) (surfacePhaseTransition p e q f).source := by
  apply ContMDiffOn.contDiffOn
  exact (surfacePhaseChart_smooth q f hf).comp
    ((surfacePhaseChart_symm_smooth p e hi).mono (fun _ hx => hx.1)) (fun _ hx => hx.2)

lemma surfacePhaseTransition_det_ne (p : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm) (q : M)
    (f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hf : ContDiff ℝ ∞ f) (hfi : ContDiff ℝ ∞ f.symm)
    {x : SmallModes.Base} (hx : x ∈ (surfacePhaseTransition p e q f).source) :
    RealModes.coordDet (fderiv ℝ (surfacePhaseTransition p e q f) x) ≠ 0 := by
  let T := surfacePhaseTransition p e q f
  have hs : ContDiffOn ℝ ∞ T T.source := surfacePhaseTransition_smooth p e hi q f hf
  have ht : ContDiffOn ℝ ∞ T.symm T.target := by
    change ContDiffOn ℝ ∞ (surfacePhaseTransition q f p e) (surfacePhaseTransition q f p e).source
    exact surfacePhaseTransition_smooth q f hfi p e he
  exact RealModes.coordDet_fderiv_ne_zero_of_local_inverse T.open_source T.open_target
    hs ht T.mapsTo (fun y hy => T.left_inv hy) hx

omit [IsManifold planeModel ∞ M] in
lemma surfacePhaseMap_transition_germ (p q : M)
    (e f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (F : M → Space)
    {x : SmallModes.Base} (hx : x ∈ (surfacePhaseTransition p e q f).source) :
    surfacePhaseMap p e F =ᶠ[𝓝 x]
      surfacePhaseMap q f F ∘ surfacePhaseTransition p e q f := by
  filter_upwards [(surfacePhaseTransition p e q f).open_source.mem_nhds hx] with y hy
  change spaceCoordinates (F ((surfacePhaseChart p e).symm y)) =
    spaceCoordinates (F ((surfacePhaseChart q f).symm
      ((surfacePhaseChart q f) ((surfacePhaseChart p e).symm y))))
  have hyj : (surfacePhaseChart p e).symm y ∈ (surfacePhaseChart q f).source := hy.2
  rw [(surfacePhaseChart q f).left_inv hyj]

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_JetMetricCoordinatePullback
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete metric-plus-polynomial operator transforms through fixed
nonlinear coordinates, including its finite periodic error. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.JetPolynomial
open RealModes

lemma metric_coordinate_pullback {F : Base → Space} {T : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hT : ContDiff ℝ ∞ T) (x : Base) :
    realMetricTensor ((F ∘ T) ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry x) =
      tensorCoordinatePullbackValue T x
        (realMetricTensor (F ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry (T x))) := by
  let τ : SmallModes.Base → SmallModes.Base :=
    planeCoordinateIsometry ∘ T ∘ planeCoordinateIsometry.symm
  have hτ : ContDiff ℝ ∞ τ := planeCoordinateIsometry.contDiff.comp
    (hT.comp planeCoordinateIsometry.symm.contDiff)
  have he : (F ∘ planeCoordinateIsometry.symm) ∘ τ =
      (F ∘ T) ∘ planeCoordinateIsometry.symm := by
    funext p
    simp [τ]
  rw [← he,realMetricTensor_comp
    ((hF.comp planeCoordinateIsometry.symm.contDiff).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _) (hτ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _)]
  have hd : fderiv ℝ τ (planeCoordinateIsometry x) = tensorCoordinateDerivative T x := by
    dsimp [τ]
    rw [fderiv_comp _ (planeCoordinateIsometry.differentiableAt)
      ((hT.comp planeCoordinateIsometry.symm.contDiff).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _),
      fderiv_comp _ (hT.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _) planeCoordinateIsometry.symm.differentiableAt]
    simp only [LinearIsometryEquiv.fderiv,LinearIsometryEquiv.symm_apply_apply]
    rfl
  simp only [PhaseMean.pullbackField,hd,τ,Function.comp_apply,LinearIsometryEquiv.symm_apply_apply,tensorCoordinatePullbackValue]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseMetricRead
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The metric and intrinsic Gauss expression in phase coordinates are
fixed by the prescribed global metric, independently of its isometric
realization. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes SurfaceJetCoordinates JetPolynomial
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phaseMetricRead_isometry (i : A.centers) {T : JetPolynomial.Base → JetPolynomial.Base}
    (hT : ContDiff ℝ ∞ T) {g : SmoothMetric M} {F : M → Space}
    (hF : IsSmoothIsometricImmersion M g F) {p : JetPolynomial.Base}
    (hp : A.chartWeight i (T p) ≠ 0) :
    realMetricTensor (A.phaseRealChartMap i T F) (baseEquiv p) =
      A.phaseMetricRead i T g (baseEquiv p) := by
  have hm : g.inner = inducedTensor F := by
    funext q
    ext v w
    exact (hF.2 q v w).symm
  change realMetricTensor ((A.jetChartMap i F ∘ T) ∘ planeCoordinateIsometry.symm)
    (planeCoordinateIsometry p) = _
  rw [metric_coordinate_pullback (A.jetChartMap_smooth i hF.1) hT p,
    A.metric_read_on_weight i hF.1 hp,← hm]
  simp only [phaseMetricRead,baseEquiv.symm_apply_apply]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PositiveTensorPullback
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Matrix
namespace ClosedSurfaceR4.PhaseMean
open SmallModes

lemma evaluate_pullback (L : Base →L[ℝ] Base) (H : Tensor) (v w : Base) :
    evaluate (pullback L H) v w = evaluate H (L v) (L w) := by
  have hL (u : Base) : L u = u.1 • L dx + u.2 • L dy := by
    rw [← map_smul,← map_smul,← map_add]
    congr 1
    ext <;> simp [dx,dy]
  change evaluate H (L dx) (L dx) * v.1 * w.1 +
    evaluate H (L dx) (L dy) * (v.1*w.2+v.2*w.1) +
    evaluate H (L dy) (L dy) * v.2 * w.2 = evaluate H (L v) (L w)
  rw [hL v,hL w]
  simp only [evaluate,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

lemma positive_pullback (L : Base →L[ℝ] Base) (hL : Function.Injective L) {H : Tensor}
    (hH : 0 < H 0 ∧ 0 < H 0*H 2-(H 1)^2) :
    0 < pullback L H 0 ∧ 0 < pullback L H 0*pullback L H 2-(pullback L H 1)^2 := by
  apply (tensor_positive_iff _).mp
  intro v hv
  rw [evaluate_pullback]
  apply (tensor_positive_iff H).mpr hH
  intro hz
  exact hv (hL (by simpa using hz))

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseMetricPositive
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity of the prescribed metric survives the actual inverse phase
chart. In particular its curvature denominator is nonzero on the active
chart locus. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes SurfaceJetCoordinates JetPolynomial
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phaseMetricRead_positive (i : A.centers) (g : SmoothMetric M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {p : JetPolynomial.Base} (hp : p ∈ e.target) (hactive : A.chartWeight i (e.symm p) ≠ 0) :
    0 < A.phaseMetricRead i e.symm g (baseEquiv p) 0 ∧
      0 < A.phaseMetricRead i e.symm g (baseEquiv p) 0 *
        A.phaseMetricRead i e.symm g (baseEquiv p) 2 -
          (A.phaseMetricRead i e.symm g (baseEquiv p) 1)^2 := by
  have hpt : e.symm p ∈ (A.chartWeightCompact i : Set JetPolynomial.Base) := by
    rw [← A.chartWeight_tsupport i]
    exact subset_tsupport (A.chartWeight i) hactive
  have hmode : planeCoordinateIsometry (e.symm p) ∈
      (JetPolynomial.Perturbation.modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) :=
    ⟨e.symm p,hpt,rfl⟩
  have hm := A.tensorPlaneRead_metric g i hmode
  have hpositive := coordinateMetric_positive g (i : M) (A.modeSupport_subset_coordinateDomain i hmode)
  have hold : 0 < A.tensorChartRead i g.inner (e.symm p) 0 ∧
      0 < A.tensorChartRead i g.inner (e.symm p) 0 * A.tensorChartRead i g.inner (e.symm p) 2 -
        (A.tensorChartRead i g.inner (e.symm p) 1)^2 := by
    rw [← hm] at hpositive
    simpa only [tensorPlaneRead,Function.comp_apply,LinearIsometryEquiv.symm_apply_apply] using hpositive
  have hinv : e ∘ e.symm =ᶠ[𝓝 p] id := by
    filter_upwards [e.open_target.mem_nhds hp] with q hq
    exact e.right_inv hq
  have hcomp : (fderiv ℝ e (e.symm p)).comp (fderiv ℝ e.symm p) =
      ContinuousLinearMap.id ℝ JetPolynomial.Base := by
    rw [← fderiv_comp p (he.differentiable (by simp) _) (hi.differentiable (by simp) _),
      hinv.fderiv_eq,fderiv_id]
  have hdi : Function.Injective (fderiv ℝ e.symm p) := by
    intro u v huv
    have hh := congrArg (fderiv ℝ e (e.symm p)) huv
    change ((fderiv ℝ e (e.symm p)).comp (fderiv ℝ e.symm p)) u =
      ((fderiv ℝ e (e.symm p)).comp (fderiv ℝ e.symm p)) v at hh
    simpa only [hcomp,ContinuousLinearMap.id_apply] using hh
  have hL : Function.Injective (tensorCoordinateDerivative e.symm p) :=
    planeCoordinateIsometry.injective.comp (hdi.comp planeCoordinateIsometry.symm.injective)
  have hh := PhaseMean.positive_pullback (tensorCoordinateDerivative e.symm p) hL hold
  simpa only [phaseMetricRead,baseEquiv.symm_apply_apply,tensorCoordinatePullbackValue] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseMetricRegularity
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes SurfaceJetCoordinates NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phaseMetricRead_isometry_det (i : A.centers)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    {p : SmallModes.Base} (hp : A.chartWeight i (T (baseEquiv.symm p)) ≠ 0) :
    gramDet (SmallModes.coordDeriv SmallModes.dx (A.phaseRealChartMap i T F) p)
      (SmallModes.coordDeriv SmallModes.dy (A.phaseRealChartMap i T F) p) =
    A.phaseMetricRead i T g p 0 * A.phaseMetricRead i T g p 2 -
      (A.phaseMetricRead i T g p 1)^2 := by
  have hm := A.phaseMetricRead_isometry i hT hF (p := baseEquiv.symm p) hp
  rw [baseEquiv.apply_symm_apply] at hm
  have hh := congrArg (fun H : PhaseMean.Tensor => H 0*H 2-(H 1)^2) hm
  exact hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

namespace ClosedSurfaceR4.RealModes
open SmallModes NormalFrame
lemma coordinateGauss_eq_curvature_mul (F : RField 4) (p : Base)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0) :
    coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p =
      coordinateGaussianCurvature (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p *
        gramDet (coordDeriv dx F p) (coordDeriv dy F p) := by
  change _ = (_ / gramDet (coordDeriv dx F p) (coordDeriv dy F p)) * _
  exact (div_mul_cancel₀ _ hD).symm
end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CurveSecondFields
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth global representatives of second-form fields along a compact curve.
A cutoff in its own phase chart extends the field without choosing a normal frame. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes SmallModes NormalFrame SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phase_gram_ne_zero (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    {p : SmallModes.Base} (hp : baseEquiv.symm p ∈ e.target)
    (ha : A.chartWeight i (e.symm (baseEquiv.symm p)) ≠ 0) :
    gramDet (coordDeriv dx (A.phaseRealChartMap i e.symm F) p)
      (coordDeriv dy (A.phaseRealChartMap i e.symm F) p) ≠ 0 := by
  rw [A.phaseMetricRead_isometry_det i hi hF ha]
  have hh := (A.phaseMetricRead_positive i g e he hi hp ha).2.ne'
  simpa only [baseEquiv.apply_symm_apply] using hh

omit [CompactSpace M] in
lemma phaseCurveSecondField_eq (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (β : SmallModes.Base → ℝ) (F : M → Space) (v w : SmallModes.Base → SmallModes.Base)
    {p : M} (hp : p ∈ (chart (i : M)).source) (ho : A.outer i p = 1)
    (hβ : β (baseEquiv (e (chart (i : M) p))) = 1) :
    spaceCoordinates (A.phaseCurveSecondField i e β F v w p) =
      realSecondForm (A.phaseRealChartMap i e.symm F)
        (v (baseEquiv (e (chart (i : M) p)))) (w (baseEquiv (e (chart (i : M) p))))
        (baseEquiv (e (chart (i : M) p))) := by
  simp only [phaseCurveSecondField,restore,indicator_of_mem hp,ho,hβ,one_smul,
    spaceCoordinates.apply_symm_apply]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CrossingPositivePairing
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The boundary Gauss inequality used when matching the interior and
exterior preferred normals. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.VelocityFrame
open SmallModes RealModes NormalFrame

lemma secondForm_gauss_directions {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (p v w : Base) :
    realSecondForm F v v p ⬝ᵥ realSecondForm F w w p -
      realSecondForm F v w p ⬝ᵥ realSecondForm F v w p =
    (v.1*w.2-v.2*w.1)^2 *
      (realSecondForm F dx dx p ⬝ᵥ realSecondForm F dy dy p -
        realSecondForm F dx dy p ⬝ᵥ realSecondForm F dx dy p) := by
  conv_lhs =>
    simp only [realSecondForm_bilinear hF v v,realSecondForm_bilinear hF w w,
      realSecondForm_bilinear hF v w]
  simp only [realSecondTensor,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
    add_dotProduct,dotProduct_add,smul_dotProduct,dotProduct_smul,smul_eq_mul,
    dotProduct_comm (realSecondForm F dy dy p) (realSecondForm F dx dx p),
    dotProduct_comm (realSecondForm F dx dy p) (realSecondForm F dx dx p),
    dotProduct_comm (realSecondForm F dy dy p) (realSecondForm F dx dy p)]
  ring

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_IntrinsicCrossingNaturality
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The intrinsic ordered crossing is expressed entirely by the second
fundamental form, and is unchanged under smooth coordinate changes. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.VelocityFrame
open SmallModes RealModes NormalFrame PhaseGeometry

lemma orderedCrossing_intrinsic_eq {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (p v w : Base) (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0) :
    orderedCrossing F v w p
        (coordinateGaussianCurvature (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p) =
      (realSecondForm F v w p ⬝ᵥ normalize (realSecondForm F v v p))^2 +
        realSecondForm F v v p ⬝ᵥ realSecondForm F w w p -
          realSecondForm F v w p ⬝ᵥ realSecondForm F v w p := by
  have hgram : gramDet (coordDeriv v F p) (coordDeriv w F p) =
      (v.1*w.2-v.2*w.1)^2*gramDet (coordDeriv dx F p) (coordDeriv dy F p) := by
    rw [coordDeriv_eq_basis F v,coordDeriv_eq_basis F w,gramDet_change_basis]
  have hg := secondForm_gauss_directions hF p v w
  rw [gauss_metric_identity hF p hD,coordinateGauss_eq_curvature_mul F p hD] at hg
  unfold orderedCrossing
  rw [hgram]
  nlinarith only [hg]

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseChartTransition
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The localized analytic maps have the same second forms as the actual
surface phase charts. This permits later curves to keep their own charts. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates RealModes SmallModes PhaseGeometry VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas

omit [CompactSpace M] in
lemma phaseRealChartMap_surface_germ (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (F : M → Space)
    {x : SmallModes.Base} (hx : x ∈ (surfacePhaseChart (i : M) e).target)
    (hw : A.weight i ((surfacePhaseChart (i : M) e).symm x) ≠ 0) :
    A.phaseRealChartMap i e.symm F =ᶠ[𝓝 x] surfacePhaseMap (i : M) e F := by
  have ho := (A.outer_eventually_one_of_weight_ne_zero i hw).comp_tendsto
    ((surfacePhaseChart (i : M) e).continuousAt_symm hx)
  filter_upwards [(surfacePhaseChart (i : M) e).open_target.mem_nhds hx,ho] with y hy hoy
  have hyt : e.symm (baseEquiv.symm y) ∈ (chart (i : M)).target := hy.2
  change spaceCoordinates (A.vectorChartRead i F (e.symm (baseEquiv.symm y))) =
    spaceCoordinates (F ((chart (i : M)).symm (e.symm (baseEquiv.symm y))))
  change A.outer i ((chart (i : M)).symm (e.symm (baseEquiv.symm y))) = 1 at hoy
  simp only [vectorChartRead,localize,indicator_of_mem hyt,hoy,one_pow,one_smul]

omit [CompactSpace M] in
lemma phaseRealChartMap_transition_germ (A B : SmoothingAtlas M)
    (i : A.centers) (j : B.centers)
    (e f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (F : M → Space)
    {x : SmallModes.Base} (hx : x ∈ (surfacePhaseTransition (i : M) e (j : M) f).source)
    (hwA : A.weight i ((surfacePhaseChart (i : M) e).symm x) ≠ 0)
    (hwB : B.weight j ((surfacePhaseChart (i : M) e).symm x) ≠ 0) :
    A.phaseRealChartMap i e.symm F =ᶠ[𝓝 x]
      B.phaseRealChartMap j f.symm F ∘ surfacePhaseTransition (i : M) e (j : M) f := by
  have hxA : x ∈ (surfacePhaseChart (i : M) e).target := hx.1
  have hxB : (surfacePhaseChart (i : M) e).symm x ∈ (surfacePhaseChart (j : M) f).source := hx.2
  let T := surfacePhaseTransition (i : M) e (j : M) f
  have hy : T x ∈ (surfacePhaseChart (j : M) f).target :=
    (surfacePhaseChart (j : M) f).map_source hxB
  have hwy : B.weight j ((surfacePhaseChart (j : M) f).symm (T x)) ≠ 0 := by
    change B.weight j ((surfacePhaseChart (j : M) f).symm
      ((surfacePhaseChart (j : M) f) ((surfacePhaseChart (i : M) e).symm x))) ≠ 0
    rwa [(surfacePhaseChart (j : M) f).left_inv hxB]
  exact (A.phaseRealChartMap_surface_germ i e F hxA hwA).trans
    ((surfacePhaseMap_transition_germ (i : M) (j : M) e f F hx).trans
      (((B.phaseRealChartMap_surface_germ j f F hy hwy).comp_tendsto
        (T.continuousAt hx)).symm))

lemma phase_secondForm_transition (A B : SmoothingAtlas M)
    (i : A.centers) (j : B.centers)
    (e f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (hf : ContDiff ℝ ∞ f) (hfi : ContDiff ℝ ∞ f.symm)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    {x : SmallModes.Base} (hx : x ∈ (surfacePhaseTransition (i : M) e (j : M) f).source)
    (hwA : A.weight i ((surfacePhaseChart (i : M) e).symm x) ≠ 0)
    (hwB : B.weight j ((surfacePhaseChart (i : M) e).symm x) ≠ 0)
    (v w : SmallModes.Base) :
    let T := surfacePhaseTransition (i : M) e (j : M) f
    realSecondForm (A.phaseRealChartMap i e.symm F) v w x =
      realSecondForm (B.phaseRealChartMap j f.symm F)
        (fderiv ℝ T x v) (fderiv ℝ T x w) (T x) := by
  let T := surfacePhaseTransition (i : M) e (j : M) f
  have hg := A.phaseRealChartMap_transition_germ B i j e f F hx hwA hwB
  have hxB : (surfacePhaseChart (i : M) e).symm x ∈ (surfacePhaseChart (j : M) f).source := hx.2
  have hy : T x ∈ (surfacePhaseChart (j : M) f).target :=
    (surfacePhaseChart (j : M) f).map_source hxB
  have hwy : B.chartWeight j (f.symm (baseEquiv.symm (T x))) ≠ 0 := by
    have hyw : B.weight j ((surfacePhaseChart (j : M) f).symm (T x)) ≠ 0 := by
      change B.weight j ((surfacePhaseChart (j : M) f).symm
        ((surfacePhaseChart (j : M) f) ((surfacePhaseChart (i : M) e).symm x))) ≠ 0
      rwa [(surfacePhaseChart (j : M) f).left_inv hxB]
    have hyt : f.symm (baseEquiv.symm (T x)) ∈ (chart (j : M)).target := hy.2
    rw [chartWeight,indicator_of_mem hyt]
    simpa only [surfacePhaseChart_symm_apply] using hyw
  rw [(realSecondForm_eventuallyEq hg v w).eq_of_nhds]
  exact realSecondForm_comp_on T.open_source isOpen_univ
    (B.phaseRealChartMap_smooth j hfi hF.1).contDiffOn
    (surfacePhaseTransition_smooth (i : M) e hi (j : M) f hf) hx (mem_univ _) v w
    (B.phase_gram_ne_zero j f hf hfi hF hy.1 hwy)
    (surfacePhaseTransition_det_ne (i : M) e he hi (j : M) f hf hfi hx)

lemma phase_intrinsic_crossing_transition (A B : SmoothingAtlas M)
    (i : A.centers) (j : B.centers)
    (e f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (hf : ContDiff ℝ ∞ f) (hfi : ContDiff ℝ ∞ f.symm)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    {x : SmallModes.Base} (hx : x ∈ (surfacePhaseTransition (i : M) e (j : M) f).source)
    (hwA : A.weight i ((surfacePhaseChart (i : M) e).symm x) ≠ 0)
    (hwB : B.weight j ((surfacePhaseChart (i : M) e).symm x) ≠ 0)
    (v w : SmallModes.Base) :
    let T := surfacePhaseTransition (i : M) e (j : M) f
    let H := A.phaseRealChartMap i e.symm F
    let G := B.phaseRealChartMap j f.symm F
    orderedCrossing H v w x
      (coordinateGaussianCurvature (realMetric H dx dx) (realMetric H dx dy) (realMetric H dy dy) x) =
    orderedCrossing G (fderiv ℝ T x v) (fderiv ℝ T x w) (T x)
      (coordinateGaussianCurvature (realMetric G dx dx) (realMetric G dx dy) (realMetric G dy dy) (T x)) := by
  let T := surfacePhaseTransition (i : M) e (j : M) f
  have hxA : x ∈ (surfacePhaseChart (i : M) e).target := hx.1
  have htA : e.symm (baseEquiv.symm x) ∈ (chart (i : M)).target := hxA.2
  have ha : A.chartWeight i (e.symm (baseEquiv.symm x)) ≠ 0 := by
    rw [chartWeight,indicator_of_mem htA]
    exact hwA
  have hxB : (surfacePhaseChart (i : M) e).symm x ∈ (surfacePhaseChart (j : M) f).source := hx.2
  have hy : T x ∈ (surfacePhaseChart (j : M) f).target :=
    (surfacePhaseChart (j : M) f).map_source hxB
  have htB : f.symm (baseEquiv.symm (T x)) ∈ (chart (j : M)).target := hy.2
  have hb : B.chartWeight j (f.symm (baseEquiv.symm (T x))) ≠ 0 := by
    rw [chartWeight,indicator_of_mem htB]
    change B.weight j ((surfacePhaseChart (j : M) f).symm
      ((surfacePhaseChart (j : M) f) ((surfacePhaseChart (i : M) e).symm x))) ≠ 0
    rwa [(surfacePhaseChart (j : M) f).left_inv hxB]
  dsimp only
  rw [orderedCrossing_intrinsic_eq (A.phaseRealChartMap_smooth i hi hF.1) x v w
      (A.phase_gram_ne_zero i e he hi hF hxA.1 ha),
    orderedCrossing_intrinsic_eq (B.phaseRealChartMap_smooth j hfi hF.1) (T x) _ _
      (B.phase_gram_ne_zero j f hf hfi hF hy.1 hb),
    A.phase_secondForm_transition B i j e f he hi hf hfi hF hx hwA hwB v w,
    A.phase_secondForm_transition B i j e f he hi hf hfi hF hx hwA hwB v v,
    A.phase_secondForm_transition B i j e f he hi hf hfi hF hx hwA hwB w w]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseTransitionVectors
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A later curve's transverse coordinate vector, transported to the
current phase chart and extended smoothly from its compact overlap. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma fderiv_local_inverse_injective
    (e : OpenPartialHomeomorph Base Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {x : Base} (hx : x ∈ e.source) : Function.Injective (fderiv ℝ e x) := by
  have hd := ((he x hx).contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hdi := ((hi (e x) (e.map_source hx)).contDiffAt
    (e.open_target.mem_nhds (e.map_source hx))).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have heq : e.symm ∘ e =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact e.left_inv hy
  have hc : (fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x) = ContinuousLinearMap.id ℝ Base := by
    rw [← fderiv_comp x hdi hd,heq.fderiv_eq,fderiv_id]
  intro v w h
  have hh := congrArg (fderiv ℝ e.symm (e x)) h
  change ((fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x)) v =
    ((fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x)) w at hh
  simpa only [hc,ContinuousLinearMap.id_apply] using hh

theorem compact_transverse_vector
    (e : OpenPartialHomeomorph Base Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {K : Set Base} (hK : IsCompact K) (hKe : K ⊆ e.target) :
    ∃ v : Base → Base, ContDiff ℝ ∞ v ∧
      ∀ x ∈ K, v x = fderiv ℝ e (e.symm x) dy ∧ v x ≠ 0 := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ e) e.source :=
    he.fderiv_of_isOpen e.open_source (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hvec : ContDiffOn ℝ ∞ (fun x => fderiv ℝ e (e.symm x) dy) e.target :=
    (hD.clm_apply contDiffOn_const).comp hi e.symm.mapsTo
  obtain ⟨U,_,hKU,_,v,hv,hveq⟩ := CollarVelocity.compact_smooth_extension hK e.open_target hKe hvec
  refine ⟨v,hv,?_⟩
  intro x hx
  have hh := hveq (hKU hx)
  refine ⟨hh,?_⟩
  rw [hh]
  have hinj := fderiv_local_inverse_injective e he hi (e.map_target (hKe hx))
  intro hz
  have hdy := hinj (hz.trans (map_zero (fderiv ℝ e (e.symm x))).symm)
  exact (show (dy : Base) ≠ 0 from by simp [dy]) hdy

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CurveSecondTransition
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A curve's global second-form representative agrees with its transported
second form in the current primitive chart. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas

lemma curveSecondField_transition (A B : SmoothingAtlas M)
    (i : A.centers) (j : B.centers)
    (e f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (hf : ContDiff ℝ ∞ f) (hfi : ContDiff ℝ ∞ f.symm)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (β : SmallModes.Base → ℝ)
    {x : SmallModes.Base} (hx : x ∈ (surfacePhaseTransition (j : M) f (i : M) e).source)
    (hwB : B.weight j ((surfacePhaseChart (j : M) f).symm x) ≠ 0)
    (hwA : A.weight i ((surfacePhaseChart (j : M) f).symm x) ≠ 0)
    (hβ : β x = 1) :
    let T := surfacePhaseTransition (j : M) f (i : M) e
    spaceCoordinates (B.phaseCurveSecondField j f β F (fun _ => dy) (fun _ => dy)
      ((surfacePhaseChart (j : M) f).symm x)) =
      realSecondForm (A.phaseRealChartMap i e.symm F)
        (fderiv ℝ T x dy) (fderiv ℝ T x dy) (T x) := by
  have hxj : x ∈ (surfacePhaseChart (j : M) f).target := hx.1
  have hp := (surfacePhaseChart (j : M) f).map_target hxj
  have hread := B.phaseCurveSecondField_eq j f β F (fun _ => dy) (fun _ => dy)
    hp.1 (B.outer_one j _ (subset_tsupport (B.weight j) hwB)) (by
      change β ((surfacePhaseChart (j : M) f) ((surfacePhaseChart (j : M) f).symm x)) = 1
      rwa [(surfacePhaseChart (j : M) f).right_inv hxj])
  have hr : baseEquiv (f (chart (j : M) ((surfacePhaseChart (j : M) f).symm x))) = x :=
    (surfacePhaseChart (j : M) f).right_inv hxj
  simp only [hr] at hread
  rw [hread]
  exact B.phase_secondForm_transition A j i f e hf hfi he hi hF hx hwB hwA dy dy

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseBoundaryCurve
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed compact boundary curves and their actual second-form fields.
The cutoff is chosen from the curve geometry, independently of any immersion. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes SmallModes VelocityFrame NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace PhaseBoundaryCurve
variable {B : SmoothingAtlas M} (c : PhaseBoundaryCurve B)

lemma cutoff_properties : ContDiff ℝ ∞ c.cutoff ∧ HasCompactSupport c.cutoff ∧
    (∀ x ∈ c.coordinate '' c.carrier, c.cutoff x = 1) ∧
    ∀ x ∈ tsupport c.cutoff, baseEquiv.symm x ∈ c.phase.target ∧
      B.chartWeight c.index (c.phase.symm (baseEquiv.symm x)) ≠ 0 :=
  Classical.choose_spec c.cutoff_exists

lemma second_transition (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    {p : M} (hp : p ∈ c.carrier)
    (hps : p ∈ (surfacePhaseChart (i : M) e).source) (hw : A.weight i p ≠ 0) :
    let T := surfacePhaseTransition (c.index : M) c.phase (i : M) e
    c.second F p = realSecondForm (A.phaseRealChartMap i e.symm F)
      (fderiv ℝ T (c.coordinate p) dy) (fderiv ℝ T (c.coordinate p) dy)
      (baseEquiv (e (chart (i : M) p))) := by
  have hpc : p ∈ (surfacePhaseChart (c.index : M) c.phase).source := c.source hp
  have hback : (surfacePhaseChart (c.index : M) c.phase).symm (c.coordinate p) = p :=
    (surfacePhaseChart (c.index : M) c.phase).left_inv hpc
  have hx : c.coordinate p ∈ (surfacePhaseTransition (c.index : M) c.phase (i : M) e).source := by
    refine ⟨(surfacePhaseChart (c.index : M) c.phase).map_source hpc,?_⟩
    change (surfacePhaseChart (c.index : M) c.phase).symm (c.coordinate p) ∈
      (surfacePhaseChart (i : M) e).source
    rwa [hback]
  have h := A.curveSecondField_transition B i c.index e c.phase he hi c.smooth c.inverse_smooth
    hF c.cutoff hx (by rw [hback]; exact c.active p hp) (by rwa [hback])
    (c.cutoff_properties.2.2.1 _ ⟨p,hp,rfl⟩)
  have ht : surfacePhaseTransition (c.index : M) c.phase (i : M) e (c.coordinate p) =
      baseEquiv (e (chart (i : M) p)) := by
    change (surfacePhaseChart (i : M) e)
      ((surfacePhaseChart (c.index : M) c.phase).symm (c.coordinate p)) = _
    rw [hback]
    rfl
  change spaceCoordinates (B.phaseCurveSecondField c.index c.phase c.cutoff F
    (fun _ => dy) (fun _ => dy)
    ((surfacePhaseChart (c.index : M) c.phase).symm (c.coordinate p))) =
    realSecondForm (A.phaseRealChartMap i e.symm F)
      (fderiv ℝ (surfacePhaseTransition (c.index : M) c.phase (i : M) e) (c.coordinate p) dy)
      (fderiv ℝ (surfacePhaseTransition (c.index : M) c.phase (i : M) e) (c.coordinate p) dy)
      (surfacePhaseTransition (c.index : M) c.phase (i : M) e (c.coordinate p)) at h
  rw [hback,ht] at h
  exact h

end PhaseBoundaryCurve
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CompactPhaseCurveVectors
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth direction coefficients for the actual pieces of later curves
inside one fixed primitive disk. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace PhaseBoundaryCurve
variable {B : SmoothingAtlas M} (c : PhaseBoundaryCurve B)

omit [CompactSpace M] in
lemma inPhase_compact (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {K : Set M} (hK : IsCompact K) (hKs : K ⊆ (surfacePhaseChart q e).source) :
    IsCompact (c.inPhase q e K) :=
  (c.compact.inter hK).image_of_continuousOn
    ((surfacePhaseChart q e).continuousOn.mono (fun _ hp => hKs hp.2))

omit [CompactSpace M] [T2Space M] in
lemma inPhase_transition_target (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {K : Set M} (hKs : K ⊆ (surfacePhaseChart q e).source) :
    c.inPhase q e K ⊆ (surfacePhaseTransition (c.index : M) c.phase q e).target := by
  rintro _ ⟨p,hp,rfl⟩
  change surfacePhaseChart q e p ∈
    ((surfacePhaseChart (c.index : M) c.phase).symm.trans (surfacePhaseChart q e)).target
  refine ⟨(surfacePhaseChart q e).map_source (hKs hp.2),?_⟩
  change (surfacePhaseChart q e).symm (surfacePhaseChart q e p) ∈
    (surfacePhaseChart (c.index : M) c.phase).source
  rw [(surfacePhaseChart q e).left_inv (hKs hp.2)]
  exact c.source hp.1

omit [CompactSpace M] [T2Space M] in
lemma coordinate_transition (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {p : M} (hp : p ∈ c.carrier) :
    surfacePhaseTransition (c.index : M) c.phase q e (c.coordinate p) = surfacePhaseChart q e p := by
  change surfacePhaseChart q e ((surfacePhaseChart (c.index : M) c.phase).symm
    ((surfacePhaseChart (c.index : M) c.phase) p)) = _
  rw [(surfacePhaseChart (c.index : M) c.phase).left_inv (c.source hp)]

omit [CompactSpace M] in
theorem inPhase_direction_coefficients (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {K : Set M} (hK : IsCompact K) (hKs : K ⊆ (surfacePhaseChart q e).source) :
    ∃ b d : Base → ℝ, ContDiff ℝ ∞ b ∧ ContDiff ℝ ∞ d ∧
      (∀ x ∈ c.inPhase q e K, b x ≠ 0 ∨ d x ≠ 0) ∧
      ∀ p ∈ c.carrier ∩ K,
        (b (surfacePhaseChart q e p),d (surfacePhaseChart q e p)) =
          fderiv ℝ (surfacePhaseTransition (c.index : M) c.phase q e) (c.coordinate p) dy := by
  let T := surfacePhaseTransition (c.index : M) c.phase q e
  obtain ⟨v,hv,hspec⟩ := compact_transverse_vector T
    (surfacePhaseTransition_smooth (c.index : M) c.phase c.inverse_smooth q e he)
    (surfacePhaseTransition_smooth q e hi (c.index : M) c.phase c.smooth)
    (c.inPhase_compact q e hK hKs) (c.inPhase_transition_target q e hKs)
  refine ⟨fun x => (v x).1,fun x => (v x).2,hv.fst,hv.snd,?_,?_⟩
  · intro x hx
    by_contra hh
    push Not at hh
    exact (hspec x hx).2 (Prod.ext hh.1 hh.2)
  · intro p hp
    change v (surfacePhaseChart q e p) = _
    have hx : surfacePhaseChart q e p ∈ c.inPhase q e K := mem_image_of_mem _ hp
    rw [(hspec _ hx).1]
    have hxt : c.coordinate p ∈ T.source := by
      refine ⟨(surfacePhaseChart (c.index : M) c.phase).map_source (c.source hp.1),?_⟩
      change (surfacePhaseChart (c.index : M) c.phase).symm
        ((surfacePhaseChart (c.index : M) c.phase) p) ∈ (surfacePhaseChart q e).source
      rw [(surfacePhaseChart (c.index : M) c.phase).left_inv (c.source hp.1)]
      exact hKs hp.2
    rw [← c.coordinate_transition q e hp.1,T.left_inv hxt]

end PhaseBoundaryCurve
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseTransitionCocycle
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Chain identities for the actual nonlinear phase charts. They transport
both directions of an ordered crossing through a third chart. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4
open SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
lemma surfacePhaseTransition_apply (q r : M)
    (e f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) {p : M}
    (hp : p ∈ (surfacePhaseChart q e).source) :
    surfacePhaseTransition q e r f (surfacePhaseChart q e p) = surfacePhaseChart r f p := by
  change (surfacePhaseChart r f) ((surfacePhaseChart q e).symm (surfacePhaseChart q e p)) = _
  rw [(surfacePhaseChart q e).left_inv hp]

omit [IsManifold planeModel ∞ M] in
lemma surfacePhaseTransition_source (q r : M)
    (e f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) {p : M}
    (hp : p ∈ (surfacePhaseChart q e).source) (hr : p ∈ (surfacePhaseChart r f).source) :
    surfacePhaseChart q e p ∈ (surfacePhaseTransition q e r f).source := by
  refine ⟨(surfacePhaseChart q e).map_source hp,?_⟩
  change (surfacePhaseChart q e).symm (surfacePhaseChart q e p) ∈ (surfacePhaseChart r f).source
  rwa [(surfacePhaseChart q e).left_inv hp]

omit [IsManifold planeModel ∞ M] in
lemma surfacePhaseTransition_cocycle_germ (q₁ q₂ q₃ : M)
    (e₁ e₂ e₃ : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {p : M} (h₁ : p ∈ (surfacePhaseChart q₁ e₁).source)
    (h₂ : p ∈ (surfacePhaseChart q₂ e₂).source)
    (h₃ : p ∈ (surfacePhaseChart q₃ e₃).source) :
    surfacePhaseTransition q₂ e₂ q₃ e₃ ∘ surfacePhaseTransition q₁ e₁ q₂ e₂ =ᶠ[𝓝 (surfacePhaseChart q₁ e₁ p)] surfacePhaseTransition q₁ e₁ q₃ e₃ := by
  have h₁₂ := surfacePhaseTransition_source q₁ q₂ e₁ e₂ h₁ h₂
  have h₁₃ := surfacePhaseTransition_source q₁ q₃ e₁ e₃ h₁ h₃
  filter_upwards [(surfacePhaseTransition q₁ e₁ q₂ e₂).open_source.mem_nhds h₁₂,
    (surfacePhaseTransition q₁ e₁ q₃ e₃).open_source.mem_nhds h₁₃] with x hx _
  have hxs : (surfacePhaseChart q₁ e₁).symm x ∈ (surfacePhaseChart q₂ e₂).source := hx.2
  change (surfacePhaseChart q₃ e₃) ((surfacePhaseChart q₂ e₂).symm
    ((surfacePhaseChart q₂ e₂) ((surfacePhaseChart q₁ e₁).symm x))) = _
  rw [(surfacePhaseChart q₂ e₂).left_inv hxs]
  rfl

omit [IsManifold planeModel ∞ M] in
lemma surfacePhaseTransition_self_germ (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {x : SmallModes.Base} (hx : x ∈ (surfacePhaseChart q e).target) :
    surfacePhaseTransition q e q e =ᶠ[𝓝 x] id := by
  filter_upwards [(surfacePhaseChart q e).open_target.mem_nhds hx] with y hy
  exact (surfacePhaseChart q e).right_inv hy

omit [IsManifold planeModel ∞ M] in
lemma surfacePhaseTransition_self_fderiv (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {x : SmallModes.Base} (hx : x ∈ (surfacePhaseChart q e).target) :
    fderiv ℝ (surfacePhaseTransition q e q e) x = ContinuousLinearMap.id ℝ SmallModes.Base := by
  rw [(surfacePhaseTransition_self_germ q e hx).fderiv_eq,fderiv_id]

lemma surfacePhaseTransition_fderiv_cocycle (q₁ q₂ q₃ : M)
    (e₁ e₂ e₃ : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi₁ : ContDiff ℝ ∞ e₁.symm) (he₂ : ContDiff ℝ ∞ e₂)
    (hi₂ : ContDiff ℝ ∞ e₂.symm) (he₃ : ContDiff ℝ ∞ e₃)
    {p : M} (h₁ : p ∈ (surfacePhaseChart q₁ e₁).source)
    (h₂ : p ∈ (surfacePhaseChart q₂ e₂).source)
    (h₃ : p ∈ (surfacePhaseChart q₃ e₃).source) :
    fderiv ℝ (surfacePhaseTransition q₁ e₁ q₃ e₃) (surfacePhaseChart q₁ e₁ p) =
      (fderiv ℝ (surfacePhaseTransition q₂ e₂ q₃ e₃) (surfacePhaseChart q₂ e₂ p)).comp
        (fderiv ℝ (surfacePhaseTransition q₁ e₁ q₂ e₂) (surfacePhaseChart q₁ e₁ p)) := by
  have h₁₂ := surfacePhaseTransition_source q₁ q₂ e₁ e₂ h₁ h₂
  have h₂₃ := surfacePhaseTransition_source q₂ q₃ e₂ e₃ h₂ h₃
  have hd₁₂ := (((surfacePhaseTransition_smooth q₁ e₁ hi₁ q₂ e₂ he₂)
    (surfacePhaseChart q₁ e₁ p) h₁₂).contDiffAt
      ((surfacePhaseTransition q₁ e₁ q₂ e₂).open_source.mem_nhds h₁₂)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hd₂₃ := (((surfacePhaseTransition_smooth q₂ e₂ hi₂ q₃ e₃ he₃)
    (surfacePhaseChart q₂ e₂ p) h₂₃).contDiffAt
      ((surfacePhaseTransition q₂ e₂ q₃ e₃).open_source.mem_nhds h₂₃)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hg := surfacePhaseTransition_cocycle_germ q₁ q₂ q₃ e₁ e₂ e₃ h₁ h₂ h₃
  rw [← hg.fderiv_eq]
  have ht := surfacePhaseTransition_apply q₁ q₂ e₁ e₂ h₁
  rw [fderiv_comp _ (by rwa [ht]) hd₁₂,ht]

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_RestrictedPhaseTransition
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restricting the phase chart's source leaves its coordinate directions
unchanged on the original chart. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4
open SurfaceJetCoordinates SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma same_phase_transition_fderiv (q r : M) (hqr : q = r)
    (e f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hfe : ∀ x, f x = e x) {p : M} (hp : p ∈ (surfacePhaseChart q e).source) :
    fderiv ℝ (surfacePhaseTransition q e r f) (surfacePhaseChart q e p) =
      ContinuousLinearMap.id ℝ Base := by
  have hfun : (surfacePhaseTransition q e r f : Base → Base) = surfacePhaseTransition q e q e := by
    funext x
    change surfacePhaseChart r f ((surfacePhaseChart q e).symm x) =
      surfacePhaseChart q e ((surfacePhaseChart q e).symm x)
    simp only [surfacePhaseChart_apply,hfe,← hqr]
  rw [hfun]
  exact surfacePhaseTransition_self_fderiv q e ((surfacePhaseChart q e).map_source hp)

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PhaseCurveCrossings
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intrinsic ordered crossing invariants for the fixed later curves.
Their values can be computed in whichever phase chart is being corrected. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes SmallModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace PhaseBoundaryCurve
variable {B : SmoothingAtlas M} (c d : PhaseBoundaryCurve B)

lemma crossing_transition (A : SmoothingAtlas M) (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    {p : M} (hc : p ∈ c.carrier) (hd : p ∈ d.carrier)
    (hp : p ∈ (surfacePhaseChart (i : M) e).source) (hw : A.weight i p ≠ 0) :
    let H := A.phaseRealChartMap i e.symm F
    let vc := fderiv ℝ (surfacePhaseTransition (c.index : M) c.phase (i : M) e) (c.coordinate p) dy
    let vd := fderiv ℝ (surfacePhaseTransition (d.index : M) d.phase (i : M) e) (d.coordinate p) dy
    let q := baseEquiv (e (chart (i : M) p))
    c.crossing d F p = orderedCrossing H vc vd q
      (coordinateGaussianCurvature (realMetric H dx dx) (realMetric H dx dy) (realMetric H dy dy) q) := by
  have hpc : p ∈ (surfacePhaseChart (c.index : M) c.phase).source := c.source hc
  have hpd : p ∈ (surfacePhaseChart (d.index : M) d.phase).source := d.source hd
  have hback : (surfacePhaseChart (c.index : M) c.phase).symm (c.coordinate p) = p :=
    (surfacePhaseChart (c.index : M) c.phase).left_inv hpc
  have hx : c.coordinate p ∈ (surfacePhaseTransition (c.index : M) c.phase (i : M) e).source :=
    surfacePhaseTransition_source _ _ _ _ hpc hp
  let u := fderiv ℝ (surfacePhaseTransition (d.index : M) d.phase (c.index : M) c.phase)
    (d.coordinate p) dy
  have ht := B.phase_intrinsic_crossing_transition A c.index i c.phase e c.smooth c.inverse_smooth
    he hi hF hx (by rw [hback]; exact c.active p hc) (by rwa [hback]) dy u
  have hq : surfacePhaseTransition (c.index : M) c.phase (i : M) e (c.coordinate p) =
      baseEquiv (e (chart (i : M) p)) := surfacePhaseTransition_apply _ _ _ _ hpc
  have hcoc := surfacePhaseTransition_fderiv_cocycle (d.index : M) (c.index : M) (i : M)
    d.phase c.phase e d.inverse_smooth c.smooth c.inverse_smooth he hpd hpc hp
  have hvec : fderiv ℝ (surfacePhaseTransition (c.index : M) c.phase (i : M) e) (c.coordinate p) u =
      fderiv ℝ (surfacePhaseTransition (d.index : M) d.phase (i : M) e) (d.coordinate p) dy := by
    exact (congrArg (fun L : SmallModes.Base →L[ℝ] SmallModes.Base => L dy) hcoc).symm
  dsimp only at ht ⊢
  change c.crossing d F p = _ at ht
  rw [hq,hvec] at ht
  exact ht

end PhaseBoundaryCurve
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_FiniteBoundaryCrossingSets
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact crossing sets for the remaining curves in a finite induction.
The no-three-curves condition keeps these points off the next boundary. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {B : SmoothingAtlas M} {ι : Type*} [Fintype ι]

omit [CompactSpace M] in
lemma boundaryCrossingSet_finite (curves : ι → PhaseBoundaryCurve B) (s : Set ι)
    (hpair : ∀ i j, i ≠ j → ((curves i).carrier ∩ (curves j).carrier).Finite) :
    (boundaryCrossingSet curves s).Finite := by
  classical
  have hU : (⋃ a : {a : ι × ι // a.1 ≠ a.2},
      (curves a.1.1).carrier ∩ (curves a.1.2).carrier).Finite :=
    Set.finite_iUnion (fun a => hpair a.1.1 a.1.2 a.2)
  apply hU.subset
  rintro p ⟨i,_,j,_,hij,hi,hj⟩
  exact mem_iUnion.mpr ⟨⟨(i,j),hij⟩,hi,hj⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FiniteBoundaryStepGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite invariant supplies precisely the old boundary inequalities
and the crossing set disjointness required at the next primitive step. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {B : SmoothingAtlas M} {ι : Type*} [Fintype ι]

omit [CompactSpace M] [Fintype ι] in
/-- At a listed crossing exactly two remaining curves occur. The point
itself indexes the crossing, so no duplicate crossing labels are introduced. -/
lemma boundaryCrossingSet_select (curves : ι → PhaseBoundaryCurve B) (s : Set ι)
    (htriple : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      (curves i).carrier ∩ (curves j).carrier ∩ (curves k).carrier = ∅) :
    ∃ left right : boundaryCrossingSet curves s → ι,
      (∀ p, left p ∈ s ∧ right p ∈ s ∧ left p ≠ right p ∧
        (p : M) ∈ (curves (left p)).carrier ∧ (p : M) ∈ (curves (right p)).carrier) ∧
      ∀ (p : boundaryCrossingSet curves s) j, (p : M) ∈ (curves j).carrier → j = left p ∨ j = right p := by
  classical
  have hex (p : boundaryCrossingSet curves s) :
      ∃ i j, i ∈ s ∧ j ∈ s ∧ i ≠ j ∧
        (p : M) ∈ (curves i).carrier ∧ (p : M) ∈ (curves j).carrier := by
    obtain ⟨i,hi,j,hj,hij,hpi,hpj⟩ := p.2
    exact ⟨i,j,hi,hj,hij,hpi,hpj⟩
  choose left right hchoice using hex
  refine ⟨left,right,hchoice,?_⟩
  intro p j hpj
  by_cases hl : j = left p
  · exact Or.inl hl
  by_cases hr : j = right p
  · exact Or.inr hr
  have hh := hchoice p
  have hx : (p : M) ∈ (curves (left p)).carrier ∩ (curves (right p)).carrier ∩ (curves j).carrier :=
    ⟨⟨hh.2.2.2.1,hh.2.2.2.2⟩,hpj⟩
  rw [htriple (left p) (right p) j hh.2.2.1 (Ne.symm hl) (Ne.symm hr)] at hx
  exact hx.elim

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PreparedPhaseCrossingSlopes
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The generic phase selection makes each relevant transported boundary
direction nonvertical, and a finite crossing set has a fixed slope bound. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {B : SmoothingAtlas M}

lemma finite_crossing_slope_bound {σ : Type*} [Fintype σ]
    (v w : σ → Base) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ j, |(v j).2/(v j).1| ≤ L ∧ |(w j).2/(w j).1| ≤ L := by
  classical
  let L := ∑ j, (|(v j).2/(v j).1| + |(w j).2/(w j).1|)
  have hnon (j : σ) : 0 ≤ |(v j).2/(v j).1| + |(w j).2/(w j).1| :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  refine ⟨L,Finset.sum_nonneg (fun j _ => hnon j),?_⟩
  intro j
  have hj : |(v j).2/(v j).1| + |(w j).2/(w j).1| ≤ L :=
    Finset.single_le_sum (fun k _ => hnon k) (Finset.mem_univ j)
  exact ⟨(le_add_of_nonneg_right (abs_nonneg _)).trans hj,
    (le_add_of_nonneg_left (abs_nonneg _)).trans hj⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitivePatchCurves
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual remaining boundary curves and finite crossing points inside a
constructed primitive patch. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
variable {A B : SmoothingAtlas M} {i : A.centers}
  {e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base}
  {F : M → Space} {amp phi : M → ℝ} {D : Set M}
namespace SupportedPrimitivePatch
variable (d : SupportedPrimitivePatch A i e F amp phi D)

omit [T2Space M] in
lemma coordinate_mem_compact {p : M} (hp : p ∈ closure D) :
    baseEquiv.symm (surfacePhaseChart (i : M) e p) ∈ d.compactSet := by
  change baseEquiv.symm (baseEquiv (e (chart (i : M) p))) ∈ _
  rw [baseEquiv.symm_apply_apply]
  exact d.closed_coordinates p hp

omit [T2Space M] in
lemma coordinate_mem_region {p : M} (hp : p ∈ closure D) :
    surfacePhaseChart (i : M) e p ∈ d.region := by
  apply d.window_region
  refine ⟨baseEquiv.symm (surfacePhaseChart (i : M) e p),?_,baseEquiv.apply_symm_apply _⟩
  exact subset_closure (d.support_window (d.coordinate_mem_compact hp))

lemma curve_compact (c : PhaseBoundaryCurve B) : IsCompact (d.curve c) :=
  c.inPhase_compact (i : M) e isClosed_closure.isCompact d.source_closed

omit [T2Space M] in
lemma curve_region (c : PhaseBoundaryCurve B) : d.curve c ⊆ d.region := by
  rintro x ⟨p,hp,rfl⟩
  exact d.coordinate_mem_region hp.2

omit [T2Space M] in
lemma curve_compact_coordinates (c : PhaseBoundaryCurve B) :
    ∀ x ∈ d.curve c, baseEquiv.symm x ∈ d.compactSet := by
  rintro x ⟨p,hp,rfl⟩
  exact d.coordinate_mem_compact hp.2

theorem curve_coefficients (c : PhaseBoundaryCurve B) :
    ∃ b k : Base → ℝ, ContDiff ℝ ∞ b ∧ ContDiff ℝ ∞ k ∧
      (∀ x ∈ d.curve c, b x ≠ 0 ∨ k x ≠ 0) ∧
      ∀ p ∈ c.carrier ∩ closure D,
        (b (surfacePhaseChart (i : M) e p),k (surfacePhaseChart (i : M) e p)) =
          fderiv ℝ (surfacePhaseTransition (c.index : M) c.phase (i : M) e) (c.coordinate p) dy :=
  c.inPhase_direction_coefficients (i : M) e d.phase_smooth d.inverse_smooth
    isClosed_closure.isCompact d.source_closed

omit [T2Space M] in
lemma innerCrossings_finite {E : Set M} (hE : E.Finite) : (d.innerCrossings E).Finite :=
  (hE.inter_of_left D).image _

omit [T2Space M] in
lemma innerCrossings_positive (E : Set M) : ∀ x ∈ d.innerCrossings E, 0 < d.amplitude x := by
  rintro x ⟨p,hp,rfl⟩
  exact (d.amplitude_positive _).mpr ⟨p,hp.2,rfl⟩

omit [T2Space M] in
lemma innerCrossings_region (E : Set M) : d.innerCrossings E ⊆ d.region := by
  rintro x ⟨p,hp,rfl⟩
  exact d.coordinate_mem_region (subset_closure hp.2)

omit [T2Space M] in
lemma innerCrossings_compact_coordinates (E : Set M) :
    ∀ x ∈ d.innerCrossings E, baseEquiv.symm x ∈ d.compactSet := by
  rintro x ⟨p,hp,rfl⟩
  exact d.coordinate_mem_compact (subset_closure hp.2)

end SupportedPrimitivePatch
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitivePatchBoundary
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer the actual old boundary invariant to the new analytic patch.
The source restriction preserves the current primitive's vertical direction. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
variable {A B : SmoothingAtlas M} {i : A.centers}
  {e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base}
  {F : M → Space} {amp phi : M → ℝ} {D : Set M}
namespace SupportedPrimitivePatch
variable (d : SupportedPrimitivePatch A i e F amp phi D)

omit [T2Space M] in
include d in
lemma current_second (c₀ : PhaseBoundaryCurve B)
    (hi : (i : M) = (c₀.index : M)) (he : ∀ x, e x = c₀.phase x)
    {g : SmoothMetric M} (hF : IsSmoothIsometricImmersion M g F)
    {p : M} (hp : p ∈ c₀.carrier) (hpD : p ∈ closure D) :
    c₀.second F p = realSecondForm (A.phaseRealChartMap i e.symm F) dy dy
      (surfacePhaseChart (i : M) e p) := by
  have hs := c₀.second_transition A i e d.phase_smooth d.inverse_smooth hF hp
    (d.source_closed hpD) (d.active_closed p hpD)
  have ht := same_phase_transition_fderiv (c₀.index : M) (i : M) hi.symm c₀.phase e he (c₀.source hp)
  change fderiv ℝ (surfacePhaseTransition (c₀.index : M) c₀.phase (i : M) e)
    (c₀.coordinate p) = ContinuousLinearMap.id ℝ Base at ht
  dsimp only at hs
  rw [ht,ContinuousLinearMap.id_apply] at hs
  exact hs

omit [T2Space M] in
lemma zero_amplitude_frontier (c : PhaseBoundaryCurve B) (hD : IsOpen D)
    {p : M} (hp : p ∈ c.carrier ∩ closure D)
    (ha : d.amplitude (surfacePhaseChart (i : M) e p) = 0) : p ∈ frontier D := by
  refine ⟨hp.2,?_⟩
  rw [hD.interior_eq]
  intro hpin
  have hpos := (d.amplitude_positive _).mpr ⟨p,hpin,rfl⟩
  rw [ha] at hpos
  exact lt_irrefl _ hpos

omit [T2Space M] in
lemma old_boundary_crossing (c₀ c : PhaseBoundaryCurve B)
    (hi : (i : M) = (c₀.index : M)) (he : ∀ x, e x = c₀.phase x)
    (hD : IsOpen D) (hfront : c₀.carrier = frontier D)
    {g : SmoothMetric M} (hF : IsSmoothIsometricImmersion M g F)
    (b k : Base → ℝ)
    (hv : ∀ p ∈ c.carrier ∩ closure D,
      (b (surfacePhaseChart (i : M) e p),k (surfacePhaseChart (i : M) e p)) =
        fderiv ℝ (surfacePhaseTransition (c.index : M) c.phase (i : M) e) (c.coordinate p) dy)
    (hpositive : ∀ p ∈ c.carrier ∩ frontier D, 0 < c₀.crossing c F p) :
    ∀ x ∈ d.curve c, d.amplitude x = 0 →
      0 < orderedCrossing (A.phaseRealChartMap i e.symm F) dy (b x,k x) x
        (coordinateGaussianCurvature (realMetric (A.phaseRealChartMap i e.symm F) dx dx)
          (realMetric (A.phaseRealChartMap i e.symm F) dx dy)
          (realMetric (A.phaseRealChartMap i e.symm F) dy dy) x) := by
  rintro x ⟨p,hp,rfl⟩ ha
  have hpf := d.zero_amplitude_frontier c hD hp ha
  have hp₀ : p ∈ c₀.carrier := hfront.symm ▸ hpf
  have hcross := c₀.crossing_transition c A i e d.phase_smooth d.inverse_smooth hF hp₀ hp.1
    (d.source_closed hp.2) (d.active_closed p hp.2)
  have ht := same_phase_transition_fderiv (c₀.index : M) (i : M) hi.symm c₀.phase e he (c₀.source hp₀)
  change fderiv ℝ (surfacePhaseTransition (c₀.index : M) c₀.phase (i : M) e)
    (c₀.coordinate p) = ContinuousLinearMap.id ℝ Base at ht
  dsimp only at hcross
  rw [ht,ContinuousLinearMap.id_apply,← hv p hp] at hcross
  have hc := hpositive p ⟨hp.1,hpf⟩
  rw [hcross] at hc
  exact hc

end SupportedPrimitivePatch
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitivePatchBoundaryStep
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed local primitive data feed the exact analytic theorem,
with the global rank-one metric written in the original surface variables. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates SmallModes RealModes PhaseGeometry VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SupportedPrimitivePatch
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.patchStepDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.patchStepFiberSpace
local instance patchStepDualSmul_r47cad9_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {A : SmoothingAtlas M} {i : A.centers}
    {e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base}
    {F : M → Space} {amp phi : M → ℝ} {D : Set M}

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.patchStepFiberNormed
local instance patchStepSectionNormed_r47cad9_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance patchStepSectionSpace_r47cad9_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem boundary_step_oai {B : SmoothingAtlas M} {ι : Type*} [Fintype ι]
    (d : SupportedPrimitivePatch A i e F amp phi D)
    (c₀ : PhaseBoundaryCurve B) (hi : (i : M) = (c₀.index : M))
    (he : ∀ x, e x = c₀.phase x)
    (curves : ι → PhaseBoundaryCurve B)
    (hpair : ∀ j k, j ≠ k → ((curves j).carrier ∩ (curves k).carrier).Finite)
    (htriple : ∀ j k l, j ≠ k → j ≠ l → k ≠ l →
      (curves j).carrier ∩ (curves k).carrier ∩ (curves l).carrier = ∅)
    (hD : IsOpen D) (hDr : interior (closure D) = D) (hfront : c₀.carrier = frontier D)
    (hEf : Disjoint (boundaryCrossingSet curves univ) (frontier D))
    {g : SmoothMetric M} (data : MetricGoodPhaseData g F)
    (hF : IsSmoothIsometricImmersion M g F) (n : PreferredNormal F)
    (hgeom : FiniteBoundaryGeometry curves (boundaryCrossingSet curves univ) F n)
    (hcurrent : ∀ p ∈ c₀.carrier, c₀.second F p ≠ 0 ∧
      spaceCoordinates (n.vector p) ≠ -normalize (c₀.second F p))
    (hfrontGeom : ∀ j p, p ∈ (curves j).carrier ∩ frontier D →
      0 < (curves j).second F p ⬝ᵥ spaceCoordinates (n.vector p) ∧
      0 < c₀.crossing (curves j) F p)
    (hfirst : ∀ j p, p ∈ boundaryCrossingSet curves univ ∩ D → p ∈ (curves j).carrier →
      (fderiv ℝ (surfacePhaseTransition ((curves j).index : M) (curves j).phase
        (i : M) e) ((curves j).coordinate p) dy).1 ≠ 0)
    {P : Set SmallModes.Base} (hP : P.Finite)
    (hlocal : ∀ p ∈ (⋃ j, d.curve (curves j)) \ P,
      ∃ N : Set SmallModes.Base, IsOpen N ∧ p ∈ N ∧ ∃ f : SmallModes.Base → ℝ, ContDiffOn ℝ ∞ f N ∧
        (∀ x ∈ (⋃ j, d.curve (curves j)) ∩ N, f x = 0) ∧ fderiv ℝ f p dy ≠ 0)
    (h : SmoothMetric M)
    (htarget : h.inner = g.inner + (fun p => (amp p)^2 • SmoothingAtlas.phaseDifferentialSquare phi p)) :
    ∃ W : M → Space, IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
      ∃ N : PreferredNormal W, FiniteBoundaryGeometry curves (boundaryCrossingSet curves univ) W N := by
  classical
  let E₀ := boundaryCrossingSet curves (univ : Set ι)
  have hE₀ : E₀.Finite := boundaryCrossingSet_finite curves univ hpair
  let σ := E₀ ∩ D
  let : Fintype σ := (hE₀.inter_of_left D).fintype
  obtain ⟨l,r,hlr,honly⟩ := boundaryCrossingSet_select curves univ htriple
  let left : σ → ι := fun p => l ⟨p,p.2.1⟩
  let right : σ → ι := fun p => r ⟨p,p.2.1⟩
  let x : σ → SmallModes.Base := fun p => surfacePhaseChart (i : M) e p
  choose b k hb hk hbk hv using fun j => d.curve_coefficients (curves j)
  have hsource (p : σ) : (p : M) ∈ (surfacePhaseChart (i : M) e).source :=
    d.source_closed (subset_closure p.2.2)
  have hxback (p : σ) : (surfacePhaseChart (i : M) e).symm (x p) = p :=
    (surfacePhaseChart (i : M) e).left_inv (hsource p)
  have hxinj : Function.Injective x := by
    intro p q hpq
    apply Subtype.ext
    have hh := congrArg (surfacePhaseChart (i : M) e).symm hpq
    simpa only [hxback] using hh
  have hxE (p : σ) : x p ∈ d.innerCrossings E₀ := ⟨p,p.2,rfl⟩
  have hxl (p : σ) : (p : M) ∈ (curves (left p)).carrier := (hlr ⟨p,p.2.1⟩).2.2.2.1
  have hxr (p : σ) : (p : M) ∈ (curves (right p)).carrier := (hlr ⟨p,p.2.1⟩).2.2.2.2
  have hfirst' (p : σ) : b (left p) (x p) ≠ 0 ∧ b (right p) (x p) ≠ 0 := by
    have hf (j : ι) (hp : (p : M) ∈ (curves j).carrier) : b j (x p) ≠ 0 := by
      have hh := congrArg Prod.fst (hv j p ⟨hp,subset_closure p.2.2⟩)
      change b j (x p) = _ at hh
      rw [hh]
      exact hfirst j p p.2 hp
    exact ⟨hf _ (hxl p),hf _ (hxr p)⟩
  obtain ⟨L,hL,hslopes⟩ := finite_crossing_slope_bound
    (fun p : σ => (b (left p) (x p),k (left p) (x p)))
    (fun p : σ => (b (right p) (x p),k (right p) (x p)))
  have hmetric : g.inner = inducedTensor F := by
    funext p
    ext v w
    exact (hF.2 p v w).symm
  have htarget' : h.inner = g.inner + A.bundleRestore A.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e d.cutoff
        (fun q => ![(d.amplitude (baseEquiv q))^2,0,0]) y)) := by
    rw [d.tensor]
    exact htarget
  have hCS : d.compactSet ⊆ (d.window : Set JetPolynomial.Base) ∩ e.target :=
    fun _ hx => ⟨d.support_window hx,d.target hx⟩
  let ell : JetPolynomial.Base →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have hell₀ : ell (coordinateVector 0) = 1 := by simp [ell,coordinateVector]
  have hell₁ : ell (coordinateVector 1) = 0 := by simp [ell,coordinateVector]
  have hworld : ∀ p ∈ frontier D,
      realSecondForm (A.phaseRealChartMap i e.symm F) dy dy (surfacePhaseChart (i : M) e p) ≠ 0 ∧
      spaceCoordinates (n.vector p) ≠ -normalize
        (realSecondForm (A.phaseRealChartMap i e.symm F) dy dy (surfacePhaseChart (i : M) e p)) := by
    intro p hp
    have hpc : p ∈ c₀.carrier := hfront.symm ▸ hp
    rw [← d.current_second c₀ hi he hF hpc hp.1]
    exact hcurrent p hpc
  have honly' : ∀ p j, x p ∈ d.curve (curves j) → j = left p ∨ j = right p := by
    intro p j hp
    obtain ⟨q,hq,hqp⟩ := hp
    have heq : q = (p : M) := (surfacePhaseChart (i : M) e).injOn
      (d.source_closed hq.2) (hsource p) hqp
    subst q
    exact honly ⟨p,p.2.1⟩ j hq.1
  have hafront : ∀ p ∈ frontier D, d.amplitude (surfacePhaseChart (i : M) e p) = 0 := by
    intro p hp
    have hz : ¬ 0 < d.amplitude (surfacePhaseChart (i : M) e p) := by
      rw [d.amplitude_positive]
      rintro ⟨q,hq,heq⟩
      have hqp := (surfacePhaseChart (i : M) e).injOn
        (d.source_closed (subset_closure hq)) (d.source_closed hp.1) heq
      subst q
      exact hp.2 (hD.interior_eq.symm ▸ hq)
    exact le_antisymm (le_of_not_gt hz) (d.amplitude_nonneg _)
  have hvfront : ∀ p ∈ frontier D, surfacePhaseChart (i : M) e p ∉ (surfacePhaseChart (i : M) e) '' D := by
    intro p hp hpin
    obtain ⟨q,hq,heq⟩ := hpin
    have hqp := (surfacePhaseChart (i : M) e).injOn
      (d.source_closed (subset_closure hq)) (d.source_closed hp.1) heq
    subst q
    exact hp.2 (hD.interior_eq.symm ▸ hq)
  obtain ⟨W,hW,hgood,N,havoid,hcross⟩ :=
    data.independent_circular_primitive_boundary_step A d.outer hF.1 hmetric i e
      d.phase_smooth d.inverse_smooth d.cutoff_smooth d.cutoff_compact d.cutoff_source d.cover
      d.amplitude_smooth d.region_compact d.open_region d.region_open d.normal_smooth
      d.immersion d.normal_properties d.convexity d.amplitude_nonneg d.boundary
      (fun j => d.curve_compact (curves j)) (fun j => d.curve_region (curves j)) hP hlocal
      (d.innerCrossings_finite hE₀) (d.innerCrossings_region E₀) (d.innerCrossings_positive E₀)
      L hL hb hk hbk d.window d.window_compact d.phase_window d.window_region
      d.compactSet d.compact d.support_window d.inverse_support d.cutoff_one d.amplitude_off
      ell hell₀ hell₁ h htarget' d.compact hCS
      (fun j => d.curve_compact_coordinates (curves j)) d.compact_active
      (d.innerCrossings_compact_coordinates E₀)
      (fun j => d.old_boundary_crossing c₀ (curves j) hi he hD hfront hF (b j) (k j)
        (hv j) (fun p hp => (hfrontGeom j p hp).2))
      left right x hxinj hxE (V := (surfacePhaseChart (i : M) e) '' D)
      ((surfacePhaseChart (i : M) e).isOpen_image_of_subset_source hD
        (fun p hp => d.source_closed (subset_closure hp)))
      (fun p => ⟨p,p.2.2,rfl⟩) honly' hfirst' hslopes B curves n
      (fun j p hp => ⟨hgeom.nonzero j p hp,hgeom.avoids j p hp⟩)
      hD hDr (fun p hp => (d.source_closed hp).1) (fun p hp => (d.source_closed hp).2)
      d.active_closed E₀ hE₀ hEf d.support d.closed_coordinates
      (fun j p hp hpD => ⟨p,⟨hp,hpD⟩,rfl⟩)
      (fun j p hp hpD => hv j p ⟨hp,hpD⟩) hworld
      hafront (fun j p hp hpD => (hfrontGeom j p ⟨hp,hpD⟩).1) hvfront
      (fun p => by rw [hxback]; exact p.2)
      (fun p hp hpD => ⟨⟨p,hp,hpD⟩,hxback ⟨p,hp,hpD⟩⟩)
      (fun j k hjk p hp hj hk =>
        ⟨⟨hgeom.positive j k hjk p hp hj hk,hgeom.positive k j hjk.symm p hp hk hj⟩,
          hgeom.crossing j k hjk p hp hj hk,hgeom.crossing k j hjk.symm p hp hk hj⟩)
  exact ⟨W,hW,hgood,N,{
      nonzero := fun j p hp => (havoid j p hp).1
      avoids := fun j p hp => (havoid j p hp).2
      positive := fun j k hjk p hp hj hk => (hcross j k hjk p hp hj hk).1.1
      crossing := fun j k hjk p hp hj hk => (hcross j k hjk p hp hj hk).2.1 }⟩

end SupportedPrimitivePatch
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SupportedPrimitivePatch.boundary_step_oai.{u_1, u_2} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SupportedPrimitivePatch.boundary_step_oai.{u_1, u_2}
