-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.nonempty
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:38:04.277277+00:00
-- url     : https://prove2.me/submissions/f65c9381-9a1f-40e8-b184-f50682edfd61

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI011
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_exists_metric_good_smoothingAtlas

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GoodDirections
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes
open Set Polynomial



lemma secondQuadratic_smul {n : ℕ} (B : Fin 3 → RVec n) (v : Base) (w : ℝ) :
    secondQuadratic B (w • v) = w ^ 2 • secondQuadratic B v := by
  ext i
  simp only [secondQuadratic, Prod.smul_fst, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring



end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_GoodPhases
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.PhaseMean Set

lemma good_neg {n : ℕ} {B : Fin 3 → RVec n} {ξ : Base} (h : Good B ξ) : Good B (-ξ) := by
  constructor
  · exact neg_ne_zero.mpr h.1
  · have he : (-(-ξ).2, (-ξ).1) = (-1 : ℝ) • (-ξ.2, ξ.1) := by ext <;> simp
    rw [he, secondQuadratic_smul]
    simpa using h.2



end ClosedSurfaceR4.PhaseGeometry

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.PhaseMean Set

lemma continuous_secondQuadratic {n : ℕ} :
    Continuous (fun z : (Fin 3 → RVec n) × Base => secondQuadratic z.1 z.2) := by
  unfold secondQuadratic
  fun_prop

lemma isOpen_good {X : Type*} [TopologicalSpace X] {n : ℕ}
    {B : X → Fin 3 → RVec n} {ξ : X → Base} (hB : Continuous B) (hξ : Continuous ξ) :
    IsOpen {p : X | Good (B p) (ξ p)} := by
  change IsOpen ({p : X | ξ p ≠ 0} ∩
    {p : X | secondQuadratic (B p) (-(ξ p).2, (ξ p).1) ≠ 0})
  apply (isOpen_ne_fun hξ continuous_const).inter
  apply isOpen_ne_fun _ continuous_const
  exact continuous_secondQuadratic.comp (hB.prodMk ((hξ.snd.neg).prodMk hξ.fst))



end ClosedSurfaceR4.PhaseGeometry

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
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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

lemma second_coordDeriv_quadratic {n : ℕ} {F : RField n} (hF : ContDiff ℝ ∞ F)
    (v p : Base) : coordDeriv v (coordDeriv v F) p =
      (v.1^2) • coordDeriv dx (coordDeriv dx F) p +
      (2*v.1*v.2) • coordDeriv dx (coordDeriv dy F) p +
      (v.2^2) • coordDeriv dy (coordDeriv dy F) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
  have hsym := real_second_coordDeriv_comm hF p dy dx
  simp only [real_second_coordDeriv hd] at hsym ⊢
  conv_lhs => arg 2; rw [base_eq_basis v]
  conv_lhs => arg 1; arg 2; rw [base_eq_basis v]
  simp only [map_add, map_smul, add_apply, smul_apply,
    hsym]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma realSecondForm_quadratic {F : RField 4} (hF : ContDiff ℝ ∞ F) (v p : Base) :
    realSecondForm F v v p = secondQuadratic (realSecondTensor F p) v := by
  unfold realSecondForm
  rw [second_coordDeriv_quadratic hF]
  have hlin := realNormalPart_linear (coordDeriv dx F p) (coordDeriv dy F p)
  rw [hlin.map_add, hlin.map_add, hlin.map_smul, hlin.map_smul, hlin.map_smul]
  simp [secondQuadratic, realSecondTensor, realSecondForm]

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
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
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

lemma rotated_pullCovector (A : Base →L[ℝ] Base) (ξ : Base) :
    A (-(pullCovector A ξ).2,(pullCovector A ξ).1) = coordDet A • (-ξ.2,ξ.1) := by
  rw [linear_apply_basis]
  ext <;> simp [pullCovector,coordDet,Prod.smul_mk] <;> ring

lemma phase_length_comp_smooth {F : RField 4} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (ξ p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : coordDet (fderiv ℝ φ p) ≠ 0) :
    secondQuadratic (realSecondTensor (F ∘ φ) p)
      (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1) =
      (coordDet (fderiv ℝ φ p))^2 •
        secondQuadratic (realSecondTensor F (φ p)) (-ξ.2,ξ.1) := by
  rw [← realSecondForm_quadratic (hF.comp hφ),realSecondForm_comp_smooth hF hφ _ _ _ hD hdet,
    rotated_pullCovector,realSecondForm_quadratic hF,secondQuadratic_smul]

lemma norm_phase_length_comp_smooth {F : RField 4} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (ξ p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : coordDet (fderiv ℝ φ p) ≠ 0) :
    ‖secondQuadratic (realSecondTensor (F ∘ φ) p)
      (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1)‖ =
      (coordDet (fderiv ℝ φ p))^2 *
        ‖secondQuadratic (realSecondTensor F (φ p)) (-ξ.2,ξ.1)‖ := by
  rw [phase_length_comp_smooth hF hφ ξ p hD hdet,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]

lemma norm_realSecondForm_le {F : RField 4} (hF : ContDiff ℝ ∞ F) (v w p : Base) :
    ‖realSecondForm F v w p‖ ≤ 4*‖realSecondTensor F p‖*‖v‖*‖w‖ := by
  have h11 : |v.1*w.1| ≤ ‖v‖*‖w‖ := by
    rw [abs_mul]
    exact mul_le_mul (by simpa using norm_fst_le v) (by simpa using norm_fst_le w)
      (abs_nonneg _) (norm_nonneg _)
  have h22 : |v.2*w.2| ≤ ‖v‖*‖w‖ := by
    rw [abs_mul]
    exact mul_le_mul (by simpa using norm_snd_le v) (by simpa using norm_snd_le w)
      (abs_nonneg _) (norm_nonneg _)
  have h12 : |v.1*w.2+v.2*w.1| ≤ 2*‖v‖*‖w‖ := by
    have ha : |v.1*w.2| ≤ ‖v‖*‖w‖ := by
      rw [abs_mul]
      exact mul_le_mul (by simpa using norm_fst_le v) (by simpa using norm_snd_le w)
        (abs_nonneg _) (norm_nonneg _)
    have hb : |v.2*w.1| ≤ ‖v‖*‖w‖ := by
      rw [abs_mul]
      exact mul_le_mul (by simpa using norm_snd_le v) (by simpa using norm_fst_le w)
        (abs_nonneg _) (norm_nonneg _)
    linarith [abs_add_le (v.1*w.2) (v.2*w.1)]
  rw [realSecondForm_bilinear hF]
  calc
    _ ≤ (‖(v.1*w.1) • realSecondTensor F p 0‖+
        ‖(v.1*w.2+v.2*w.1) • realSecondTensor F p 1‖)+
        ‖(v.2*w.2) • realSecondTensor F p 2‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (‖v‖*‖w‖*‖realSecondTensor F p‖+
        (2*‖v‖*‖w‖)*‖realSecondTensor F p‖)+‖v‖*‖w‖*‖realSecondTensor F p‖ := by
      simp only [norm_smul,Real.norm_eq_abs]
      gcongr
      · exact norm_le_pi_norm _ 0
      · exact norm_le_pi_norm _ 1
      · exact norm_le_pi_norm _ 2
    _ = _ := by ring

lemma norm_realSecondTensor_comp_smooth {F : RField 4} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : coordDet (fderiv ℝ φ p) ≠ 0) :
    ‖realSecondTensor (F ∘ φ) p‖ ≤
      4*‖realSecondTensor F (φ p)‖*‖fderiv ℝ φ p‖^2 := by
  have hbound (v : Base) (hv : ‖v‖ = 1) : ‖fderiv ℝ φ p v‖ ≤ ‖fderiv ℝ φ p‖ := by
    simpa only [hv,mul_one] using (fderiv ℝ φ p).le_opNorm v
  have hx : ‖dx‖ = 1 := by simp [dx,Prod.norm_def]
  have hy : ‖dy‖ = 1 := by simp [dy,Prod.norm_def]
  have hb (v w : Base) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
      ‖realSecondForm (F ∘ φ) v w p‖ ≤ 4*‖realSecondTensor F (φ p)‖*‖fderiv ℝ φ p‖^2 := by
    rw [realSecondForm_comp_smooth hF hφ _ _ _ hD hdet]
    calc
      _ ≤ 4*‖realSecondTensor F (φ p)‖*‖fderiv ℝ φ p v‖*‖fderiv ℝ φ p w‖ :=
        norm_realSecondForm_le hF _ _ _
      _ ≤ 4*‖realSecondTensor F (φ p)‖*‖fderiv ℝ φ p‖*‖fderiv ℝ φ p‖ := by
        gcongr
        · exact hbound v hv
        · exact hbound w hw
      _ = _ := by ring
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i
  · exact hb dx dx hx hx
  · exact hb dx dy hx hy
  · exact hb dy dy hy hy

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_JacobianBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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

lemma continuous_coordDet : Continuous coordDet := by
  unfold coordDet
  fun_prop

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



theorem compact_chart_jacobian_bounds {φ ψ : Base → Base} {U V K : Set Base}
    (hU : IsOpen U) (hV : IsOpen V) (hφ : ContDiffOn ℝ ∞ φ U)
    (hψ : ContDiffOn ℝ ∞ ψ V) (hmap : MapsTo φ U V)
    (hinv : EqOn (ψ ∘ φ) id U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ d C : ℝ, 0 < d ∧ 0 < C ∧
      ∀ p ∈ K, d ≤ |coordDet (fderiv ℝ φ p)| ∧ ‖fderiv ℝ φ p‖ ≤ C := by
  have hD : ContinuousOn (fderiv ℝ φ) K :=
    (hφ.continuousOn_fderiv_of_isOpen hU (by simp)).mono hKU
  have hd : ContinuousOn (fun p => |coordDet (fderiv ℝ φ p)|) K :=
    (continuous_coordDet.comp_continuousOn hD).abs
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hD
  by_cases hn : K.Nonempty
  · obtain ⟨p,hp,hm⟩ := hK.exists_isMinOn hn hd
    refine ⟨|coordDet (fderiv ℝ φ p)|,|C|+1,abs_pos.mpr ?_,by positivity,?_⟩
    · exact coordDet_fderiv_ne_zero_of_local_inverse hU hV hφ hψ hmap hinv (hKU hp)
    · intro q hq
      exact ⟨hm hq,(hC q hq).trans (by linarith [le_abs_self C])⟩
  · exact ⟨1,1,zero_lt_one,zero_lt_one,fun p hp => False.elim (hn ⟨p,hp⟩)⟩

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ChartModel
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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

lemma coordinateMap_smoothOn [IsManifold planeModel ∞ M] {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (p : M) :
    ContDiffOn ℝ ∞ (coordinateMap F p) (coordinateDomain p) := by
  apply ContMDiffOn.contDiffOn
  have hChart := contMDiffOn_extChartAt_symm (I := planeModel) (n := (∞ : ℕ∞ω)) p
  have h1 := hF.comp_contMDiffOn hChart
  have h2 := spaceCoordinates.contDiff.contMDiff.comp_contMDiffOn h1
  exact h2.comp planeCoordinates.symm.contDiff.contMDiff.contMDiffOn
    (fun x hx => hx)

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ImmersionJets
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes



lemma gramDet_ne_zero_of_injective (A : Base →L[ℝ] RVec 4) (hA : Function.Injective A) :
    NormalFrame.gramDet (A dx) (A dy) ≠ 0 := by
  let X := A dx
  let Y := A dy
  have hX : X ≠ 0 := by
    intro hx
    have he : dx = 0 := hA (by simpa [X] using hx)
    exact one_ne_zero (congrArg Prod.fst he)
  have hXX : X ⬝ᵥ X ≠ 0 := (dotProduct_self_eq_zero).not.mpr hX
  intro hD
  let v : Base := -(X ⬝ᵥ Y) • dx + (X ⬝ᵥ X) • dy
  have hv : A v = -(X ⬝ᵥ Y) • X + (X ⬝ᵥ X) • Y := by simp [v,X,Y]
  have hsq : A v ⬝ᵥ A v = (X ⬝ᵥ X) * NormalFrame.gramDet X Y := by
    rw [hv]
    simp only [NormalFrame.gramDet, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, dotProduct_comm Y X]
    ring
  have hz : A v = 0 := dotProduct_self_eq_zero.mp (by rw [hsq]; change _ * NormalFrame.gramDet (A dx) (A dy) = 0; rw [hD,mul_zero])
  have hv0 : v = 0 := hA (by simpa using hz)
  have hy0 := congrArg Prod.snd hv0
  exact hXX (by simpa [v,dx,dy] using hy0)

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseGeometry Set Filter

lemma contDiffAt_realSecondTensor {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : Base)
    (hD : NormalFrame.gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0) :
    ContDiffAt ℝ ∞ (realSecondTensor F) p := by
  have hx := (contDiff_real_coordDeriv hF dx).contDiffAt (x := p)
  have hy := (contDiff_real_coordDeriv hF dy).contDiffAt (x := p)
  have hb (v w : Base) : ContDiffAt ℝ ∞ (fun q => realSecondForm F v w q) p :=
    contDiffAt_realNormalPart hx hy
      (contDiff_real_coordDeriv (contDiff_real_coordDeriv hF w) v).contDiffAt hD
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact hb dx dx
  · exact hb dx dy
  · exact hb dy dy

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_LocalPhaseData
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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

lemma realSecondTensor_eventuallyEq {F G : RField 4} {p : Base}
    (h : F =ᶠ[𝓝 p] G) : realSecondTensor F =ᶠ[𝓝 p] realSecondTensor G := by
  filter_upwards [realSecondForm_eventuallyEq h dx dx, realSecondForm_eventuallyEq h dx dy,
    realSecondForm_eventuallyEq h dy dy] with q hxx hxy hyy
  ext i
  fin_cases i <;> simp [realSecondTensor, hxx, hxy, hyy]




end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ChartTransition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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

lemma coordinateTransition_smoothOn (q p : M) :
    ContDiffOn ℝ ∞ (coordinateTransition q p) (coordinateTransition q p).source := by
  apply ContMDiffOn.contDiffOn
  exact (coordinateChart_smoothOn q).comp
    ((coordinateChart_symm_smoothOn p).mono (fun x hx => hx.1)) (fun x hx => hx.2)

omit [IsManifold planeModel ∞ M] in
lemma coordinateTransition_symm (q p : M) :
    (coordinateTransition q p).symm = coordinateTransition p q := by
  simp [coordinateTransition,OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]

lemma coordinateTransition_symm_smoothOn (q p : M) :
    ContDiffOn ℝ ∞ (coordinateTransition q p).symm (coordinateTransition q p).target := by
  have h := coordinateTransition_smoothOn p q
  rw [← coordinateTransition_symm q p] at h
  exact h



theorem coordinateTransition_compact_bounds (q p : M) {K : Set SmallModes.Base}
    (hK : IsCompact K) (hKs : K ⊆ (coordinateTransition q p).source) :
    ∃ d C : ℝ, 0 < d ∧ 0 < C ∧
      ∀ x ∈ K, d ≤ |coordDet (fderiv ℝ (coordinateTransition q p) x)| ∧
        ‖fderiv ℝ (coordinateTransition q p) x‖ ≤ C := by
  let e := coordinateTransition q p
  exact compact_chart_jacobian_bounds e.open_source e.open_target
    (coordinateTransition_smoothOn q p) (coordinateTransition_symm_smoothOn q p)
    e.mapsTo (fun x hx => e.left_inv hx) hK hKs

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PhaseWeights
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.PhaseMean Set

lemma good_smul {n : ℕ} {B : Fin 3 → RVec n} {ξ : Base} {w : ℝ}
    (hw : w ≠ 0) (h : Good B ξ) : Good B (w • ξ) := by
  constructor
  · exact smul_ne_zero hw h.1
  · have he : (-(w • ξ).2, (w • ξ).1) = w • (-ξ.2, ξ.1) := by ext <;> simp
    rw [he, secondQuadratic_smul]
    exact smul_ne_zero (pow_ne_zero 2 hw) h.2



theorem uniform_good_perturbation {X : Type*} [TopologicalSpace X] {n : ℕ}
    {K : Set X} (hK : IsCompact K) {B : X → Fin 3 → RVec n} {ξ υ : X → Base}
    (hB : Continuous B) (hξ : Continuous ξ) (hυ : Continuous υ)
    (hgood : ∀ p ∈ K, Good (B p) (ξ p)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → ∀ p ∈ K, Good (B p) (ξ p + t • υ p) := by
  let U : Set (X × ℝ) := {z | Good (B z.1) (ξ z.1 + z.2 • υ z.1)}
  have hU : IsOpen U := isOpen_good (hB.comp continuous_fst)
    ((hξ.comp continuous_fst).add (continuous_snd.smul (hυ.comp continuous_fst)))
  have hKU : K ×ˢ ({0} : Set ℝ) ⊆ U := by
    rintro ⟨p, t⟩ ⟨hp, ht⟩
    simp only [mem_singleton_iff] at ht
    subst t
    simpa [U] using hgood p hp
  obtain ⟨V, W, hV, hW, hKV, h0W, hprod⟩ :=
    generalized_tube_lemma hK isCompact_singleton hU hKU
  obtain ⟨ε, hε, heW⟩ := Metric.isOpen_iff.mp hW 0 (h0W (by simp))
  refine ⟨ε, hε, fun t ht p hp => ?_⟩
  change (p, t) ∈ U
  apply hprod ⟨hKV hp, heW ?_⟩
  simpa [Metric.mem_ball, Real.dist_eq] using ht




theorem exists_dominant_weight {ι : Type*} [Fintype ι]
    {X : ι → Type*} [∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)]
    {n : ℕ} (B : ∀ i, X i → Fin 3 → RVec n) (ξ υ : ∀ i, X i → Base)
    (hB : ∀ i, Continuous (B i)) (hξ : ∀ i, Continuous (ξ i))
    (hυ : ∀ i, Continuous (υ i)) (hgood : ∀ i p, Good (B i p) (ξ i p))
    (c : ι → ℝ) :
    ∃ w : ℝ, 0 < w ∧ ∀ i p,
      Good (B i p) (w • ξ i p + c i • υ i p) ∧
      Good (B i p) (w • ξ i p - c i • υ i p) := by
  classical
  have hsmall : ∀ i, ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → ∀ p,
      Good (B i p) (ξ i p + t • υ i p) := by
    intro i
    obtain ⟨ε, hε, ht⟩ := uniform_good_perturbation (K := univ) isCompact_univ
      (hB i) (hξ i) (hυ i) (fun p _ => hgood i p)
    exact ⟨ε, hε, fun t htp p => ht t htp p (mem_univ p)⟩
  choose ε hε hsmall using hsmall
  let w := 1 + ∑ i, |c i| / ε i
  have hw : 0 < w := by
    dsimp [w]
    exact add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun i _ => div_nonneg (abs_nonneg _) (hε i).le)
  have hc : ∀ i, |c i / w| < ε i := by
    intro i
    have hsum := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset ι)) =>
      div_nonneg (abs_nonneg (c j)) (hε j).le) (Finset.mem_univ i)
    have hb : |c i| / ε i < w := by dsimp [w]; linarith
    rw [abs_div, abs_of_pos hw, div_lt_iff₀ hw]
    have ht := (div_lt_iff₀ (hε i)).mp hb
    nlinarith
  refine ⟨w, hw, fun i p => ⟨?_, ?_⟩⟩
  · have hg := good_smul hw.ne' (hsmall i (c i / w) (hc i) p)
    convert hg using 1
    all_goals try with_reducible_and_instances rfl
    rw [smul_add, smul_smul, mul_div_cancel₀ _ hw.ne']
  · have hg := good_smul hw.ne' (hsmall i (-(c i / w)) (by simpa using hc i) p)
    convert hg using 1
    all_goals try with_reducible_and_instances rfl
    rw [smul_add, smul_smul]
    simp only [mul_neg, mul_div_cancel₀ _ hw.ne', neg_smul, sub_eq_add_neg]

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_LengthMargins
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma good_of_direction_length_pos {n : ℕ} (B : Fin 3 → RVec n) (ξ : Base)
    (h : 0 < ‖secondQuadratic B (-ξ.2,ξ.1)‖) : Good B ξ := by
  refine ⟨?_, norm_pos_iff.mp h⟩
  intro hξ
  simp [hξ,secondQuadratic] at h





end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_CoordinateMargins
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
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

lemma norm_pullCovector_le (A : Base →L[ℝ] Base) (ξ : Base) :
    ‖pullCovector A ξ‖ ≤ 2*‖A‖*‖ξ‖ := by
  have hd : ‖dx‖ = 1 := by simp [dx,Prod.norm_def]
  have he : ‖dy‖ = 1 := by simp [dy,Prod.norm_def]
  have bound (v : Base) (hv : ‖v‖ = 1) : |ξ.1*(A v).1+ξ.2*(A v).2| ≤ 2*‖A‖*‖ξ‖ := by
    have hA : ‖A v‖ ≤ ‖A‖ := by simpa only [hv,mul_one] using A.le_opNorm v
    have h1 : |ξ.1*(A v).1| ≤ ‖ξ‖*‖A‖ := by
      rw [abs_mul]
      exact mul_le_mul (by simpa using norm_fst_le ξ)
        ((show |(A v).1| ≤ ‖A v‖ by simpa using norm_fst_le (A v)).trans hA) (abs_nonneg _) (norm_nonneg _)
    have h2 : |ξ.2*(A v).2| ≤ ‖ξ‖*‖A‖ := by
      rw [abs_mul]
      exact mul_le_mul (by simpa using norm_snd_le ξ)
        ((show |(A v).2| ≤ ‖A v‖ by simpa using norm_snd_le (A v)).trans hA) (abs_nonneg _) (norm_nonneg _)
    linarith [abs_add_le (ξ.1*(A v).1) (ξ.2*(A v).2)]
  change max ‖ξ.1*(A dx).1+ξ.2*(A dx).2‖ ‖ξ.1*(A dy).1+ξ.2*(A dy).2‖ ≤ _
  simpa only [Real.norm_eq_abs,max_le_iff] using And.intro (bound dx hd) (bound dy he)




theorem quantitative_chart_phase_margin {F : RField 4} {φ : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (ξ p : Base)
    {d C ε : ℝ} (hd : 0 < d) (hC : 0 < C) (hε : 0 < ε)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : d ≤ |coordDet (fderiv ℝ φ p)|) (hA : ‖fderiv ℝ φ p‖ ≤ C)
    (hB : realSecondTensor F (φ p) ≠ 0)
    (hmargin : ε*‖realSecondTensor F (φ p)‖ ≤
      ‖secondQuadratic (realSecondTensor F (φ p)) (-ξ.2,ξ.1)‖) :
    ‖pullCovector (fderiv ℝ φ p) ξ‖ ≤ 2*C*‖ξ‖ ∧
    d^2*ε/(4*C ^ 2)*‖realSecondTensor (F ∘ φ) p‖ ≤
      ‖secondQuadratic (realSecondTensor (F ∘ φ) p)
        (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1)‖ ∧
    Good (realSecondTensor (F ∘ φ) p) (pullCovector (fderiv ℝ φ p) ξ) ∧
    realSecondTensor (F ∘ φ) p ≠ 0 := by
  have hdet0 : coordDet (fderiv ℝ φ p) ≠ 0 := abs_pos.mp (hd.trans_le hdet)
  have hsq : d^2 ≤ (coordDet (fderiv ℝ φ p))^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ hd.le hdet 2
  have hbc : ‖realSecondTensor (F ∘ φ) p‖ ≤ 4*‖realSecondTensor F (φ p)‖*C ^ 2 := by
    apply (norm_realSecondTensor_comp_smooth hF hφ p hD hdet0).trans
    gcongr
  have hlength := norm_phase_length_comp_smooth hF hφ ξ p hD hdet0
  have hbound : d^2*ε/(4*C ^ 2)*‖realSecondTensor (F ∘ φ) p‖ ≤
      ‖secondQuadratic (realSecondTensor (F ∘ φ) p)
        (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1)‖ := by
    rw [hlength]
    calc
      _ ≤ d^2*ε/(4*C ^ 2)*(4*‖realSecondTensor F (φ p)‖*C ^ 2) := by gcongr
      _ = d^2*(ε*‖realSecondTensor F (φ p)‖) := by field_simp
      _ ≤ d^2*‖secondQuadratic (realSecondTensor F (φ p)) (-ξ.2,ξ.1)‖ := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_right hsq (norm_nonneg _)
  have hpos : 0 < ‖secondQuadratic (realSecondTensor (F ∘ φ) p)
        (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1)‖ := by
    rw [hlength]
    exact mul_pos (sq_pos_of_ne_zero hdet0) ((mul_pos hε (norm_pos_iff.mpr hB)).trans_le hmargin)
  refine ⟨(norm_pullCovector_le _ _).trans ?_,hbound,good_of_direction_length_pos _ _ hpos,?_⟩
  · gcongr
  · intro hz
    simp only [hz,secondQuadratic,Pi.zero_apply,smul_zero,add_zero,norm_zero] at hpos
    exact lt_irrefl 0 hpos

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry Set Filter




theorem quantitative_chart_phase_margin_on {F : RField 4} {φ : Base → Base}
    {U V : Set Base} (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℝ ∞ F V) (hφ : ContDiffOn ℝ ∞ φ U)
    {p : Base} (hp : p ∈ U) (hφp : φ p ∈ V) (ξ : Base)
    {d C ε : ℝ} (hd : 0 < d) (hC : 0 < C) (hε : 0 < ε)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : d ≤ |coordDet (fderiv ℝ φ p)|) (hA : ‖fderiv ℝ φ p‖ ≤ C)
    (hB : realSecondTensor F (φ p) ≠ 0)
    (hmargin : ε*‖realSecondTensor F (φ p)‖ ≤
      ‖secondQuadratic (realSecondTensor F (φ p)) (-ξ.2,ξ.1)‖) :
    ‖pullCovector (fderiv ℝ φ p) ξ‖ ≤ 2*C*‖ξ‖ ∧
    d^2*ε/(4*C ^ 2)*‖realSecondTensor (F ∘ φ) p‖ ≤
      ‖secondQuadratic (realSecondTensor (F ∘ φ) p)
        (-(pullCovector (fderiv ℝ φ p) ξ).2,(pullCovector (fderiv ℝ φ p) ξ).1)‖ ∧
    Good (realSecondTensor (F ∘ φ) p) (pullCovector (fderiv ℝ φ p) ξ) ∧
    realSecondTensor (F ∘ φ) p ≠ 0 := by
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
  have hTG := (realSecondTensor_eventuallyEq heG).eq_of_nhds
  have hTF := (realSecondTensor_eventuallyEq hecomp).eq_of_nhds
  have h := quantitative_chart_phase_margin hG.contDiff hΦ.contDiff ξ p hd hC hε hDG
    (by simpa only [eD] using hdet) (by simpa only [eD] using hA)
    (by simpa only [ep,hTG] using hB) (by simpa only [ep,hTG] using hmargin)
  simpa only [eD,hTF] using h

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasMargins
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
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

omit [IsManifold planeModel ∞ M] in
lemma coordinateMap_transition (F : M → Space) (q p : M)
    {x : SmallModes.Base} (hx : x ∈ (coordinateTransition q p).source) :
    coordinateMap F q (coordinateTransition q p x) = coordinateMap F p x := by
  change spaceCoordinates (F (coordinateInverse q (coordinateTransition q p x))) =
    spaceCoordinates (F (coordinateInverse p x))
  rw [← coordinateChart_symm_apply, ← coordinateChart_symm_apply]
  change spaceCoordinates (F ((coordinateChart q).symm
    (coordinateChart q ((coordinateChart p).symm x)))) = _
  have hqx : (coordinateChart p).symm x ∈ (coordinateChart q).source := hx.2
  rw [(coordinateChart q).left_inv hqx]

omit [IsManifold planeModel ∞ M] in
lemma coordinateMap_transition_eventuallyEq (F : M → Space) (q p : M)
    {x : SmallModes.Base} (hx : x ∈ (coordinateTransition q p).source) :
    coordinateMap F q ∘ coordinateTransition q p =ᶠ[𝓝 x] coordinateMap F p := by
  filter_upwards [(coordinateTransition q p).open_source.mem_nhds hx] with y hy
  exact coordinateMap_transition F q p hy




theorem actual_chart_phase_margin {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (q p : M)
    {x : SmallModes.Base} (hx : x ∈ (coordinateTransition q p).source) (ξ : SmallModes.Base)
    {d L ε : ℝ} (hd : 0 < d) (hL : 0 < L) (hε : 0 < ε)
    (hD : NormalFrame.gramDet (coordDeriv dx (coordinateMap F q) (coordinateTransition q p x))
      (coordDeriv dy (coordinateMap F q) (coordinateTransition q p x)) ≠ 0)
    (hdet : d ≤ |coordDet (fderiv ℝ (coordinateTransition q p) x)|)
    (hA : ‖fderiv ℝ (coordinateTransition q p) x‖ ≤ L)
    (hB : realSecondTensor (coordinateMap F q) (coordinateTransition q p x) ≠ 0)
    (hmargin : ε*‖realSecondTensor (coordinateMap F q) (coordinateTransition q p x)‖ ≤
      ‖secondQuadratic (realSecondTensor (coordinateMap F q) (coordinateTransition q p x)) (-ξ.2,ξ.1)‖) :
    ‖pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ‖ ≤ 2*L*‖ξ‖ ∧
    d^2*ε/(4*L^2)*‖realSecondTensor (coordinateMap F p) x‖ ≤
      ‖secondQuadratic (realSecondTensor (coordinateMap F p) x)
        (-(pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ).2,
          (pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ).1)‖ ∧
    Good (realSecondTensor (coordinateMap F p) x)
      (pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ) ∧
    realSecondTensor (coordinateMap F p) x ≠ 0 := by
  have hy : coordinateTransition q p x ∈ coordinateDomain q := by
    rw [← coordinateChart_target]
    exact (coordinateChart q).map_source hx.2
  have ht := quantitative_chart_phase_margin_on
    (coordinateTransition q p).open_source (coordinateDomain_open q)
    (coordinateMap_smoothOn hF q) (coordinateTransition_smoothOn q p)
    hx hy ξ hd hL hε hD hdet hA hB hmargin
  have he := (realSecondTensor_eventuallyEq
    (coordinateMap_transition_eventuallyEq F q p hx)).eq_of_nhds
  simpa only [he] using ht

end ClosedSurfaceR4

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
lemma coordinateChart_compact_image {K : Set M} (hK : IsCompact K) (p : M)
    (hKs : K ⊆ (coordinateChart p).source) :
    IsCompact (coordinateChart p '' K) := hK.image_of_continuousOn ((coordinateChart p).continuousOn.mono hKs)

omit [IsManifold planeModel ∞ M] in
lemma coordinateChart_image_overlap {K : Set M} (q p : M)
    (hKp : K ⊆ (coordinateChart p).source) (hKq : K ⊆ (coordinateChart q).source) :
    coordinateChart p '' K ⊆ (coordinateTransition q p).source := by
  rintro x ⟨a,ha,rfl⟩
  constructor
  · exact (coordinateChart p).map_source (hKp ha)
  · change (coordinateChart p).symm (coordinateChart p a) ∈ (coordinateChart q).source
    rw [(coordinateChart p).left_inv (hKp ha)]
    exact hKq ha




theorem compact_overlap_phase_margin {K : Set M} (hK : IsCompact K) (q p : M)
    (hKp : K ⊆ (coordinateChart p).source) (hKq : K ⊆ (coordinateChart q).source) :
    ∃ η L : ℝ, 0 < η ∧ 0 < L ∧
      ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
      ∀ x ∈ coordinateChart p '' K, ∀ ξ : SmallModes.Base, ∀ ε : ℝ, 0 < ε →
      NormalFrame.gramDet (coordDeriv dx (coordinateMap F q) (coordinateTransition q p x))
        (coordDeriv dy (coordinateMap F q) (coordinateTransition q p x)) ≠ 0 →
      realSecondTensor (coordinateMap F q) (coordinateTransition q p x) ≠ 0 →
      ε*‖realSecondTensor (coordinateMap F q) (coordinateTransition q p x)‖ ≤
        ‖secondQuadratic (realSecondTensor (coordinateMap F q) (coordinateTransition q p x)) (-ξ.2,ξ.1)‖ →
      ‖pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ‖ ≤ L*‖ξ‖ ∧
      η*ε*‖realSecondTensor (coordinateMap F p) x‖ ≤
        ‖secondQuadratic (realSecondTensor (coordinateMap F p) x)
          (-(pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ).2,
            (pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ).1)‖ ∧
      Good (realSecondTensor (coordinateMap F p) x)
        (pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ) ∧
      realSecondTensor (coordinateMap F p) x ≠ 0 := by
  obtain ⟨d,L,hd,hL,hbound⟩ := coordinateTransition_compact_bounds q p
    (coordinateChart_compact_image hK p hKp) (coordinateChart_image_overlap q p hKp hKq)
  refine ⟨d^2/(4*L^2),2*L,div_pos (sq_pos_of_pos hd)
    (mul_pos (by norm_num) (sq_pos_of_pos hL)),mul_pos (by norm_num) hL,?_⟩
  intro F hF x hx ξ ε hε hD hB hm
  have h := actual_chart_phase_margin hF q p
    (coordinateChart_image_overlap q p hKp hKq hx) ξ hd hL hε hD
    (hbound x hx).1 (hbound x hx).2 hB hm
  have he : d^2/(4*L^2)*ε = d^2*ε/(4*L^2) := by ring
  simpa only [he] using h

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasPhases
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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

lemma phaseDerivative_linear_comp {φ : SmallModes.Base → SmallModes.Base}
    {x : SmallModes.Base} (hφ : DifferentiableAt ℝ φ x) (ξ : SmallModes.Base) :
    phaseDerivative (phaseLinear ξ ∘ φ) x = pullCovector (fderiv ℝ φ x) ξ := by
  have hd := ((phaseLinear ξ).hasFDerivAt.comp x hφ.hasFDerivAt).fderiv
  unfold phaseDerivative
  rw [hd]
  rfl



theorem actual_phase_differential (q p : M) (ξ : SmallModes.Base)
    {x : SmallModes.Base} (hx : x ∈ (coordinateTransition q p).source) :
    phaseDerivative (atlasPhase q ξ ∘ (coordinateChart p).symm) x =
      pullCovector (fderiv ℝ (coordinateTransition q p) x) ξ := by
  change phaseDerivative (phaseLinear ξ ∘ coordinateTransition q p) x = _
  have hc := ((coordinateTransition_smoothOn q p) x hx).contDiffAt
    ((coordinateTransition q p).open_source.mem_nhds hx)
  exact phaseDerivative_linear_comp (hc.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) ξ

omit [IsManifold planeModel ∞ M] in
lemma coordinateTransition_apply_chart (q p : M) {a : M}
    (ha : a ∈ (coordinateChart p).source) :
    coordinateTransition q p (coordinateChart p a) = coordinateChart q a := by
  change coordinateChart q ((coordinateChart p).symm (coordinateChart p a)) = _
  rw [(coordinateChart p).left_inv ha]

omit [IsManifold planeModel ∞ M] in
lemma coordinateTransition_mem_chart (q p : M) {a : M}
    (hap : a ∈ (coordinateChart p).source) (haq : a ∈ (coordinateChart q).source) :
    coordinateChart p a ∈ (coordinateTransition q p).source := by
  constructor
  · exact (coordinateChart p).map_source hap
  · change (coordinateChart p).symm (coordinateChart p a) ∈ (coordinateChart q).source
    rwa [(coordinateChart p).left_inv hap]



end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PhaseDifferentials
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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

lemma phaseDerivative_add {f g : SmallModes.Base → ℝ} {x : SmallModes.Base}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    phaseDerivative (f+g) x = phaseDerivative f x + phaseDerivative g x := by
  unfold phaseDerivative
  rw [fderiv_add hf hg]
  rfl

lemma phaseDerivative_sub {f g : SmallModes.Base → ℝ} {x : SmallModes.Base}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    phaseDerivative (f-g) x = phaseDerivative f x - phaseDerivative g x := by
  unfold phaseDerivative
  rw [fderiv_sub hf hg]
  rfl

lemma phaseDerivative_const_smul {f : SmallModes.Base → ℝ} {x : SmallModes.Base}
    (hf : DifferentiableAt ℝ f x) (c : ℝ) :
    phaseDerivative (c • f) x = c • phaseDerivative f x := by
  unfold phaseDerivative
  rw [fderiv_const_smul hf]
  rfl

lemma atlasPhase_in_chart_differentiable (q p : M) (ξ : SmallModes.Base)
    {a : M} (hap : a ∈ (coordinateChart p).source) (haq : a ∈ (coordinateChart q).source) :
    DifferentiableAt ℝ (atlasPhase q ξ ∘ (coordinateChart p).symm) (coordinateChart p a) := by
  have hx := coordinateTransition_mem_chart q p hap haq
  have ht := ((coordinateTransition_smoothOn q p) _ hx).contDiffAt
    ((coordinateTransition q p).open_source.mem_nhds hx)
  exact (phaseLinear ξ).differentiableAt.comp _ (ht.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))



end ClosedSurfaceR4

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
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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

lemma restore_smul (p : M) (χ : M → ℝ) (a : ℝ) (f : Base → V) :
    restore p χ (a • f) = a • restore p χ f := by
  funext x
  by_cases hx : x ∈ (chart p).source <;> simp [restore, hx, smul_smul, mul_comm]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GlobalPhaseGerms
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! On intersecting weight supports, restored global linear phases have
the same germs and covectors as the actual manifold coordinate phases. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
open JetPolynomial (planeCoordinateIsometry)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma linearAtlasPhase_eventually (Q : A.centers → PhaseBasis)
    (w : A.centers → Fin 3 → ℝ) (a : A.centers × Fin 3)
    (houter : ∀ x ∈ tsupport (A.weight a.1), A.outer a.1 =ᶠ[𝓝 x] (fun _ => 1))
    {p : M} (hp : p ∈ tsupport (A.weight a.1)) :
    A.linearAtlasPhase Q w a =ᶠ[𝓝 p]
      atlasPhase (a.1 : M) (w a.1 a.2 • (Q a.1).ξ a.2) := by
  filter_upwards [houter p hp,
    (chart (a.1 : M)).open_source.mem_nhds (A.weight_support a.1 hp)] with x ho hx
  rw [linearAtlasPhase, restore, indicator_of_mem hx, ho, one_smul]
  rfl

lemma vectorPlaneRead_eventually_comp_coordinateInverse
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : M → V) (k : A.centers)
    (houter : ∀ x ∈ tsupport (A.weight k), A.outer k =ᶠ[𝓝 x] (fun _ => 1))
    {p : M} (hp : p ∈ tsupport (A.weight k)) :
    A.vectorPlaneRead k F =ᶠ[𝓝 (coordinateChart (k : M) p)]
      F ∘ (coordinateChart (k : M)).symm := by
  let x := planeCoordinateIsometry (chart (k : M) p)
  let inv : SmallModes.Base → M := fun z => (chart (k : M)).symm (planeCoordinateIsometry.symm z)
  have hpS := A.weight_support k hp
  have hinv : inv x = p := by
    dsimp [inv,x]
    rw [LinearIsometryEquiv.symm_apply_apply,(chart (k : M)).left_inv hpS]
  have hc : ContinuousAt inv x := by
    apply ContinuousAt.comp
    · apply (chart (k : M)).continuousAt_symm
      simpa only [x,LinearIsometryEquiv.symm_apply_apply] using (chart (k : M)).map_source hpS
    · exact planeCoordinateIsometry.symm.continuous.continuousAt
  have ht : Tendsto inv (𝓝 x) (𝓝 p) := by simpa only [ContinuousAt,hinv] using hc
  have ho : ∀ᶠ z in 𝓝 x, A.outer k (inv z) = 1 := (houter p hp).comp_tendsto ht
  have htarget : ∀ᶠ z in 𝓝 x,
      planeCoordinateIsometry.symm z ∈ (chart (k : M)).target :=
    ((chart (k : M)).open_target.preimage planeCoordinateIsometry.symm.continuous).mem_nhds
      (by simpa only [Set.mem_preimage,x,LinearIsometryEquiv.symm_apply_apply] using
        (chart (k : M)).map_source hpS)
  change ∀ᶠ z in 𝓝 x, A.vectorPlaneRead k F z = F ((coordinateChart (k : M)).symm z)
  filter_upwards [ho,htarget] with z hz htgt
  change localize (k : M) (A.outer k) F (planeCoordinateIsometry.symm z) = _
  rw [localize,indicator_of_mem htgt]
  change A.outer k (inv z)^2 • F (inv z) = _
  rw [hz,one_pow,one_smul]
  rfl

/-- Both the original phase and its reading in another chart agree as
germs where the two actual compact supports meet. -/
lemma linearAtlasPhase_read_eventually (Q : A.centers → PhaseBasis)
    (w : A.centers → Fin 3 → ℝ) (a : A.centers × Fin 3) (k : A.centers)
    (houter : ∀ i x, x ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 x] (fun _ => 1))
    {p : M} (hpa : p ∈ tsupport (A.weight a.1)) (hpk : p ∈ tsupport (A.weight k)) :
    A.vectorPlaneRead k (A.linearAtlasPhase Q w a) =ᶠ[𝓝 (coordinateChart (k : M) p)]
      atlasPhase (a.1 : M) (w a.1 a.2 • (Q a.1).ξ a.2) ∘ (coordinateChart (k : M)).symm := by
  have hpK : p ∈ (coordinateChart (k : M)).source := by
    simpa only [coordinateChart_source,chart_source] using A.weight_support k hpk
  have hc := (coordinateChart (k : M)).continuousAt_symm
    ((coordinateChart (k : M)).map_source hpK)
  have ht : Tendsto (coordinateChart (k : M)).symm
      (𝓝 (coordinateChart (k : M) p)) (𝓝 p) := by
    simpa only [ContinuousAt,(coordinateChart (k : M)).left_inv hpK] using hc
  exact (A.vectorPlaneRead_eventually_comp_coordinateInverse
    (A.linearAtlasPhase Q w a) k (houter k) hpk).trans
    ((A.linearAtlasPhase_eventually Q w a (houter a.1) hpa).comp_tendsto ht)

lemma linearAtlasPhase_read_phaseDerivative (Q : A.centers → PhaseBasis)
    (w : A.centers → Fin 3 → ℝ) (a : A.centers × Fin 3) (k : A.centers)
    (houter : ∀ i x, x ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 x] (fun _ => 1))
    {p : M} (hpa : p ∈ tsupport (A.weight a.1)) (hpk : p ∈ tsupport (A.weight k)) :
    phaseDerivative (A.vectorPlaneRead k (A.linearAtlasPhase Q w a)) (coordinateChart (k : M) p) =
      w a.1 a.2 • atlasPhaseCovector (a.1 : M) (k : M) ((Q a.1).ξ a.2) p := by
  have he := A.linearAtlasPhase_read_eventually Q w a k houter hpa hpk
  have hd : phaseDerivative (A.vectorPlaneRead k (A.linearAtlasPhase Q w a))
      (coordinateChart (k : M) p) =
      phaseDerivative (atlasPhase (a.1 : M) (w a.1 a.2 • (Q a.1).ξ a.2) ∘
        (coordinateChart (k : M)).symm) (coordinateChart (k : M) p) := by
    unfold phaseDerivative
    rw [he.fderiv_eq (𝕜 := ℝ)]
  rw [hd]
  have hpK : p ∈ (coordinateChart (k : M)).source := by
    simpa only [coordinateChart_source,chart_source] using A.weight_support k hpk
  have hpA : p ∈ (coordinateChart (a.1 : M)).source := by
    simpa only [coordinateChart_source,chart_source] using A.weight_support a.1 hpa
  have hscale : atlasPhase (a.1 : M) (w a.1 a.2 • (Q a.1).ξ a.2) =
      w a.1 a.2 • atlasPhase (a.1 : M) ((Q a.1).ξ a.2) := by
    funext x
    simp only [atlasPhase,Function.comp_apply,phaseLinear_apply,
      Prod.smul_fst,Prod.smul_snd,smul_eq_mul,Pi.smul_apply]
    ring
  rw [hscale]
  change phaseDerivative (w a.1 a.2 •
    (atlasPhase (a.1 : M) ((Q a.1).ξ a.2) ∘ (coordinateChart (k : M)).symm))
      (coordinateChart (k : M) p) = _
  exact phaseDerivative_const_smul
    (atlasPhase_in_chart_differentiable (a.1 : M) (k : M) ((Q a.1).ξ a.2) hpK hpA) _

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_QualitativePhaseTransfer
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Good phase directions pass between surface coordinate charts. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry

lemma PhaseGeometry.Good.tensor_ne_zero {n : ℕ} {B : Fin 3 → RVec n} {ξ : Base}
    (h : Good B ξ) : B ≠ 0 := by
  intro hz
  apply h.2
  simp [hz,secondQuadratic]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

/-- The quantitative overlap theorem implies the qualitative phase
condition, with no externally supplied determinant or size constants. -/
theorem actual_phase_good_at {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (q p : M) {a : M}
    (hap : a ∈ (coordinateChart p).source) (haq : a ∈ (coordinateChart q).source)
    (ξ : Base)
    (hD : NormalFrame.gramDet
      (coordDeriv dx (coordinateMap F q) (coordinateChart q a))
      (coordDeriv dy (coordinateMap F q) (coordinateChart q a)) ≠ 0)
    (hgood : Good (realSecondTensor (coordinateMap F q) (coordinateChart q a)) ξ) :
    Good (realSecondTensor (coordinateMap F p) (coordinateChart p a))
      (atlasPhaseCovector q p ξ a) := by
  let B := realSecondTensor (coordinateMap F q) (coordinateChart q a)
  let c := ‖secondQuadratic B (-ξ.2,ξ.1)‖
  let ε := c/(‖B‖+1)
  have hc : 0 < c := norm_pos_iff.mpr hgood.2
  have hd : 0 < ‖B‖+1 := by positivity
  have hε : 0 < ε := div_pos hc hd
  have hm : ε*‖B‖ ≤ c := by
    calc
      ε*‖B‖ ≤ ε*(‖B‖+1) := mul_le_mul_of_nonneg_left (by linarith) hε.le
      _ = c := by dsimp [ε]; field_simp
  obtain ⟨η,L,_,_,ht⟩ := compact_overlap_phase_margin
    (K := ({a} : Set M)) isCompact_singleton q p
    (fun x hx => by simpa only [mem_singleton_iff.mp hx] using hap)
    (fun x hx => by simpa only [mem_singleton_iff.mp hx] using haq)
  have hx : coordinateChart p a ∈ coordinateChart p '' ({a} : Set M) :=
    ⟨a,by simp,rfl⟩
  have he := coordinateTransition_apply_chart q p hap
  have hresult := ht F hF (coordinateChart p a) hx ξ ε hε
    (by simpa only [he] using hD)
    (by simpa only [he] using hgood.tensor_ne_zero)
    (by simpa only [he] using hm)
  have hx' := coordinateTransition_mem_chart q p hap haq
  simpa only [atlasPhaseCovector,actual_phase_differential q p ξ hx'] using hresult.2.2.1

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GoodSmoothingAtlas
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smoothing atlas subordinate to actual good-phase neighborhoods. -/
noncomputable section
open Set Manifold Filter TopologicalSpace
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation

omit [IsManifold planeModel ∞ M] in
lemma coordinateMap_chart_symm (F : M → Space) (p : M) (x : SmallModes.Base) :
    coordinateMap F p x = spaceCoordinates (F ((chart p).symm (planeCoordinateIsometry.symm x))) := rfl

variable [T2Space M] [CompactSpace M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [T2Space M] [CompactSpace M] in
/-- Locally constant outer cutoffs identify the entire coordinate germ on
the original weight support, and hence every derivative used by the phases. -/
lemma vectorPlaneRead_eventually_coordinateMap
    (F : M → Space) (i : A.centers)
    (houter : ∀ x ∈ tsupport (A.weight i), A.outer i =ᶠ[𝓝 x] (fun _ => 1))
    {p : M} (hp : p ∈ tsupport (A.weight i)) :
    (spaceCoordinates ∘ A.vectorPlaneRead i F) =ᶠ[
      𝓝 (planeCoordinateIsometry (chart (i : M) p))] coordinateMap F (i : M) := by
  let x := planeCoordinateIsometry (chart (i : M) p)
  let inv : SmallModes.Base → M := fun z => (chart (i : M)).symm (planeCoordinateIsometry.symm z)
  have hpS := A.weight_support i hp
  have hinv : inv x = p := by
    dsimp [inv,x]
    rw [LinearIsometryEquiv.symm_apply_apply,(chart (i : M)).left_inv hpS]
  have hc : ContinuousAt inv x := by
    apply ContinuousAt.comp
    · apply (chart (i : M)).continuousAt_symm
      simpa only [x,LinearIsometryEquiv.symm_apply_apply] using (chart (i : M)).map_source hpS
    · exact planeCoordinateIsometry.symm.continuous.continuousAt
  have ht : Tendsto inv (𝓝 x) (𝓝 p) := by simpa only [ContinuousAt,hinv] using hc
  have ho : ∀ᶠ z in 𝓝 x, A.outer i (inv z) = 1 := (houter p hp).comp_tendsto ht
  have htarget : ∀ᶠ z in 𝓝 x,
      planeCoordinateIsometry.symm z ∈ (chart (i : M)).target :=
    ((chart (i : M)).open_target.preimage planeCoordinateIsometry.symm.continuous).mem_nhds
      (by simpa only [Set.mem_preimage,x,LinearIsometryEquiv.symm_apply_apply] using
        (chart (i : M)).map_source hpS)
  filter_upwards [ho,htarget] with z hz htgt
  change spaceCoordinates (localize (i : M) (A.outer i) F (planeCoordinateIsometry.symm z)) = _
  rw [localize,indicator_of_mem htgt]
  change spaceCoordinates (A.outer i (inv z)^2 • F (inv z)) = _
  rw [hz,one_pow,one_smul]
  exact (coordinateMap_chart_symm F (i : M) z).symm

end SmoothingAtlas

end FiniteOrderSmoothing
end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ActualPhaseGoodness
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pure global phases remain good when read in any overlapping atlas
chart. This supplies the geometric input to the compact weight choice. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry
open JetPolynomial (planeCoordinateIsometry)
open JetPolynomial.Perturbation (modeSupport)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem linearAtlasPhase_unit_read_good {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (Q : A.centers → PhaseBasis)
    (houter : ∀ i x, x ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (hImm : ∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x))
    (hpure : ∀ i j x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
      Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ((Q i).ξ j))
    (a : A.centers × Fin 3) (k : A.centers)
    {p : M} (hpa : p ∈ tsupport (A.weight a.1)) (hpk : p ∈ tsupport (A.weight k)) :
    Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) (coordinateChart (k : M) p))
      (phaseDerivative (A.vectorPlaneRead k (A.linearAtlasPhase Q (fun _ _ => 1) a))
        (coordinateChart (k : M) p)) := by
  have hpA : p ∈ (coordinateChart (a.1 : M)).source := by
    simpa only [coordinateChart_source,chart_source] using A.weight_support a.1 hpa
  have hpK : p ∈ (coordinateChart (k : M)).source := by
    simpa only [coordinateChart_source,chart_source] using A.weight_support k hpk
  have hxA : coordinateChart (a.1 : M) p ∈
      (modeSupport (A.chartWeightCompact a.1) : Set SmallModes.Base) := by
    exact ⟨chart (a.1 : M) p,⟨p,hpa,rfl⟩,rfl⟩
  have heA := A.vectorPlaneRead_eventually_coordinateMap F a.1 (houter a.1) hpa
  have hdA := heA.fderiv_eq (𝕜 := ℝ)
  have hsA := (realSecondTensor_eventuallyEq heA).eq_of_nhds
  have hi := hImm a.1 _ hxA
  have hg := hpure a.1 a.2 _ hxA
  change fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead a.1 F) (coordinateChart (a.1 : M) p) =
    fderiv ℝ (coordinateMap F (a.1 : M)) (coordinateChart (a.1 : M) p) at hdA
  change realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead a.1 F) (coordinateChart (a.1 : M) p) =
    realSecondTensor (coordinateMap F (a.1 : M)) (coordinateChart (a.1 : M) p) at hsA
  rw [hdA] at hi
  rw [hsA] at hg
  have ht := actual_phase_good_at hF (a.1 : M) (k : M) hpK hpA ((Q a.1).ξ a.2)
    (gramDet_ne_zero_of_injective _ hi) hg
  have heK := A.vectorPlaneRead_eventually_coordinateMap F k (houter k) hpk
  have hsK := (realSecondTensor_eventuallyEq heK).eq_of_nhds
  change realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) (coordinateChart (k : M) p) =
    realSecondTensor (coordinateMap F (k : M)) (coordinateChart (k : M) p) at hsK
  rw [hsK,A.linearAtlasPhase_read_phaseDerivative Q (fun _ _ => 1) a k houter hpa hpk,
    one_smul]
  exact ht

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CompactPhaseWeights
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive frequency weights giving good sums and differences on the
actual compact pairwise phase supports. -/
noncomputable section
open Set

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

theorem finite_set_compact_good_weights {ι X : Type*} [TopologicalSpace X] {n : ℕ}
    (K : ι → ι → Set X) (hK : ∀ a b, IsCompact (K a b))
    (hKs : ∀ a b, K a b = K b a)
    (B : X → Fin 3 → RVec n) (ξ : ι → X → Base)
    (hB : Continuous B) (hξ : ∀ a, Continuous (ξ a))
    (hgood : ∀ a b, a ≠ b → ∀ x ∈ K a b, Good (B x) (ξ a x))
    (s : Finset ι) :
    ∃ w : ι → ℝ, (∀ a ∈ s, 0 < w a) ∧
      ∀ a ∈ s, ∀ b ∈ s, a ≠ b → ∀ x ∈ K a b,
        Good (B x) (w a • ξ a x + w b • ξ b x) ∧
        Good (B x) (w a • ξ a x - w b • ξ b x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨fun _ => 1, ?_, ?_⟩ <;> simp
  | @insert a s ha ih =>
      obtain ⟨w, hw, hpairs⟩ := ih
      let : ∀ b : {b // b ∈ s}, CompactSpace (K a b.1) :=
        fun b => isCompact_iff_compactSpace.mp (hK a b.1)
      obtain ⟨lam, hlam, hdominant⟩ := exists_dominant_weight
        (ι := {b // b ∈ s}) (X := fun b => K a b.1)
        (fun _ x => B x.1) (fun _ x => ξ a x.1) (fun b x => ξ b.1 x.1)
        (fun _ => hB.comp continuous_subtype_val)
        (fun _ => (hξ a).comp continuous_subtype_val)
        (fun b => (hξ b.1).comp continuous_subtype_val)
        (fun b x => hgood a b.1 (fun hab => ha (hab.symm ▸ b.2)) x.1 x.2)
        (fun b => w b.1)
      let w' := Function.update w a lam
      have hw'a : w' a = lam := Function.update_self a lam w
      have hw'old (b : ι) (hb : b ∈ s) : w' b = w b := by
        exact Function.update_of_ne (fun hba : b = a => ha (hba ▸ hb)) lam w
      refine ⟨w', ?_, ?_⟩
      · intro b hb
        rcases Finset.mem_insert.mp hb with hba | hb
        · rw [hba,hw'a]
          exact hlam
        · rw [hw'old b hb]
          exact hw b hb
      · intro b hb c hc hbc x hx
        rcases Finset.mem_insert.mp hb with hba | hb
        · subst b
          have hc' : c ∈ s := (Finset.mem_insert.mp hc).resolve_left hbc.symm
          rw [hw'a, hw'old c hc']
          exact hdominant ⟨c,hc'⟩ ⟨x,hx⟩
        · rcases Finset.mem_insert.mp hc with hca | hc
          · subst c
            have hxa : x ∈ K a b := by rwa [hKs a b]
            have hh := hdominant ⟨b,hb⟩ ⟨x,hxa⟩
            rw [hw'old b hb, hw'a]
            refine ⟨?_, ?_⟩
            · simpa only [add_comm] using hh.1
            · simpa only [neg_sub] using good_neg hh.2
          · rw [hw'old b hb, hw'old c hc]
            exact hpairs b hb c hc hbc x hx

/-- One fixed positive weight for each member of an arbitrary finite
phase family makes all distinct pairwise sums and differences good on
their prescribed symmetric compact supports. -/
theorem finite_compact_good_weights {ι X : Type*} [Finite ι] [TopologicalSpace X] {n : ℕ}
    (K : ι → ι → Set X) (hK : ∀ a b, IsCompact (K a b))
    (hKs : ∀ a b, K a b = K b a)
    (B : X → Fin 3 → RVec n) (ξ : ι → X → Base)
    (hB : Continuous B) (hξ : ∀ a, Continuous (ξ a))
    (hgood : ∀ a b, a ≠ b → ∀ x ∈ K a b, Good (B x) (ξ a x)) :
    ∃ w : ι → ℝ, (∀ a, 0 < w a) ∧
      ∀ a b, a ≠ b → ∀ x ∈ K a b,
        Good (B x) (w a • ξ a x + w b • ξ b x) ∧
        Good (B x) (w a • ξ a x - w b • ξ b x) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  obtain ⟨w,hw,hpairs⟩ := finite_set_compact_good_weights K hK hKs B ξ hB hξ hgood
    (Finset.univ : Finset ι)
  exact ⟨w,fun a => hw a (Finset.mem_univ a),
    fun a b => hpairs a (Finset.mem_univ a) b (Finset.mem_univ b)⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasCompactPhaseWeights
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One frequency per global phase, chosen simultaneously on every chart overlap. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry
open JetPolynomial.Perturbation (modeSupport)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- Compactness selects frequencies before any target tensor or correction scale.
The same frequency works in every chart that meets the phase support. -/
theorem exists_overlap_phase_weights {ι : Type*} [Finite ι]
    {F : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    (φ : ι → M → ℝ) (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
    (S : ι → Set M) (hS : ∀ a, IsClosed (S a))
    (hImm : ∀ k p, p ∈ tsupport (A.weight k) → Function.Injective
      (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead k F) (coordinateChart (k : M) p)))
    (hgood : ∀ k a p, p ∈ tsupport (A.weight k) → p ∈ S a →
      Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F)
        (coordinateChart (k : M) p))
        (phaseDerivative (A.vectorPlaneRead k (φ a)) (coordinateChart (k : M) p))) :
    ∃ w : ι → ℝ, (∀ a, 0 < w a) ∧
      ∀ k a b, a ≠ b → ∀ p, p ∈ tsupport (A.weight k) → p ∈ S a → p ∈ S b →
        Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F)
          (coordinateChart (k : M) p))
          (w a • phaseDerivative (A.vectorPlaneRead k (φ a)) (coordinateChart (k : M) p) +
           w b • phaseDerivative (A.vectorPlaneRead k (φ b)) (coordinateChart (k : M) p)) ∧
        Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F)
          (coordinateChart (k : M) p))
          (w a • phaseDerivative (A.vectorPlaneRead k (φ a)) (coordinateChart (k : M) p) -
           w b • phaseDerivative (A.vectorPlaneRead k (φ b)) (coordinateChart (k : M) p)) := by
  classical
  let X := Σ k : A.centers, ↥(tsupport (A.weight k))
  let : ∀ k : A.centers, CompactSpace ↥(tsupport (A.weight k)) :=
    fun k => isCompact_iff_compactSpace.mp (isClosed_tsupport (A.weight k)).isCompact
  let point : X → M := fun x => x.2.1
  have hpoint : Continuous point := continuous_sigma fun _ => continuous_subtype_val
  let B : X → Fin 3 → RVec 4 := fun x =>
    realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead x.1 F)
      (coordinateChart (x.1 : M) x.2.1)
  let ξ : ι → X → Base := fun a x =>
    phaseDerivative (A.vectorPlaneRead x.1 (φ a)) (coordinateChart (x.1 : M) x.2.1)
  have hc (k : A.centers) : Continuous
      (fun p : ↥(tsupport (A.weight k)) => coordinateChart (k : M) p.1) :=
    (coordinateChart (k : M)).continuousOn.comp_continuous continuous_subtype_val
      (fun p => by simpa only [coordinateChart_source,chart_source] using A.weight_support k p.2)
  have hB : Continuous B := by
    apply continuous_sigma
    intro k
    apply continuous_iff_continuousAt.mpr
    intro p
    exact ContinuousAt.comp (f := fun p : ↥(tsupport (A.weight k)) =>
      coordinateChart (k : M) p.1) ((contDiffAt_realSecondTensor
      (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth k hF)) _
      (gramDet_ne_zero_of_injective _ (hImm k p.1 p.2))).continuousAt) (hc k).continuousAt
  have hξ (a : ι) : Continuous (ξ a) := continuous_sigma fun k =>
    (continuous_phaseDerivative (A.vectorPlaneRead_smooth k (hφ a))).comp (hc k)
  let K : ι → ι → Set X := fun a b => point ⁻¹' (S a ∩ S b)
  have hK (a b : ι) : IsCompact (K a b) :=
    ((hS a).inter (hS b)).preimage hpoint |>.isCompact
  have hKs (a b : ι) : K a b = K b a := by simp only [K,inter_comm]
  obtain ⟨w,hw,hpairs⟩ := finite_compact_good_weights K hK hKs B ξ hB hξ
    (fun a _ _ x hx => hgood x.1 a x.2.1 x.2.2 hx.1)
  refine ⟨w,hw,?_⟩
  intro k a b hab p hp hpa hpb
  exact hpairs a b hab ⟨k,⟨p,hp⟩⟩ ⟨hpa,hpb⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedAtlasPhases
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Frequency scaling of the actual smooth global atlas phases. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4

lemma phaseLinear_smul (c : ℝ) (ξ : SmallModes.Base) :
    phaseLinear (c • ξ) = c • phaseLinear ξ := by
  apply ContinuousLinearMap.ext
  intro x
  change phaseLinear (c • ξ) x = c * phaseLinear ξ x
  simp only [phaseLinear_apply,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

namespace FiniteOrderSmoothing
open PhaseGeometry
open JetPolynomial (planeCoordinateIsometry)
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma linearAtlasPhase_smooth (Q : A.centers → PhaseBasis)
    (w : A.centers → Fin 3 → ℝ) (a : A.centers × Fin 3) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (A.linearAtlasPhase Q w a) :=
  restore_smooth (a.1 : M) (A.outer_smooth a.1) (A.outer_support a.1)
    ((phaseLinear (w a.1 a.2 • (Q a.1).ξ a.2)).contDiff.comp planeCoordinateIsometry.contDiff)

lemma linearAtlasPhase_smul_unit (Q : A.centers → PhaseBasis)
    (w : A.centers → Fin 3 → ℝ) (a : A.centers × Fin 3) :
    A.linearAtlasPhase Q w a = w a.1 a.2 • A.linearAtlasPhase Q (fun _ _ => 1) a := by
  unfold linearAtlasPhase
  simp only [one_smul]
  have he : phaseLinear (w a.1 a.2 • (Q a.1).ξ a.2) ∘ planeCoordinateIsometry =
      w a.1 a.2 • (phaseLinear ((Q a.1).ξ a.2) ∘ planeCoordinateIsometry) := by
    funext x
    rw [phaseLinear_smul]
    rfl
  rw [he,restore_smul]

lemma vectorPlaneRead_real_smul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (k : A.centers) (c : ℝ) (F : M → V) :
    A.vectorPlaneRead k (c • F) = c • A.vectorPlaneRead k F := by
  funext x
  change localize (k : M) (A.outer k) (c • F) (planeCoordinateIsometry.symm x) = _
  rw [localize_smul]
  rfl

variable [CompactSpace M]

/-- Frequency weights scale the read phase derivative everywhere, not
just on the compact supports used to establish good geometry. -/
lemma linearAtlasPhase_read_derivative_smul_unit (Q : A.centers → PhaseBasis)
    (w : A.centers → Fin 3 → ℝ) (a : A.centers × Fin 3) (k : A.centers)
    (x : SmallModes.Base) :
    phaseDerivative (A.vectorPlaneRead k (A.linearAtlasPhase Q w a)) x =
      w a.1 a.2 •
        phaseDerivative (A.vectorPlaneRead k (A.linearAtlasPhase Q (fun _ _ => 1) a)) x := by
  rw [A.linearAtlasPhase_smul_unit Q w a,A.vectorPlaneRead_real_smul]
  exact phaseDerivative_const_smul
    ((A.vectorPlaneRead_smooth k (A.linearAtlasPhase_smooth Q (fun _ _ => 1) a)).differentiable
      (by simp) x) _

end SmoothingAtlas
end FiniteOrderSmoothing
end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_GoodQuadraticAtlasPhases
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual restored global phases have good quadratic interactions. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- A single choice of positive frequencies makes every actual quadratic
phase good on the compact support where its amplitude can be nonzero. -/
theorem exists_good_quadratic_atlas_phases {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (Q : A.centers → PhaseBasis)
    (houter : ∀ i x, x ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (hImm : ∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x))
    (hpure : ∀ i j x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
      Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ((Q i).ξ j)) :
    ∃ w : A.centers → Fin 3 → ℝ, (∀ i j, 0 < w i j) ∧
      ∀ k l x, x ∈ (modeSupport
        (A.quadraticOverlapCompact (fun a : A.centers × Fin 3 => tsupport (A.weight a.1))
          (fun a => isClosed_tsupport (A.weight a.1)) k l) : Set SmallModes.Base) →
        Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F) x)
          (phaseDerivative (coordinatePhase (A.globalQuadraticPhase (A.linearAtlasPhase Q w) k l)) x) := by
  classical
  let φ := A.linearAtlasPhase Q (fun _ _ => 1)
  have hφ (a : A.centers × Fin 3) : ContMDiff planeModel 𝓘(ℝ) ∞ (φ a) :=
    A.linearAtlasPhase_smooth Q (fun _ _ => 1) a
  have hpoint (k : A.centers) (p : M) (hp : p ∈ tsupport (A.weight k)) :
      coordinateChart (k : M) p ∈ (modeSupport (A.chartWeightCompact k) : Set SmallModes.Base) :=
    ⟨chart (k : M) p,⟨p,hp,rfl⟩,rfl⟩
  obtain ⟨v,hv,hpairs⟩ := A.exists_overlap_phase_weights hF φ hφ
    (fun a : A.centers × Fin 3 => tsupport (A.weight a.1)) (fun _ => isClosed_tsupport _)
    (fun k p hp => hImm k _ (hpoint k p hp))
    (fun k a p hpk hpa => A.linearAtlasPhase_unit_read_good hF Q houter hImm hpure a k hpa hpk)
  let w : A.centers → Fin 3 → ℝ := fun i j => v (i,j)
  refine ⟨w,fun i j => hv (i,j),?_⟩
  intro k l x hx
  change x ∈ planeCoordinateIsometry '' ((chart (k : M)) ''
    (tsupport (A.weight k) ∩ globalQuadraticSupport
      (fun a : A.centers × Fin 3 => tsupport (A.weight a.1)) l)) at hx
  rcases hx with ⟨y,⟨p,⟨hpk,hpl⟩,rfl⟩,rfl⟩
  have he : coordinatePhase (A.globalQuadraticPhase (A.linearAtlasPhase Q w) k l) =
      quadraticPhase (fun a => A.vectorPlaneRead k (A.linearAtlasPhase Q w a)) l := by
    funext z
    simp only [coordinatePhase,globalQuadraticPhase,Function.comp_apply,
      LinearIsometryEquiv.apply_symm_apply]
  rw [he]
  change Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead k F)
    (coordinateChart (k : M) p))
    (phaseDerivative (quadraticPhase (fun a => A.vectorPlaneRead k (A.linearAtlasPhase Q w a)) l)
      (coordinateChart (k : M) p))
  have hd (a : A.centers × Fin 3) :=
    (A.vectorPlaneRead_smooth k (A.linearAtlasPhase_smooth Q w a)).differentiable (by simp)
      (coordinateChart (k : M) p)
  have hscale (a : A.centers × Fin 3) :
      phaseDerivative (A.vectorPlaneRead k (A.linearAtlasPhase Q w a)) (coordinateChart (k : M) p) =
        v a • phaseDerivative (A.vectorPlaneRead k (φ a)) (coordinateChart (k : M) p) := by
    exact A.linearAtlasPhase_read_derivative_smul_unit Q w a k _
  rcases l with a | ⟨a,b,c⟩
  · change Good _ (phaseDerivative ((2 : ℝ) • A.vectorPlaneRead k (A.linearAtlasPhase Q w a)) _)
    rw [phaseDerivative_const_smul (hd a) 2,hscale]
    exact good_smul (by norm_num : (2 : ℝ) ≠ 0)
      (good_smul (hv a).ne' (A.linearAtlasPhase_unit_read_good hF Q houter hImm hpure a k hpl hpk))
  · have hpairs' := hpairs k a b.1 b.2.symm p hpk hpl.1 hpl.2
    cases c
    · change Good _ (phaseDerivative
        (A.vectorPlaneRead k (A.linearAtlasPhase Q w a) +
         A.vectorPlaneRead k (A.linearAtlasPhase Q w b.1)) _)
      rw [phaseDerivative_add (hd a) (hd b.1),hscale,hscale]
      exact hpairs'.1
    · change Good _ (phaseDerivative
        (A.vectorPlaneRead k (A.linearAtlasPhase Q w a) -
         A.vectorPlaneRead k (A.linearAtlasPhase Q w b.1)) _)
      rw [phaseDerivative_sub (hd a) (hd b.1),hscale,hscale]
      exact hpairs'.2

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_MetricGoodPhaseData
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual metric-adapted phase geometry, including all cross-chart
quadratic phases needed by the small-increment construction. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes PhaseGeometry
open JetPolynomial JetPolynomial.Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace MetricGoodPhaseData
local instance metricPhaseDataFiberNormed_rc84853_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance metricPhaseDataFiberSpace_rc84853_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance metricPhaseDataDualAdd_rc84853_1 : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance metricPhaseDataDualSmul_rc84853_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable [T2Space M]

local instance metricPhaseDataSectionNormed_rc84853_1 (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricPhaseDataSectionSpace_rc84853_1 (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- A metric and an immersion with nonzero coordinate second form
produce all the fixed phase geometry required by the analytic step. -/
theorem nonempty_oai (g : SmoothMetric M) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p))
    (hB : ∀ p, ∃ v w : SmallModes.Base,
      realSecondForm (coordinateMap F p) v w (coordinateCenter p) ≠ 0) :
    Nonempty (MetricGoodPhaseData g F) := by
  obtain ⟨A,P,_,houter,hgeometry⟩ := exists_metric_good_smoothingAtlas g hF hImm hB
  let Q : A.centers → PhaseBasis := fun i => (P (i : M)).phaseBasis
  have hi : ∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x) :=
    fun i x hx => (hgeometry i x hx).1
  have hp : ∀ i j x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
      Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ((Q i).ξ j) :=
    fun i j x hx => (hgeometry i x hx).2.2.1 j
  obtain ⟨w,hw,hquad⟩ := A.exists_good_quadratic_atlas_phases hF Q houter hi hp
  exact ⟨{
    A := A
    Q := Q
    w := w
    weight_pos := hw
    outer_locally_one := houter
    immersion := hi
    pure_good := hp
    metric_positive := fun i j x hx => (hgeometry i x hx).2.1 j
    quadratic_good := hquad
  }⟩

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.nonempty_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.nonempty_oai.{u_1}
