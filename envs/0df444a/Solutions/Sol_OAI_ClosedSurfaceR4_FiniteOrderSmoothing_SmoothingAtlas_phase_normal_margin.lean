-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phase_normal_margin
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:03:40.293977+00:00
-- url     : https://prove2.me/submissions/c763b06f-2ad3-4526-9044-0c5681458ce7

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
import Definitions.Def_OAIQ249SI009
import Definitions.Def_OAIQ249SI010

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
attribute [-instance] _root_.instVAddIntReal_solutions
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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ImmersionJets
attribute [-instance] _root_.instVAddIntReal_solutions
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

lemma injective_of_gramDet_ne_zero (A : Base →L[ℝ] RVec 4)
    (hD : NormalFrame.gramDet (A dx) (A dy) ≠ 0) : Function.Injective A := by
  have hz : ∀ v : Base, A v = 0 → v = 0 := by
    intro v hv
    have hb : A v = v.1 • A dx + v.2 • A dy := by
      calc A v = A (v.1 • dx + v.2 • dy) := congrArg A (base_eq_basis v)
           _ = _ := by simp
    have hx := congrArg (fun W => A dx ⬝ᵥ W) hv
    have hy := congrArg (fun W => A dy ⬝ᵥ W) hv
    rw [hb] at hx hy
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, dotProduct_zero,
      dotProduct_comm (A dy) (A dx)] at hx hy
    have hvx : v.1 = 0 := by
      apply (mul_eq_zero.mp (show NormalFrame.gramDet (A dx) (A dy) * v.1 = 0 by
        unfold NormalFrame.gramDet
        linear_combination (A dy ⬝ᵥ A dy) * hx - (A dx ⬝ᵥ A dy) * hy)).resolve_left hD
    have hvy : v.2 = 0 := by
      apply (mul_eq_zero.mp (show NormalFrame.gramDet (A dx) (A dy) * v.2 = 0 by
        unfold NormalFrame.gramDet
        linear_combination (A dx ⬝ᵥ A dx) * hy - (A dx ⬝ᵥ A dy) * hx)).resolve_left hD
    exact Prod.ext hvx hvy
  intro p q hpq
  exact sub_eq_zero.mp (hz (p-q) (by simpa using sub_eq_zero.mpr hpq))

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SmoothCoordinates
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
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
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_LocalPhaseData
attribute [-instance] _root_.instVAddIntReal_solutions
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseChartGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Good phase directions remain good in their actual nonlinear phase charts. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma inverse_chart_derivative (e : OpenPartialHomeomorph Base Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm) {y : Base} (hy : y ∈ e.target) :
    (fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y) = ContinuousLinearMap.id ℝ Base := by
  have hh : e ∘ e.symm =ᶠ[𝓝 y] id := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact e.right_inv hz
  rw [← fderiv_comp y (he.differentiable (by simp) _) (hi.differentiable (by simp) _),
    hh.fderiv_eq,fderiv_id]

lemma inverse_chart_derivative_injective (e : OpenPartialHomeomorph Base Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm) {y : Base} (hy : y ∈ e.target) :
    Function.Injective (fderiv ℝ e.symm y) := by
  have hh := inverse_chart_derivative e he hi hy
  intro u v huv
  have h := congrArg (fderiv ℝ e (e.symm y)) huv
  change ((fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y)) u =
    ((fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y)) v at h
  simpa only [hh,ContinuousLinearMap.id_apply] using h

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SurfaceJetCoordinates
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translate the geometric surface jets to the coordinates used by the
quantitative finite-polynomial construction. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.SurfaceJetCoordinates
open RealModes SmallModes WeightedEstimates

lemma directional_chart (f : Base → ℝ) (hf : ContDiff ℝ ∞ f) (w : List (Fin 2)) :
    iteratedDirectional (w.map JetPolynomial.coordinateVector) (f ∘ baseEquiv) =
      (iteratedDirectional (w.map (fun i => baseEquiv (JetPolynomial.coordinateVector i))) f) ∘ baseEquiv := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [List.map_cons, iteratedDirectional]
    rw [ih]
    funext p
    have hs : ContDiff ℝ ∞
        (iteratedDirectional (w.map (fun i => baseEquiv (JetPolynomial.coordinateVector i))) f) :=
      contDiffOn_univ.mp (contDiffOn_iteratedDirectional isOpen_univ hf.contDiffOn _)
    rw [fderiv_comp p (hs.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _) baseEquiv.differentiableAt,
      baseEquiv.fderiv, ContinuousLinearMap.comp_apply]
    rfl

lemma directional_component {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (w : List Base) (a : Fin 4) :
    iteratedDirectional w (fun p => F p a) = fun p => iteratedDirectional w F p a := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    simp only [iteratedDirectional]
    rw [ih]
    funext p
    have hs : ContDiff ℝ ∞ (iteratedDirectional w F) :=
      contDiffOn_univ.mp (contDiffOn_iteratedDirectional isOpen_univ hF.contDiffOn w)
    rw [fderiv_apply (hs.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p) a]
    rfl

theorem decode_lowJet {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : JetPolynomial.Base) :
    decode (JetPolynomial.lowJet (F ∘ baseEquiv) p) = CollarVelocity.jetSection F (baseEquiv p) := by
  apply Prod.ext
  · rfl
  · funext i a
    change JetPolynomial.jet (F ∘ baseEquiv) (JetPolynomial.lowWord (![1, 2, 3, 4, 6] i)) a p =
      realTwoJet F (baseEquiv p) i a
    have he (w : List (Fin 2)) : JetPolynomial.jet (F ∘ baseEquiv) w a p =
        iteratedDirectional (w.map (fun j => baseEquiv (JetPolynomial.coordinateVector j))) F (baseEquiv p) a := by
      change iteratedDirectional (w.map JetPolynomial.coordinateVector)
        ((fun q => F q a) ∘ baseEquiv) p = _
      rw [directional_chart _ (contDiff_pi.mp hF a) w, Function.comp_apply, directional_component hF]
    rw [he]
    fin_cases i <;> simp [JetPolynomial.lowWord, realTwoJet, iteratedDirectional, coordDeriv,
      JetPolynomial.coordinateVector, dx, dy] <;> rfl

end ClosedSurfaceR4.SurfaceJetCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseChartNormalTransport
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A normal-curvature margin in a phase chart gives a fixed margin in
the original coordinates, uniformly for every smooth immersion. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma phase_chart_normal_transport
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {W V : RField 4} (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    (hrel : ∀ x ∈ e.source, W x = V (e x)) {x : Base} (hx : x ∈ e.source)
    (hI : Function.Injective (fderiv ℝ V (e x))) :
    Function.Injective (fderiv ℝ W x) ∧
      ‖realSecondTensor V (e x)‖ ≤
        4*‖realSecondTensor W x‖*‖fderiv ℝ e.symm (e x)‖^2 := by
  have hR : W =ᶠ[𝓝 x] V ∘ e := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact hrel y hy
  have hIx : Function.Injective (fderiv ℝ W x) := by
    rw [hR.fderiv_eq,fderiv_comp x (hV.differentiable (by simp) _) (he.differentiable (by simp) _)]
    exact hI.comp (inverse_chart_derivative_injective e.symm hi he hx)
  refine ⟨hIx,?_⟩
  have hVrel : V =ᶠ[𝓝 (e x)] W ∘ e.symm := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hx)] with y hy
    simpa only [Function.comp_apply,e.right_inv hy] using (hrel (e.symm y) (e.map_target hy)).symm
  have hD : coordDet (fderiv ℝ e.symm (e x)) ≠ 0 :=
    coordDet_fderiv_ne_zero_of_local_inverse e.open_target e.open_source hi.contDiffOn he.contDiffOn
      (fun _ hy => e.map_target hy) (fun y hy => e.right_inv hy) (e.map_source hx)
  have hh := norm_realSecondTensor_comp_smooth hW hi (e x)
    (by simpa only [e.left_inv hx,coordDeriv] using gramDet_ne_zero_of_injective _ hIx) hD
  rw [← (realSecondTensor_eventuallyEq hVrel).eq_of_nhds,e.left_inv hx] at hh
  exact hh

theorem compact_phase_chart_normal_margin
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {K : Set Base} (hK : IsCompact K) (hKS : K ⊆ e.source) :
    ∃ D : ℝ, 0 < D ∧ ∀ (W V : RField 4), ContDiff ℝ ∞ W → ContDiff ℝ ∞ V →
      (∀ x ∈ e.source, W x = V (e x)) →
      ∀ x ∈ K, Function.Injective (fderiv ℝ V (e x)) →
      ∀ c : ℝ, c < ‖realSecondTensor V (e x)‖ →
        Function.Injective (fderiv ℝ W x) ∧ c/D < ‖realSecondTensor W x‖ := by
  have hd : Continuous (fun x => fderiv ℝ e.symm (e x)) :=
    ((hi.fderiv_right (m := ∞) (by simp)).continuous).comp he.continuous
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hd.continuousOn
  let D : ℝ := 4*(1+|B|)^2
  have hD : 0 < D := by dsimp [D] <;> positivity
  refine ⟨D,hD,?_⟩
  intro W V hW hV hrel x hx hI c hc
  obtain ⟨hIx,hbound⟩ := phase_chart_normal_transport e he hi hW hV hrel (hKS hx) hI
  refine ⟨hIx,(div_lt_iff₀ hD).mpr ?_⟩
  have hnorm : ‖fderiv ℝ e.symm (e x)‖ ≤ 1+|B| := (hB x hx).trans (by linarith [le_abs_self B])
  have hb : 4*‖realSecondTensor W x‖*‖fderiv ℝ e.symm (e x)‖^2 ≤
      ‖realSecondTensor W x‖*D := by
    dsimp [D]
    calc
      _ ≤ 4*‖realSecondTensor W x‖*(1+|B|)^2 := by gcongr
      _ = _ := by ring
  exact hc.trans_le (hbound.trans hb)

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_RealPhaseChart
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual phase chart in the real pair coordinates used by curvature. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.JetPolynomial

lemma realPhaseChart_apply (e : OpenPartialHomeomorph Base Base) (x : SmallModes.Base) :
    realPhaseChart e x = planeCoordinateIsometry (e (planeCoordinateIsometry.symm x)) := rfl

lemma realPhaseChart_symm_apply (e : OpenPartialHomeomorph Base Base) (x : SmallModes.Base) :
    (realPhaseChart e).symm x = planeCoordinateIsometry (e.symm (planeCoordinateIsometry.symm x)) := rfl

lemma realPhaseChart_smooth (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e) :
    ContDiff ℝ ∞ (realPhaseChart e) :=
  planeCoordinateIsometry.contDiff.comp (he.comp planeCoordinateIsometry.symm.contDiff)

lemma realPhaseChart_symm_smooth (e : OpenPartialHomeomorph Base Base) (hi : ContDiff ℝ ∞ e.symm) :
    ContDiff ℝ ∞ (realPhaseChart e).symm :=
  planeCoordinateIsometry.contDiff.comp (hi.comp planeCoordinateIsometry.symm.contDiff)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SurfaceVelocityIdentities
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The leading metric and support of the actual second-jet family. -/
noncomputable section
open Set
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates CovarianceCorrector
open LocalPeriodicExpansion
local notation "ι" => JetVelocityCoordinates.toEuclidean

lemma first_slot {G : JetPolynomial.Base → JetPolynomial.Space}
    (hG : ContDiff ℝ ∞ G) (i : Fin 2) (p : JetPolynomial.Base) :
    slot (![1, 2] i) (lowJet G p) = fderiv ℝ G p (coordinateVector i) := by
  funext a
  have he := congrArg (fun L : JetPolynomial.Base →L[ℝ] ℝ => L (coordinateVector i))
    (fderiv_apply (hG.differentiable (by simp) p) a)
  calc
    _ = fderiv ℝ (fun q => G q a) p (coordinateVector i) := by fin_cases i <;> rfl
    _ = _ := he

lemma euclidean_first_derivative {G : JetPolynomial.Base → JetPolynomial.Space}
    (hG : ContDiff ℝ ∞ G) (i : Fin 2) (p : JetPolynomial.Base) :
    fderiv ℝ (fun q => ι (G q)) p (coordinateVector i) =
      ι (slot (![1, 2] i) (lowJet G p)) := by
  have hd := (JetVelocityCoordinates.toEuclidean.hasFDerivAt.comp p
    (hG.differentiable (by simp) p).hasFDerivAt).fderiv
  calc
    _ = ι (fderiv ℝ G p (coordinateVector i)) :=
      congrArg (fun L : JetPolynomial.Base →L[ℝ] Euclidean => L (coordinateVector i)) hd
    _ = _ := congrArg ι (first_slot hG i p).symm

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveNormalCoordinates
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normal triple estimates imply the actual good phase and injective
differential in the plane coordinates used by the exact correction. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open RealModes JetPolynomial JetVelocityCoordinates SurfaceJetCoordinates

lemma primitiveNormalTriple_toEuclidean {G : JetPolynomial.Base → JetPolynomial.Space}
    (hG : ContDiff ℝ ∞ G) (p : JetPolynomial.Base) :
    primitiveNormalTriple (fun q => JetVelocityCoordinates.toEuclidean (G q)) p =
      ![slot 1 (lowJet G p),slot 2 (lowJet G p),slot 6 (lowJet G p)] := by
  have hy : (fun q => fderiv ℝ (fun r => JetVelocityCoordinates.toEuclidean (G r)) q
      (coordinateVector 1)) = fun q => JetVelocityCoordinates.toEuclidean (slot 2 (lowJet G q)) :=
    funext (euclidean_first_derivative hG 1)
  ext k a
  fin_cases k
  · change spaceCoordinates (fderiv ℝ (fun q => JetVelocityCoordinates.toEuclidean (G q)) p
      (coordinateVector 0)) a = _
    rw [euclidean_first_derivative hG]
    rfl
  · change spaceCoordinates (fderiv ℝ (fun q => JetVelocityCoordinates.toEuclidean (G q)) p
      (coordinateVector 1)) a = _
    rw [euclidean_first_derivative hG]
    rfl
  · change spaceCoordinates (fderiv ℝ
      (fun q => fderiv ℝ (fun r => JetVelocityCoordinates.toEuclidean (G r)) q
        (coordinateVector 1)) p (coordinateVector 1)) a = _
    rw [hy,euclidean_y_derivative hG]
    rfl

lemma primitiveNormalTriple_chart {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (p : JetPolynomial.Base) :
    primitiveNormalTriple (fun q => JetVelocityCoordinates.toEuclidean (F (baseEquiv q))) p =
      ![realTwoJet F (baseEquiv p) 0,realTwoJet F (baseEquiv p) 1,
        realTwoJet F (baseEquiv p) 4] := by
  have he := primitiveNormalTriple_toEuclidean (hF.comp baseEquiv.contDiff) p
  simp only [Function.comp_apply] at he
  rw [he]
  have hh := decode_lowJet hF p
  ext k a
  fin_cases k
  · exact congrArg (fun J : CollarVelocity.JetBase => J.2 0 a) hh
  · exact congrArg (fun J : CollarVelocity.JetBase => J.2 1 a) hh
  · exact congrArg (fun J : CollarVelocity.JetBase => J.2 4 a) hh

theorem good_phase_of_primitive_normal {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (p : JetPolynomial.Base)
    (hD :
      let H := primitiveNormalTriple
        (fun q => JetVelocityCoordinates.toEuclidean (F (baseEquiv q))) p
      NormalFrame.gramDet (H 0) (H 1) ≠ 0)
    (hB :
      let H := primitiveNormalTriple
        (fun q => JetVelocityCoordinates.toEuclidean (F (baseEquiv q))) p
      realNormalPart (H 0) (H 1) (H 2) ≠ 0) :
    Function.Injective (fderiv ℝ F (baseEquiv p)) ∧
      PhaseGeometry.Good (realSecondTensor F (baseEquiv p)) SmallModes.dx := by
  dsimp only at hD hB
  rw [primitiveNormalTriple_chart hF] at hD hB
  change realSecondForm F SmallModes.dy SmallModes.dy (baseEquiv p) ≠ 0 at hB
  refine ⟨injective_of_gramDet_ne_zero _ hD,?_,?_⟩
  · intro hz
    exact one_ne_zero (congrArg Prod.fst hz)
  · simpa [PhaseGeometry.secondQuadratic,realSecondTensor,SmallModes.dx,SmallModes.dy] using hB

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseNormalTripleMargin
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normal triple of the actual inverse-chart map controls the old
coordinate immersion and second form with a fixed compact-chart constant. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetVelocityCoordinates SurfaceVelocityFamily.Loop SurfaceJetCoordinates RealModes

lemma normalTriple_secondTensor_margin {F : SmallModes.Base → RealModes.RVec 4}
    (hF : ContDiff ℝ ∞ F) (p : JetPolynomial.Base) {c : ℝ}
    (hN : c < ‖realNormalPart
      (primitiveNormalTriple (fun q => JetVelocityCoordinates.toEuclidean (F (baseEquiv q))) p 0)
      (primitiveNormalTriple (fun q => JetVelocityCoordinates.toEuclidean (F (baseEquiv q))) p 1)
      (primitiveNormalTriple (fun q => JetVelocityCoordinates.toEuclidean (F (baseEquiv q))) p 2)‖) :
    c < ‖realSecondTensor F (baseEquiv p)‖ := by
  rw [primitiveNormalTriple_chart hF] at hN
  change c < ‖realSecondForm F SmallModes.dy SmallModes.dy (baseEquiv p)‖ at hN
  exact hN.trans_le (norm_le_pi_norm (realSecondTensor F (baseEquiv p)) (2 : Fin 3))

theorem compact_phase_normalTriple_margin
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {K : Set JetPolynomial.Base} (hK : IsCompact K) (hKS : K ⊆ e.source) :
    ∃ D : ℝ, 0 < D ∧ ∀ (H : JetPolynomial.Base → Space), ContDiff ℝ ∞ H →
      ∀ x ∈ K, ∀ c : ℝ, 0 < c →
        (let J := primitiveNormalTriple (H ∘ e.symm) (e x)
         NormalFrame.gramDet (J 0) (J 1) ≠ 0 ∧ c < ‖realNormalPart (J 0) (J 1) (J 2)‖) →
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ H ∘ planeCoordinateIsometry.symm)
          (planeCoordinateIsometry x)) ∧
        c/D < ‖realSecondTensor (spaceCoordinates ∘ H ∘ planeCoordinateIsometry.symm)
          (planeCoordinateIsometry x)‖ := by
  let er := realPhaseChart e
  have her := realPhaseChart_smooth e he
  have hir := realPhaseChart_symm_smooth e hi
  obtain ⟨D,hD,hd⟩ := PhaseGeometry.compact_phase_chart_normal_margin er her hir
    (hK.image planeCoordinateIsometry.continuous) (by
      rintro _ ⟨x,hx,rfl⟩
      change planeCoordinateIsometry.symm (planeCoordinateIsometry x) ∈ e.source
      simpa only [LinearIsometryEquiv.symm_apply_apply] using hKS hx)
  refine ⟨D,hD,?_⟩
  intro H hH x hx c hc hn
  let W := spaceCoordinates ∘ H ∘ planeCoordinateIsometry.symm
  let V := W ∘ er.symm
  have hW : ContDiff ℝ ∞ W := spaceCoordinates.contDiff.comp (hH.comp planeCoordinateIsometry.symm.contDiff)
  have hV : ContDiff ℝ ∞ V := hW.comp hir
  have hbase (q : JetPolynomial.Base) : baseEquiv q = planeCoordinateIsometry q := rfl
  have hrepr : (fun q => JetVelocityCoordinates.toEuclidean (V (baseEquiv q))) = H ∘ e.symm := by
    funext q
    simp only [V,W,er,hbase,realPhaseChart_symm_apply,Function.comp_apply,
      LinearIsometryEquiv.symm_apply_apply,JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.symm_apply_apply]
  have htriple := hn
  rw [← hrepr] at htriple
  have hgood := good_phase_of_primitive_normal hV (e x) htriple.1
    (norm_pos_iff.mp (hc.trans htriple.2))
  have hmargin := normalTriple_secondTensor_margin hV (e x) htriple.2
  rw [hbase] at hgood hmargin
  have hrel : ∀ y ∈ er.source, W y = V (er y) := by
    intro y hy
    change W y = W (er.symm (er y))
    rw [er.left_inv hy]
  have hout := hd W V hW hV hrel (planeCoordinateIsometry x) ⟨x,hx,rfl⟩
    (by simpa only [er,realPhaseChart_apply,LinearIsometryEquiv.symm_apply_apply] using hgood.1)
    c (by simpa only [er,realPhaseChart_apply,LinearIsometryEquiv.symm_apply_apply] using hmargin)
  exact hout

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasPhaseNormalMargin
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform phase-chart normal margins on a fixed smoothing-atlas patch. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes SurfaceVelocityFamily.Loop
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem phase_normal_margin_oai (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (hcover : (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ e.source) :
    ∃ D : ℝ, 0 < D ∧ ∀ (V : M → Space), ContMDiff planeModel spaceModel ∞ V →
      ∀ x ∈ (A.chartWeightCompact i : Set JetPolynomial.Base), ∀ c : ℝ, 0 < c →
        (let J := primitiveNormalTriple (A.vectorChartRead i V ∘ e.symm) (e x)
         NormalFrame.gramDet (J 0) (J 1) ≠ 0 ∧ c < ‖realNormalPart (J 0) (J 1) (J 2)‖) →
        Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i V)
          (planeCoordinateIsometry x)) ∧
        c/D < ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i V)
          (planeCoordinateIsometry x)‖ := by
  obtain ⟨D,hD,hd⟩ := compact_phase_normalTriple_margin e he hi
    (A.chartWeightCompact i).isCompact hcover
  refine ⟨D,hD,?_⟩
  intro V hV x hx c hc hn
  have hh := hd (A.vectorChartRead i V) (A.vectorChartRead_smooth i hV) x hx c hc hn
  have heq : spaceCoordinates ∘ A.vectorChartRead i V ∘ planeCoordinateIsometry.symm =
      spaceCoordinates ∘ A.vectorPlaneRead i V := rfl
  rwa [heq] at hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phase_normal_margin_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phase_normal_margin_oai.{u_1}
