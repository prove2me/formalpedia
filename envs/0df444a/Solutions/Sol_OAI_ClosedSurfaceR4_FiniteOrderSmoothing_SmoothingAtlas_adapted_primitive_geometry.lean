-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.adapted_primitive_geometry
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:32:16.281548+00:00
-- url     : https://prove2.me/submissions/7b11a571-91f2-4e33-affc-61738658c956

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI011
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_phase_gram_at_source

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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ChartModel
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
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

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricPullback
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
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
  [IsManifold planeModel ∞ M]

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

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_LocalPhaseData
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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SquarePartition
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open Set Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  {ι : Type*} [Fintype ι]




theorem exists_smooth_square_partition (U : ι → Set M) (hU : ∀ i, IsOpen (U i))
    (hcover : (Set.univ : Set M) ⊆ ⋃ i, U i) :
    ∃ ψ : ι → M → ℝ,
      (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (ψ i)) ∧
      (∀ i, tsupport (ψ i) ⊆ U i) ∧
      (∀ i, HasCompactSupport (ψ i)) ∧
      (∀ i p, 0 ≤ ψ i p) ∧ (∀ p, ∑ i, (ψ i p)^2 = 1) := by
  classical
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, E) isClosed_univ U hU hcover
  let σ : M → ℝ := fun p => ∑ i, (ρ i p)^2
  have hsum (p : M) : ∑ i, ρ i p = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ p)
  have hσ (p : M) : 0 < σ p := by
    have hnon : 0 ≤ σ p := Finset.sum_nonneg (fun i _ => sq_nonneg (ρ i p))
    by_contra hn
    have hz : σ p = 0 := le_antisymm (not_lt.mp hn) hnon
    have hi : ∀ i, ρ i p = 0 := by
      intro i
      have hs := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_ : j ∈ Finset.univ) => sq_nonneg (ρ j p))).mp hz i (Finset.mem_univ i)
      exact sq_eq_zero_iff.mp hs
    have hf := hsum p
    simp only [hi, Finset.sum_const_zero] at hf
    norm_num at hf
  have hsmoothσ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ σ := by
    exact contMDiff_finsetSum (fun i _ => (ρ i).contMDiff.pow 2)
  have hsmoothsqrt : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun p => Real.sqrt (σ p)) := by
    intro p
    exact (Real.contDiffAt_sqrt (hσ p).ne').contMDiffAt.comp p (hsmoothσ p)
  let ψ : ι → M → ℝ := fun i p => ρ i p / Real.sqrt (σ p)
  have hψsupp (i : ι) : tsupport (ψ i) ⊆ tsupport (ρ i) := by
    apply closure_mono
    intro p hp
    simp only [Function.mem_support] at hp ⊢
    exact fun hn => hp (by simp [ψ, hn])
  refine ⟨ψ, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (ρ i).contMDiff.div₀ hsmoothsqrt (fun p => (Real.sqrt_pos.mpr (hσ p)).ne')
  · intro i
    exact (hψsupp i).trans (hρ i)
  · intro i
    exact (isClosed_tsupport (ψ i)).isCompact
  · intro i p
    exact div_nonneg (ρ.nonneg i p) (Real.sqrt_nonneg _)
  · intro p
    calc
      ∑ i, (ψ i p)^2 = (∑ i, (ρ i p)^2) / (Real.sqrt (σ p))^2 := by
        simp only [ψ, div_pow, Finset.sum_div]
      _ = σ p / σ p := by rw [Real.sq_sqrt (hσ p).le]
      _ = 1 := div_self (hσ p).ne'

end ClosedSurfaceR4.PhaseGeometry

namespace ClosedSurfaceR4.PhaseGeometry
open Set Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]



theorem exists_finite_smooth_square_partition (U : M → Set M)
    (hU : ∀ p, IsOpen (U p)) (hp : ∀ p, p ∈ U p) :
    ∃ (t : Finset M) (ψ : t → M → ℝ),
      (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (ψ i)) ∧
      (∀ i, tsupport (ψ i) ⊆ U i) ∧
      (∀ i, HasCompactSupport (ψ i)) ∧
      (∀ i p, 0 ≤ ψ i p) ∧ (∀ p, ∑ i, (ψ i p)^2 = 1) := by
  classical
  have hc : (univ : Set M) ⊆ ⋃ p, U p := fun p _ => mem_iUnion.mpr ⟨p, hp p⟩
  obtain ⟨t,ht⟩ := isCompact_univ.elim_finite_subcover U hU hc
  have hct : (univ : Set M) ⊆ ⋃ i : t, U i := by
    intro p _
    obtain ⟨i,hi,hpi⟩ := mem_iUnion₂.mp (ht (mem_univ p))
    exact mem_iUnion.mpr ⟨⟨i,hi⟩,hpi⟩
  obtain ⟨ψ,hψ⟩ := exists_smooth_square_partition (E := E) (fun i : t => U i)
    (fun i => hU i) hct
  exact ⟨t,ψ,hψ⟩

end ClosedSurfaceR4.PhaseGeometry

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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ProjectionBounds
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
open SmallModes Set Metric

lemma contDiff_gram_pair : ContDiff ℝ ∞ (fun p : TangentPair => NormalFrame.gramDet p.1 p.2) := by
  unfold NormalFrame.gramDet dotProduct
  fun_prop

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricBounds
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

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_Main
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
open SmallModes RealModes PhaseGeometry Set Bundle Manifold Filter


variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]



theorem IsSmoothIsometricImmersion.mfderiv_injective {g : SmoothMetric M}
    {F : M → Space} (h : IsSmoothIsometricImmersion M g F) (p : M) :
    Function.Injective (mfderiv planeModel spaceModel F p) := by
  intro v w hvw
  apply sub_eq_zero.mp
  by_contra hne
  have hv : mfderiv planeModel spaceModel F p (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  have hinner := h.2 p (v - w) (v - w)
  rw [hv, inner_zero_left] at hinner
  exact (ne_of_gt (g.pos p (v - w) hne)) hinner.symm



end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasImmersionGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local good-phase geometry in any covering chart gives the intrinsic
immersion and nonzero second-form hypotheses for the next primitive. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology Matrix
namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma coordinateMap_injective_of_immersion {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hI : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p))
    (q : M) {x : SmallModes.Base} (hx : x ∈ coordinateDomain q) :
    Function.Injective (fderiv ℝ (coordinateMap F q) x) := by
  have hi := ((coordinateInverse_smoothOn q) x hx).contMDiffAt
    ((coordinateDomain_open q).mem_nhds hx)
  have hm := (hF (coordinateInverse q x)).mdifferentiableAt (by simp)
  have hic := hi.mdifferentiableAt (by simp)
  have hd := mfderiv_comp x hm hic
  rw [mfderiv_eq_fderiv] at hd
  have hs : DifferentiableAt ℝ (F ∘ coordinateInverse q) x :=
    (hm.comp x hic).differentiableAt
  change Function.Injective (fderiv ℝ (spaceCoordinates ∘ (F ∘ coordinateInverse q)) x)
  rw [fderiv_comp x spaceCoordinates.differentiableAt hs,spaceCoordinates.fderiv,hd]
  exact spaceCoordinates.injective.comp ((hI _).comp (coordinateInverse_mfderiv_injective q hx))

end ClosedSurfaceR4

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothPhaseChart
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A noncritical smooth phase is the first coordinate of a smooth local chart. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

lemma phaseLinear_phaseDerivative (φ : Base → ℝ) (p : Base) :
    phaseLinear (phaseDerivative φ p) = fderiv ℝ φ p := by
  apply ContinuousLinearMap.ext
  intro v
  have he : v = v.1 • dx + v.2 • dy := by ext <;> simp [dx,dy]
  conv_rhs => rw [he]
  simp only [map_add,map_smul,smul_eq_mul,phaseLinear_apply,phaseDerivative]
  ring

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ConvexQuadraticPhase
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual convex phases used in finite primitive preparation. Their
coordinate covariant Hessians are uniformly positive on a sufficiently
small disk when the metric connection has a fixed bound. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

lemma convexQuadraticPhase_hasFDerivAt (ell : Base) (L : ℝ) (p : Base) :
    HasFDerivAt (convexQuadraticPhase ell L) (phaseLinear (ell + L • p)) p := by
  have h1 := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := p)
  have h2 := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x := p)
  have hh := (phaseLinear ell).hasFDerivAt (x := p) |>.add
    (((h1.pow 2).add (h2.pow 2)).const_mul (L / 2))
  apply hh.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [add_apply, smul_apply, phaseLinear_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    two_smul, smul_eq_mul]
  ring

lemma convexQuadraticPhase_coordDeriv (ell : Base) (L : ℝ) (p v : Base) :
    coordDeriv v (convexQuadraticPhase ell L) p = phaseLinear (ell + L • p) v := by
  exact congrArg (fun f : Base →L[ℝ] ℝ => f v)
    (convexQuadraticPhase_hasFDerivAt ell L p).fderiv

lemma convexQuadraticPhase_phaseDerivative (ell : Base) (L : ℝ) (p : Base) :
    phaseDerivative (convexQuadraticPhase ell L) p = ell + L • p := by
  unfold phaseDerivative
  rw [(convexQuadraticPhase_hasFDerivAt ell L p).fderiv]
  ext <;> simp [phaseLinear_apply, dx, dy]

lemma convexQuadraticPhase_second (ell : Base) (L : ℝ) (p v w : Base) :
    coordDeriv v (coordDeriv w (convexQuadraticPhase ell L)) p =
      L * (v.1*w.1 + v.2*w.2) := by
  have he : coordDeriv w (convexQuadraticPhase ell L) =
      fun p => phaseLinear ell w + L * phaseLinear w p := by
    funext q
    rw [convexQuadraticPhase_coordDeriv]
    simp only [phaseLinear_apply, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    ring
  rw [he]
  have hh := (hasFDerivAt_const (phaseLinear ell w) p).add
    ((phaseLinear w).hasFDerivAt (x := p) |>.const_mul L)
  change (fderiv ℝ ((fun _ : Base => phaseLinear ell w) +
    fun p => L * phaseLinear w p) p) v = _
  rw [hh.fderiv]
  simp only [smul_apply, smul_eq_mul, zero_add, phaseLinear_apply]
  ring

lemma convexQuadraticPhase_hessian (h : Base → PhaseMean.Tensor) (ell : Base) (L : ℝ)
    (p v w : Base) :
    coordinateMetricHessian h (convexQuadraticPhase ell L) p v w =
      L * (v.1*w.1 + v.2*w.2) - phaseLinear (ell + L • p)
        (connectionContract (metricConnectionAt (h p,fderiv ℝ h p)) v w) := by
  rw [coordinateMetricHessian, convexQuadraticPhase_second,
    convexQuadraticPhase_phaseDerivative]

lemma coordinateMetricHessian_fst_dy (h : Base → PhaseMean.Tensor) (p : Base) :
    coordinateMetricHessian h (Prod.fst : Base → ℝ) p dy dy =
      -(metricConnectionAt (h p,fderiv ℝ h p) 2).1 := by
  have he : convexQuadraticPhase dx 0 = (Prod.fst : Base → ℝ) := by
    funext q
    simp [convexQuadraticPhase, phaseLinear_apply, dx]
  have hh := convexQuadraticPhase_hessian h dx 0 p dy dy
  rw [he] at hh
  simpa [connectionContract, phaseLinear_apply, dx, dy] using hh

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CircularSmoothingAtlas
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite smoothing atlas whose positive loci are actual coordinate disks.
The cutoffs are flat circular functions, not arbitrary subordinate bumps. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

variable [IsManifold planeModel ∞ M]

variable [T2Space M]

variable [CompactSpace M]

omit [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M] in
theorem normalize_finite_positive_cutoffs {ι : Type*} [Fintype ι]
    (f : ι → M → ℝ) (hf : ∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (f i))
    (hnon : ∀ i x, 0 ≤ f i x) (hcover : ∀ x, ∃ i, 0 < f i x) :
    ∃ w : ι → M → ℝ,
      (∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (w i)) ∧
      (∀ i x, 0 ≤ w i x) ∧ (∀ i x, 0 < w i x ↔ 0 < f i x) ∧
      (∀ i, tsupport (w i) = tsupport (f i)) ∧
      ∀ x, ∑ i, (w i x)^2 = 1 := by
  classical
  let sigma : M → ℝ := fun x => ∑ i, (f i x)^2
  have hpos (x : M) : 0 < sigma x := by
    obtain ⟨i,hi⟩ := hcover x
    exact (sq_pos_of_pos hi).trans_le
      (Finset.single_le_sum (fun j _ => sq_nonneg (f j x)) (Finset.mem_univ i))
  have hsigma : ContMDiff planeModel 𝓘(ℝ) ∞ sigma :=
    contMDiff_finsetSum (fun i _ => (hf i).pow 2)
  have hsqrt : ContMDiff planeModel 𝓘(ℝ) ∞ (fun x => Real.sqrt (sigma x)) := by
    intro x
    exact (Real.contDiffAt_sqrt (hpos x).ne').contMDiffAt.comp x (hsigma x)
  let w : ι → M → ℝ := fun i x => f i x / Real.sqrt (sigma x)
  have hwpos (i : ι) (x : M) : 0 < w i x ↔ 0 < f i x :=
    div_pos_iff_of_pos_right (Real.sqrt_pos.mpr (hpos x))
  refine ⟨w,fun i => (hf i).div₀ hsqrt (fun x => (Real.sqrt_pos.mpr (hpos x)).ne'),
    fun i x => div_nonneg (hnon i x) (Real.sqrt_nonneg _),hwpos,?_,?_⟩
  · intro i
    change closure (Function.support (w i)) = closure (Function.support (f i))
    congr 1
    ext x
    change w i x ≠ 0 ↔ f i x ≠ 0
    change f i x / Real.sqrt (sigma x) ≠ 0 ↔ f i x ≠ 0
    rw [div_ne_zero_iff]
    exact and_iff_left (Real.sqrt_pos.mpr (hpos x)).ne'
  · intro x
    calc
      ∑ i, (w i x)^2 = (∑ i, (f i x)^2) / (Real.sqrt (sigma x))^2 := by
        simp only [w,div_pow,Finset.sum_div]
      _ = sigma x / sigma x := by rw [Real.sq_sqrt (hpos x).le]
      _ = 1 := div_self (hpos x).ne'

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PrescribedAtlasPatch
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed compact primitive disk can be placed in one positive atlas
patch with support in any prescribed coordinate neighborhood. -/
noncomputable section
open Set Function Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem exists_smoothingAtlas_prescribed_patch (q : M) {K U : Set M}
    (hK : IsCompact K) (hqK : q ∈ K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hUs : U ⊆ (chart q).source) :
    ∃ (A : SmoothingAtlas M) (i : A.centers), (i : M) = q ∧
      (∀ p ∈ K, 0 < A.weight i p) ∧ tsupport (A.weight i) ⊆ U ∧
      (∀ j p, 0 ≤ A.weight j p) ∧
      ∀ j p, p ∈ tsupport (A.weight j) → A.outer j =ᶠ[𝓝 p] (fun _ => 1) := by
  classical
  let V : M → Set M := fun p => if p = q then U else (chart p).source \ {q}
  have hV : ∀ p, IsOpen (V p) := by
    intro p
    by_cases hp : p = q
    · simpa only [V,ite_eq_left hp] using hU
    · simpa only [V,ite_eq_right hp] using (chart p).open_source.sdiff isClosed_singleton
  have hpV : ∀ p, p ∈ V p := by
    intro p
    by_cases hp : p = q
    · subst p; simpa only [V,ite_eq_left rfl] using hKU hqK
    · simp only [V,ite_eq_right hp,mem_sdiff,mem_singleton_iff]
      exact ⟨by rw [chart_source]; exact mem_chart_source Plane p,hp⟩
  obtain ⟨t,ψ,hψ,hsupp,_,hnon,hpart⟩ := exists_finite_smooth_square_partition
    (E := Plane) V hV hpV
  have hψ : ∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (ψ i) := by
    intro i
    simpa only [planeModel] using hψ i
  have hqt : q ∈ t := by
    by_contra hnot
    have hz (i : t) : ψ i q = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hh
      have hi : (i : M) ≠ q := fun he => hnot (he ▸ i.2)
      have hm := hsupp i hh
      simp only [V,ite_eq_right hi,mem_sdiff,mem_singleton_iff] at hm
      exact hm.2 trivial
    have he := hpart q
    simp only [hz,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero] at he
    norm_num at he
  let iq : t := ⟨q,hqt⟩
  obtain ⟨W,hW,hKW,hWU⟩ := hK.exists_isOpen_closure_subset (hU.mem_nhdsSet.mpr hKU)
  obtain ⟨β,hβ,_,hβs,hβone⟩ := exists_contMDiff_support_eq_eq_one_iff
    (I := planeModel) (n := (⊤ : ℕ∞)) hW hK.isClosed hKW
  have hβU : tsupport β ⊆ U := by
    change closure (support β) ⊆ U
    rw [hβs]
    exact hWU
  let f : t → M → ℝ := fun i p => ψ i p + if i = iq then (β p)^2 else 0
  have hf : ∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (f i) := by
    intro i
    by_cases hi : i = iq
    · have heq : f i = ψ i + fun p => (β p)^2 := by
        funext p; simp only [f,ite_eq_left hi,Pi.add_apply]
      rw [heq]
      exact (hψ i).add (hβ.pow 2)
    · simpa only [f,ite_eq_right hi,add_zero] using hψ i
  have hfnon : ∀ i p, 0 ≤ f i p := by
    intro i p
    exact add_nonneg (hnon i p) (by split_ifs <;> positivity)
  have hfle : ∀ i p, ψ i p ≤ f i p := by
    intro i p
    exact le_add_of_nonneg_right (by split_ifs <;> positivity)
  have hfcover (p : M) : ∃ i, 0 < f i p := by
    by_contra hh
    have hz : ∀ i, ψ i p = 0 := by
      intro i
      have hni : ¬ 0 < f i p := fun h => hh ⟨i,h⟩
      exact le_antisymm ((hfle i p).trans (le_of_not_gt hni)) (hnon i p)
    have hp := hpart p
    simp only [hz,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero] at hp
    norm_num at hp
  have hfV : ∀ i, tsupport (f i) ⊆ V i := by
    intro i
    by_cases hi : i = iq
    · subst i
      have hs : tsupport (f iq) ⊆ tsupport (ψ iq) ∪ tsupport β := by
        have heq : f iq = ψ iq + fun p => (β p)^2 := by
          funext p; simp [f]
        rw [heq]
        exact (tsupport_add _ _).trans (union_subset_union_right _ (show tsupport (fun p => (β p)^2) ⊆ tsupport β from by
          apply closure_mono
          intro p hp
          exact fun hz => hp (by change (β p)^2 = 0; rw [hz,zero_pow (by decide : 2 ≠ 0)])))
      apply hs.trans
      apply union_subset (hsupp iq)
      simpa only [V,show (iq : M) = q from rfl,ite_eq_left rfl] using hβU
    · simpa only [f,ite_eq_right hi,add_zero] using hsupp i
  obtain ⟨w,hw,hwnon,hwpos,hwsupp,hwsum⟩ := normalize_finite_positive_cutoffs f hf hfnon hfcover
  have hwV (i : t) : tsupport (w i) ⊆ V i := by rw [hwsupp]; exact hfV i
  have hwchart (i : t) : tsupport (w i) ⊆ (chart (i : M)).source := by
    intro p hp
    have hv := hwV i hp
    by_cases hi : (i : M) = q
    · have hu : p ∈ U := by simpa only [V,ite_eq_left hi] using hv
      simpa only [hi] using hUs hu
    · have hh : p ∈ (chart (i : M)).source ∧ p ∉ ({q} : Set M) := by
        simpa only [V,ite_eq_right hi,mem_sdiff] using hv
      exact hh.1
  have hout : ∀ i : t, ∃ chi : M → ℝ,
      ContMDiff planeModel 𝓘(ℝ) ∞ chi ∧ tsupport chi ⊆ (chart (i : M)).source ∧
      ∀ p ∈ tsupport (w i), chi =ᶠ[𝓝 p] (fun _ => 1) := by
    intro i
    have hc : IsCompact (tsupport (w i)) := (isClosed_tsupport _).isCompact
    obtain ⟨B,hB,hKB,hBc⟩ := hc.exists_isOpen_closure_subset
      ((chart (i : M)).open_source.mem_nhdsSet.mpr (hwchart i))
    obtain ⟨O,hO,hKO,hOc⟩ := hc.exists_isOpen_closure_subset (hB.mem_nhdsSet.mpr hKB)
    obtain ⟨chi,hchi,_,hchis,hchione⟩ := exists_contMDiff_support_eq_eq_one_iff
      (I := planeModel) (n := (⊤ : ℕ∞)) hB isClosed_closure hOc
    refine ⟨chi,hchi,?_,?_⟩
    · change closure (support chi) ⊆ _
      rw [hchis]
      exact hBc
    · intro p hp
      filter_upwards [hO.mem_nhds (hKO hp)] with y hy
      exact (hchione y).mp (subset_closure hy)
  choose chi hchi hchis hchione using hout
  let A : SmoothingAtlas M :=
    ⟨t,w,chi,hw,hwchart,hchi,hchis,fun i p hp => (hchione i p hp).eq_of_nhds,hwsum⟩
  refine ⟨A,iq,rfl,?_,?_,hwnon,hchione⟩
  · intro p hp
    apply (hwpos iq p).mpr
    change 0 < ψ iq p + if iq = iq then (β p)^2 else 0
    rw [ite_eq_left rfl,(hβone p).mp hp]
    linarith [hnon iq p]
  · simpa only [V,show (iq : M) = q from rfl,ite_eq_left rfl] using hwV iq

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasOuterPlateau
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Enlarge one outer cutoff's plateau without changing any partition
weight or coordinate chart. -/
noncomputable section
open Set Filter Function Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem enlarge_outer_plateau (i : A.centers) {K : Set M}
    (hK : IsCompact K) (hKs : K ⊆ (chart (i : M)).source)
    (houter : ∀ j p, p ∈ tsupport (A.weight j) → A.outer j =ᶠ[𝓝 p] (fun _ => 1)) :
    ∃ B : SmoothingAtlas M, ∃ hcenters : B.centers = A.centers,
      (∀ j p, B.weight (hcenters.symm ▸ j) p = A.weight j p) ∧
      (∀ j p, p ∈ tsupport (B.weight j) → B.outer j =ᶠ[𝓝 p] (fun _ => 1)) ∧
      ∀ p ∈ K, B.outer (hcenters.symm ▸ i) =ᶠ[𝓝 p] (fun _ => 1) := by
  classical
  obtain ⟨W,hW,hKW,hWs⟩ := hK.exists_isOpen_closure_subset
    ((chart (i : M)).open_source.mem_nhdsSet.mpr hKs)
  obtain ⟨O,hO,hKO,hOW⟩ := hK.exists_isOpen_closure_subset (hW.mem_nhdsSet.mpr hKW)
  obtain ⟨β,hβ,_,hβs,hβone⟩ := exists_contMDiff_support_eq_eq_one_iff
    (I := planeModel) (n := (⊤ : ℕ∞)) hW isClosed_closure hOW
  have hβsupport : tsupport β ⊆ (chart (i : M)).source := by
    change closure (support β) ⊆ _
    rw [hβs]
    exact hWs
  have hβgerm : ∀ p ∈ K, β =ᶠ[𝓝 p] (fun _ => 1) := by
    intro p hp
    filter_upwards [hO.mem_nhds (hKO hp)] with y hy
    exact (hβone y).mp (subset_closure hy)
  let outer : A.centers → M → ℝ := fun j =>
    if j = i then fun p => A.outer j p + β p - A.outer j p * β p else A.outer j
  have hsmooth (j : A.centers) : ContMDiff planeModel 𝓘(ℝ) ∞ (outer j) := by
    by_cases hj : j = i
    · have he : outer j = (A.outer j + β) - A.outer j * β := by funext p; simp [outer,hj]
      rw [he]
      exact ((A.outer_smooth j).add hβ).sub ((A.outer_smooth j).mul hβ)
    · simpa only [outer,ite_eq_right hj] using A.outer_smooth j
  have hsupp (j : A.centers) : tsupport (outer j) ⊆ (chart (j : M)).source := by
    by_cases hj : j = i
    · subst j
      apply subset_trans (b := tsupport (A.outer i) ∪ tsupport β) ?_
        (union_subset (A.outer_support i) hβsupport)
      apply closure_minimal _ ((isClosed_tsupport (A.outer i)).union (isClosed_tsupport β))
      · intro p hp
        by_contra hh
        have ho : A.outer i p = 0 := image_eq_zero_of_notMem_tsupport (fun ho => hh (Or.inl ho))
        have hb : β p = 0 := image_eq_zero_of_notMem_tsupport (fun hb => hh (Or.inr hb))
        apply hp
        simp [outer,ho,hb]
    · simpa only [outer,ite_eq_right hj] using A.outer_support j
  have hgerm (j : A.centers) (p : M) (hp : p ∈ tsupport (A.weight j)) :
      outer j =ᶠ[𝓝 p] (fun _ => 1) := by
    filter_upwards [houter j p hp] with x hx
    by_cases hj : j = i
    · subst j; simp [outer,hx]
    · simp [outer,hj,hx]
  let B : SmoothingAtlas M := ⟨A.centers,A.weight,outer,A.weight_smooth,A.weight_support,
    hsmooth,hsupp,fun j p hp => (hgerm j p hp).eq_of_nhds,A.partition⟩
  refine ⟨B,rfl,fun _ _ => rfl,hgerm,?_⟩
  intro p hp
  filter_upwards [hβgerm p hp] with x hx
  change outer i x = 1
  simp [outer,hx]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RealMetricDerivatives
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityFrame
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth orthonormal frames obtained by interpolating non-antipodal plane directions. -/
noncomputable section
open scoped Matrix ContDiff

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma normalize_smoothAt {v : E → Vec} {x : E} (hv : ContDiffAt ℝ ∞ v x) (hn : v x ≠ 0) :
    ContDiffAt ℝ ∞ (fun z => normalize (v z)) x := by
  have hd : ContDiffAt ℝ ∞ (fun z => v z ⬝ᵥ v z) x :=
    ContDiffAt.sum (fun i _ => (contDiffAt_pi.mp hv i).mul (contDiffAt_pi.mp hv i))
  have hp := dot_self_pos hn
  exact ((hd.sqrt hp.ne').inv (Real.sqrt_pos.mpr hp).ne').smul hv

end ClosedSurfaceR4.VelocityFrame

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

lemma surfacePhaseChart_symm_smooth (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) :
    ContMDiffOn 𝓘(ℝ,SmallModes.Base) planeModel ∞ (surfacePhaseChart q e).symm
      (surfacePhaseChart q e).target := by
  exact (FiniteOrderSmoothing.chart_symm_smooth q).comp
    (hi.comp baseEquiv.symm.contDiff).contMDiff.contMDiffOn (fun _ hx => hx.2)

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CompactPhaseDiskTopology
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact primitive disks and their boundaries in the actual phase chart. -/
noncomputable section
open Set Filter Manifold
open scoped Topology
namespace ClosedSurfaceR4
open SmallModes
variable {M : Type*} [TopologicalSpace M]

lemma compact_phase_disk_geometry (E : OpenPartialHomeomorph M Base)
    {D : Set M} (hD : IsOpen D) (hK : IsCompact (closure D))
    (hS : closure D ⊆ E.source) :
    IsOpen (E '' D) ∧ closure (E '' D) = E '' closure D ∧
      frontier (E '' D) = E '' frontier D ∧ IsCompact (closure (E '' D)) := by
  have hSD : D ⊆ E.source := subset_trans subset_closure hS
  have hI : E.IsImage D (E '' D) := by
    intro p hp
    constructor
    · rintro ⟨q,hq,he⟩
      have hqp := E.injOn (hSD hq) hp he
      exact hqp ▸ hq
    · exact fun hpD => ⟨p,hpD,rfl⟩
  have hIE : E.target ∩ E '' D = E '' D := inter_eq_right.mpr (by
    rintro _ ⟨p,hp,rfl⟩
    exact E.map_source (hSD hp))
  have hO : IsOpen (E '' D) := by
    rw [← hIE]
    exact hI.isOpen_iff.mp (E.open_source.inter hD)
  have hC : IsCompact (E '' closure D) := hK.image_of_continuousOn (E.continuousOn.mono hS)
  have hc : closure (E '' D) = E '' closure D := by
    apply Subset.antisymm
    · exact closure_minimal (image_mono subset_closure) hC.isClosed
    · rintro _ ⟨p,hp,rfl⟩
      exact (hI.closure (hS hp)).mpr hp
  have hf : frontier (E '' D) = E '' frontier D := by
    rw [frontier,hO.interior_eq,hc,frontier,hD.interior_eq]
    ext y
    constructor
    · rintro ⟨⟨p,hp,rfl⟩,hn⟩
      exact ⟨p,⟨hp,fun hpD => hn ⟨p,hpD,rfl⟩⟩,rfl⟩
    · rintro ⟨p,⟨hp,hn⟩,rfl⟩
      refine ⟨⟨p,hp,rfl⟩,?_⟩
      rintro ⟨q,hq,he⟩
      have hqp := E.injOn (hSD hq) (hS hp) he
      exact hn (hqp ▸ hq)
  exact ⟨hO,hc,hf,hc ▸ hC⟩

lemma compact_phase_boundary_neighborhood {D Ω G : Set Base}
    (hD : IsOpen D) (hK : IsCompact (closure D))
    (hΩ : IsOpen Ω) (hDΩ : closure D ⊆ Ω)
    (hG : IsOpen G) (hDG : frontier D ⊆ G) :
    ∃ V : Set Base, IsOpen V ∧ IsCompact (closure V) ∧ closure D ⊆ V ∧
      closure V ⊆ Ω ∧ closure V \ D ⊆ G := by
  have hcover : closure D ⊆ Ω ∩ (D ∪ G) := by
    intro p hp
    refine ⟨hDΩ hp,?_⟩
    by_cases hi : p ∈ D
    · exact Or.inl hi
    · exact Or.inr (hDG ⟨hp,by simpa only [hD.interior_eq] using hi⟩)
  obtain ⟨V,hV,hKV,hVG⟩ := hK.exists_isOpen_closure_subset
    ((hΩ.inter (hD.union hG)).mem_nhdsSet.mpr hcover)
  obtain ⟨B,hB,hKB,hBc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  let W := V ∩ B
  have hWV : closure W ⊆ closure V := closure_mono inter_subset_left
  have hWB : closure W ⊆ closure B := closure_mono inter_subset_right
  refine ⟨W,hV.inter hB,hBc.of_isClosed_subset isClosed_closure hWB,
    fun p hp => ⟨hKV hp,hKB hp⟩,fun p hp => (hVG (hWV hp)).1,?_⟩
  intro p hp
  exact (hVG (hWV hp.1)).2.resolve_left hp.2

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseChartGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SecondFormNormalFields
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth fields of actual second forms and their preferred unit normal. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

lemma realSecondForm_smoothOn {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {U : Set Base}
    (hD : ∀ x ∈ U, gramDet (coordDeriv dx F x) (coordDeriv dy F x) ≠ 0)
    (v w : Base) : ContDiffOn ℝ ∞ (realSecondForm F v w) U := by
  intro x hx
  exact (contDiffAt_realNormalPart
    (contDiff_real_coordDeriv hF dx).contDiffAt
    (contDiff_real_coordDeriv hF dy).contDiffAt
    (contDiff_real_coordDeriv (contDiff_real_coordDeriv hF w) v).contDiffAt
    (hD x hx)).contDiffWithinAt

lemma realBoundaryProfile_smooth {F : RField 4} (hF : ContDiff ℝ ∞ F) (z : ℝ) :
    ContDiff ℝ ∞ (realBoundaryProfile F z) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_real_coordDeriv hF dx
  · exact contDiff_real_coordDeriv hF dy
  · exact contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dy
  · exact contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dx
  · exact (contDiff_const : ContDiff ℝ ∞ (fun _ : Base => z)).smul (contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dx) dx)

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_BoundaryJetSecondForm
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unscaled five-jets encode the actual second form and ordered crossings.
These expressions are used for exterior C2 stability. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

lemma boundaryJetSecond_actual {F : RField 4} (hF : ContDiff ℝ ∞ F) (p v w : Base) :
    boundaryJetSecond (realBoundaryProfile F 1 p) v w = realSecondForm F v w p := by
  unfold boundaryJetSecond realBoundaryProfile realSecondForm
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.cons_val_four,Matrix.head_cons,Matrix.tail_cons,one_smul]
  rw [second_coordDeriv_bilinear hF v w p]

lemma boundaryJetCrossing_actual {F : RField 4} (hF : ContDiff ℝ ∞ F) (p v w : Base) (κ : ℝ) :
    boundaryJetCrossing (realBoundaryProfile F 1 p) v w κ = orderedCrossing F v w p κ := by
  unfold boundaryJetCrossing orderedCrossing
  rw [boundaryJetSecond_actual hF,boundaryJetSecond_actual hF]
  simp only [realBoundaryProfile,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [← coordDeriv_eq_basis F v,← coordDeriv_eq_basis F w]

lemma continuousAt_boundaryJetSecond {J : BoundaryProfile} (v w : Base)
    (hD : NormalFrame.gramDet (J 0) (J 1) ≠ 0) :
    ContinuousAt (fun a : BoundaryProfile × (Base × Base) => boundaryJetSecond a.1 a.2.1 a.2.2)
      (J,v,w) := by
  have h0 : ContDiff ℝ ∞ (fun a : BoundaryProfile × (Base × Base) => a.1 0) :=
    (ContinuousLinearMap.proj 0 : BoundaryProfile →L[ℝ] Vec).contDiff.comp contDiff_fst
  have h1 : ContDiff ℝ ∞ (fun a : BoundaryProfile × (Base × Base) => a.1 1) :=
    (ContinuousLinearMap.proj 1 : BoundaryProfile →L[ℝ] Vec).contDiff.comp contDiff_fst
  have h2 : ContDiff ℝ ∞ (fun a : BoundaryProfile × (Base × Base) =>
      (a.2.1.1*a.2.2.1) • a.1 4+(a.2.1.1*a.2.2.2+a.2.1.2*a.2.2.1) • a.1 3+
        (a.2.1.2*a.2.2.2) • a.1 2) := by fun_prop
  exact (contDiffAt_realNormalPart h0.contDiffAt h1.contDiffAt h2.contDiffAt hD).continuousAt

lemma continuousAt_boundaryJetCrossing {J : BoundaryProfile} {v w : Base} {κ : ℝ}
    (hD : NormalFrame.gramDet (J 0) (J 1) ≠ 0) (hP : boundaryJetSecond J v v ≠ 0) :
    ContinuousAt (fun a : BoundaryProfile × (Base × (Base × ℝ)) =>
      boundaryJetCrossing a.1 a.2.1 a.2.2.1 a.2.2.2) (J,v,w,κ) := by
  let Z := BoundaryProfile × (Base × (Base × ℝ))
  have hm : Continuous (fun a : Z => (a.1,a.2.1,a.2.2.1)) := by fun_prop
  have hp : Continuous (fun a : Z => (a.1,a.2.1,a.2.1)) := by fun_prop
  have hM := (continuousAt_boundaryJetSecond v w hD).comp
    (f := fun a : Z => (a.1,a.2.1,a.2.2.1)) (x := (J,v,w,κ)) hm.continuousAt
  have hV := (continuousAt_boundaryJetSecond v v hD).comp
    (f := fun a : Z => (a.1,a.2.1,a.2.1)) (x := (J,v,w,κ)) hp.continuousAt
  have hn := (normalize_smoothAt contDiffAt_id hP).continuousAt.comp
    (f := fun a : Z => boundaryJetSecond a.1 a.2.1 a.2.1) (x := (J,v,w,κ)) hV
  have hdot : ContinuousAt (fun a : Z => boundaryJetSecond a.1 a.2.1 a.2.2.1 ⬝ᵥ
      normalize (boundaryJetSecond a.1 a.2.1 a.2.1)) (J,v,w,κ) := by
    have hd : Continuous (fun p : Vec × Vec => p.1 ⬝ᵥ p.2) := by
      unfold dotProduct
      fun_prop
    exact hd.continuousAt.comp (f := fun a : Z =>
      (boundaryJetSecond a.1 a.2.1 a.2.2.1,normalize (boundaryJetSecond a.1 a.2.1 a.2.1)))
      (x := (J,v,w,κ)) (hM.prodMk hn)
  have hgram : Continuous (fun a : Z => a.2.2.2*
      NormalFrame.gramDet (a.2.1.1 • a.1 0+a.2.1.2 • a.1 1) (a.2.2.1.1 • a.1 0+a.2.2.1.2 • a.1 1)) := by
    have hp : Continuous (fun a : Z =>
        (a.2.1.1 • a.1 0+a.2.1.2 • a.1 1,a.2.2.1.1 • a.1 0+a.2.2.1.2 • a.1 1)) := by
      dsimp [Z]
      fun_prop
    exact (show Continuous (fun a : Z => a.2.2.2) by fun_prop).mul
      (contDiff_gram_pair.continuous.comp hp)
  exact (hdot.pow 2).add hgram.continuousAt

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_BoundaryJetCurvature
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The induced Gaussian curvature is a continuous function of the unscaled
second jet on the immersion locus. This controls the new curvature in exterior estimates. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame

lemma boundaryJetCurvature_actual {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : Base)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0) :
    boundaryJetCurvature (realBoundaryProfile F 1 p) =
      coordinateGaussianCurvature (realMetric F dx dx) (realMetric F dx dy)
        (realMetric F dy dy) p := by
  unfold boundaryJetCurvature
  rw [boundaryJetSecond_actual hF,boundaryJetSecond_actual hF,boundaryJetSecond_actual hF,
    gauss_metric_identity hF p hD]
  rfl

lemma continuousAt_boundaryJetCurvature {J : BoundaryProfile}
    (hD : gramDet (J 0) (J 1) ≠ 0) : ContinuousAt boundaryJetCurvature J := by
  have hB (v w : Base) : ContinuousAt (fun H => boundaryJetSecond H v w) J :=
    (continuousAt_boundaryJetSecond v w hD).comp
      (f := fun H => (H,v,w)) (x := J) (by fun_prop)
  have hd : Continuous (fun p : Vec × Vec => p.1 ⬝ᵥ p.2) := by
    unfold dotProduct
    fun_prop
  have hg : Continuous (fun H : BoundaryProfile => gramDet (H 0) (H 1)) :=
    contDiff_gram_pair.continuous.comp
      (show Continuous (fun H : BoundaryProfile => (H 0,H 1)) by fun_prop)
  exact ((hd.continuousAt.comp ((hB dx dx).prodMk (hB dy dy))).sub
    (hd.continuousAt.comp ((hB dx dy).prodMk (hB dx dy)))).div hg.continuousAt hD

end ClosedSurfaceR4.GeometryPreservation

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MetricAcceleration
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The negative tangential acceleration required by the velocity plane is
the actual Christoffel coefficient of the induced metric. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.RealModes
open SmallModes NormalFrame PhaseGeometry

lemma inducedCoordinateMetric_smooth {F : RField 4} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (inducedCoordinateMetric F) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact real_dot_smooth (contDiff_real_coordDeriv hF dx) (contDiff_real_coordDeriv hF dx)
  · exact real_dot_smooth (contDiff_real_coordDeriv hF dx) (contDiff_real_coordDeriv hF dy)
  · exact real_dot_smooth (contDiff_real_coordDeriv hF dy) (contDiff_real_coordDeriv hF dy)

lemma inducedCoordinateMetric_derivative {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (p v : Base) (i : Fin 3) :
    fderiv ℝ (inducedCoordinateMetric F) p v i =
      coordDeriv v (fun q => inducedCoordinateMetric F q i) p := by
  have he := congrArg (fun L : Base →L[ℝ] ℝ => L v)
    (fderiv_apply ((inducedCoordinateMetric_smooth hF).differentiable (by simp) p) i)
  exact he.symm

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MetricConnectionNaturality
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive intrinsic phase Hessian gives negative first-coordinate
acceleration in the actual nonlinear phase chart. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.RealModes
open SmallModes NormalFrame PhaseGeometry

lemma induced_connection_slots {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : Base)
    (i : Fin 3) :
    metricConnectionAt (inducedCoordinateMetric F p,fderiv ℝ (inducedCoordinateMetric F) p) i =
      let X := coordDeriv dx F p
      let Y := coordDeriv dy F p
      let C := (![coordDeriv dx (coordDeriv dx F) p,
        coordDeriv dx (coordDeriv dy F) p,coordDeriv dy (coordDeriv dy F) p] : Fin 3 → RVec 4) i
      (((Y ⬝ᵥ Y)*(X ⬝ᵥ C)-(X ⬝ᵥ Y)*(Y ⬝ᵥ C))/gramDet X Y,
       ((X ⬝ᵥ X)*(Y ⬝ᵥ C)-(X ⬝ᵥ Y)*(X ⬝ᵥ C))/gramDet X Y) := by
  have hcomm := real_second_coordDeriv_comm hF p dy dx
  fin_cases i <;>
    simp only [metricConnectionAt, metricJetDet, Matrix.cons_val_zero', Matrix.cons_val_succ']
  all_goals
    simp only [inducedCoordinateMetric_derivative hF]
    simp only [inducedCoordinateMetric, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    simp only [realMetric_partial hF, hcomm]
    simp only [realMetric, NormalFrame.gramDet, dotProduct_comm]
    congr 1 <;> congr 1 <;> ring

lemma second_connection_decomposition {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (p v w : Base) :
    let Gamma := metricConnectionAt (inducedCoordinateMetric F p,fderiv ℝ (inducedCoordinateMetric F) p)
    coordDeriv v (coordDeriv w F) p =
      fderiv ℝ F p (connectionContract Gamma v w) + realSecondForm F v w p := by
  dsimp only
  have hb (i : Fin 3) :
      (![coordDeriv dx (coordDeriv dx F) p,coordDeriv dx (coordDeriv dy F) p,
        coordDeriv dy (coordDeriv dy F) p] : Fin 3 → RVec 4) i =
      fderiv ℝ F p
        (metricConnectionAt (inducedCoordinateMetric F p,fderiv ℝ (inducedCoordinateMetric F) p) i) +
      realSecondTensor F p i := by
    rw [induced_connection_slots hF p i]
    change _ = coordDeriv _ F p + _
    conv_rhs => lhs; rw [coordDeriv_eq_basis]
    fin_cases i <;> simp only [realSecondTensor,Matrix.cons_val_zero',Matrix.cons_val_succ',
      realSecondForm,realNormalPart] <;> abel
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  change coordDeriv dx (coordDeriv dx F) p = _ at h0
  change coordDeriv dx (coordDeriv dy F) p = _ at h1
  change coordDeriv dy (coordDeriv dy F) p = _ at h2
  rw [second_coordDeriv_bilinear hF,h0,h1,h2,connectionContract,map_add,map_add,
    map_smul,map_smul,map_smul,realSecondForm_bilinear hF]
  simp only [realSecondTensor]
  module

lemma scalar_second_coordDeriv_comp {phi : Base → ℝ} {f : Base → Base}
    (hphi : ContDiff ℝ ∞ phi) (hf : ContDiff ℝ ∞ f) (v w p : Base) :
    coordDeriv v (coordDeriv w (phi ∘ f)) p =
      coordDeriv (fderiv ℝ f p v) (coordDeriv (fderiv ℝ f p w) phi) (f p) +
      fderiv ℝ phi (f p) (coordDeriv v (coordDeriv w f) p) := by
  have hDF : ContDiff ℝ ∞ (fderiv ℝ phi) := hphi.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hD1 := ((hDF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (f p)).hasFDerivAt.comp p
    ((hf.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) p).hasFDerivAt
  have hD2 := (((hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply
      (show ContDiff ℝ ∞ (fun _ : Base => w) from contDiff_const)).differentiable
    (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p).hasFDerivAt
  have hp := hD1.clm_apply hD2
  have he : (fun q => (fderiv ℝ phi ∘ f) q (coordDeriv w f q)) = coordDeriv w (phi ∘ f) := by
    funext q
    simp only [coordDeriv,fderiv_comp q (hphi.differentiable (by simp) _) (hf.differentiable (by simp) _),
      ContinuousLinearMap.comp_apply,Function.comp_apply]
  change HasFDerivAt (fun q => (fderiv ℝ phi ∘ f) q (coordDeriv w f q)) _ p at hp
  rw [he] at hp
  have heval := congrArg (fun L => L v) hp.fderiv
  have hsecond := (((hDF.differentiable (by simp)) (f p)).hasFDerivAt.clm_apply
    (hasFDerivAt_const (fderiv ℝ f p w) (f p))).fderiv
  change fderiv ℝ (fun q => fderiv ℝ phi q (fderiv ℝ f p w)) (f p) = _ at hsecond
  change fderiv ℝ (coordDeriv (fderiv ℝ f p w) phi) (f p) = _ at hsecond
  change fderiv ℝ (coordDeriv w (phi ∘ f)) p v =
    fderiv ℝ (coordDeriv (fderiv ℝ f p w) phi) (f p) (fderiv ℝ f p v) +
    fderiv ℝ phi (f p) (fderiv ℝ (fun x => fderiv ℝ f x w) p v)
  rw [hsecond]
  simpa only [coordDeriv,add_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply,
    zero_apply,map_zero,zero_add,add_zero,Function.comp_apply,add_comm] using heval

lemma phase_chart_connection_identity {F : RField 4} {f : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hf : ContDiff ℝ ∞ f) (p : Base)
    (hImm : Function.Injective (fderiv ℝ F (f p)))
    (hdet : coordDet (fderiv ℝ f p) ≠ 0) :
    let oldGamma := metricConnectionAt (inducedCoordinateMetric F (f p),
      fderiv ℝ (inducedCoordinateMetric F) (f p))
    let newGamma := metricConnectionAt (inducedCoordinateMetric (F ∘ f) p,
      fderiv ℝ (inducedCoordinateMetric (F ∘ f)) p) 2
    fderiv ℝ f p newGamma = coordDeriv dy (coordDeriv dy f) p +
      connectionContract oldGamma (fderiv ℝ f p dy) (fderiv ℝ f p dy) := by
  dsimp only
  apply hImm
  have hD := gramDet_ne_zero_of_injective _ hImm
  have hs := second_coordDeriv_comp_smooth hF hf dy dy p
  rw [second_connection_decomposition hF] at hs
  have hn := second_connection_decomposition (hF.comp hf) p dy dy
  simp only [connectionContract,dy,zero_mul,one_mul,mul_zero,add_zero,zero_add,
    zero_smul,one_smul] at hn
  change coordDeriv dy (coordDeriv dy (F ∘ f)) p =
    fderiv ℝ (F ∘ f) p
      (metricConnectionAt (inducedCoordinateMetric (F ∘ f) p,
        fderiv ℝ (inducedCoordinateMetric (F ∘ f)) p) 2) +
      realSecondForm (F ∘ f) dy dy p at hn
  rw [realSecondForm_comp_smooth hF hf dy dy p hD hdet] at hn
  have he := hn.symm.trans hs
  rw [fderiv_comp p (hF.differentiable (by simp) _) (hf.differentiable (by simp) _),
    ContinuousLinearMap.comp_apply] at he
  rw [map_add]
  apply add_right_cancel (b := realSecondForm F (fderiv ℝ f p dy) (fderiv ℝ f p dy) (f p))
  exact he.trans (by abel)

lemma phase_chart_hessian_dy {F : RField 4} {phi : Base → ℝ} {f : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hphi : ContDiff ℝ ∞ phi) (hf : ContDiff ℝ ∞ f)
    (p : Base) (hphase : phi ∘ f =ᶠ[𝓝 p] Prod.fst)
    (hImm : Function.Injective (fderiv ℝ F (f p)))
    (hdet : coordDet (fderiv ℝ f p) ≠ 0) :
    coordinateMetricHessian (inducedCoordinateMetric (F ∘ f)) Prod.fst p dy dy =
      coordinateMetricHessian (inducedCoordinateMetric F) phi (f p)
        (fderiv ℝ f p dy) (fderiv ℝ f p dy) := by
  let a := fderiv ℝ f p dy
  let oldGamma := metricConnectionAt (inducedCoordinateMetric F (f p),
      fderiv ℝ (inducedCoordinateMetric F) (f p))
  let newGamma := metricConnectionAt (inducedCoordinateMetric (F ∘ f) p,
      fderiv ℝ (inducedCoordinateMetric (F ∘ f)) p) 2
  have hd : (fderiv ℝ phi (f p)).comp (fderiv ℝ f p) = ContinuousLinearMap.fst ℝ ℝ ℝ := by
    rw [← fderiv_comp p (hphi.differentiable (by simp) _) (hf.differentiable (by simp) _),
      hphase.fderiv_eq,fderiv_fst]
  have hs : coordDeriv dy (coordDeriv dy (phi ∘ f)) p = 0 := by
    have he : coordDeriv dy (phi ∘ f) =ᶠ[𝓝 p] coordDeriv dy Prod.fst := by
      filter_upwards [hphase.eventuallyEq_nhds] with x hx
      exact congrArg (fun L : Base →L[ℝ] ℝ => L dy) hx.fderiv_eq
    rw [coordDeriv,he.fderiv_eq]
    change coordDeriv dy (coordDeriv dy Prod.fst) p = 0
    have he : coordDeriv dy (Prod.fst : Base → ℝ) = fun _ => 0 := by
      funext q
      simp [coordDeriv,fderiv_fst,dy]
    rw [he]
    simp [coordDeriv]
  rw [scalar_second_coordDeriv_comp hphi hf] at hs
  have hc := phase_chart_connection_identity hF hf p hImm hdet
  change fderiv ℝ f p newGamma = _ + connectionContract oldGamma a a at hc
  have hp := congrArg (fderiv ℝ phi (f p)) hc
  rw [map_add] at hp
  have hn : fderiv ℝ phi (f p) (fderiv ℝ f p newGamma) = newGamma.1 := by
    change ((fderiv ℝ phi (f p)).comp (fderiv ℝ f p)) newGamma = _
    rw [hd]
    rfl
  rw [hn] at hp
  rw [coordinateMetricHessian_fst_dy,coordinateMetricHessian,
    phaseLinear_phaseDerivative]
  change -newGamma.1 = coordDeriv a (coordDeriv a phi) (f p) -
    fderiv ℝ phi (f p) (connectionContract oldGamma a a)
  change coordDeriv a (coordDeriv a phi) (f p) + _ = 0 at hs
  linarith

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_AtlasBoundaryProfile
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

lemma realChartMap_smooth (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) :
    ContDiff ℝ ∞ (A.realChartMap i F) :=
  (A.jetChartMap_smooth i hF).comp baseEquiv.symm.contDiff

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseMetricConvexity
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict convexity of the prescribed surface metric gives the exact
positive transverse Hessian used by the actual phase-coordinate loop. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry SurfaceJetCoordinates

lemma coordinateMetricHessian_congr_germ {h k : Base → PhaseMean.Tensor} {p : Base}
    (hh : h =ᶠ[𝓝 p] k) (phi : Base → ℝ) (v w : Base) :
    coordinateMetricHessian h phi p v w = coordinateMetricHessian k phi p v w := by
  simp only [coordinateMetricHessian,hh.eq_of_nhds,hh.fderiv_eq]

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CoordinateIsometryMetric
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The ordinary coordinate metric of an isometric immersion is the
prescribed metric, independently of atlas partition weights. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma coordinateMap_metric_evaluate {g : SmoothMetric M} {F : M → Space}
    (hF : IsSmoothIsometricImmersion M g F) (q : M) {x : Base}
    (hx : x ∈ coordinateDomain q) (v w : Base) :
    realMetric (coordinateMap F q) v w x = PhaseMean.evaluate (coordinateMetric g q x) v w := by
  have hi := ((coordinateInverse_smoothOn q) x hx).contMDiffAt
    ((coordinateDomain_open q).mem_nhds hx)
  have hm := (hF.1 (coordinateInverse q x)).mdifferentiableAt (by simp)
  have hic := hi.mdifferentiableAt (by simp)
  have hd := mfderiv_comp x hm hic
  rw [mfderiv_eq_fderiv] at hd
  have hs : DifferentiableAt ℝ (F ∘ coordinateInverse q) x := (hm.comp x hic).differentiableAt
  have he : fderiv ℝ (coordinateMap F q) x = spaceCoordinates.toContinuousLinearMap.comp
      ((mfderiv planeModel spaceModel F (coordinateInverse q x)).comp
        (mfderiv 𝓘(ℝ,Base) planeModel (coordinateInverse q) x)) := by
    change fderiv ℝ (spaceCoordinates ∘ (F ∘ coordinateInverse q)) x = _
    rw [fderiv_comp x spaceCoordinates.differentiableAt hs,spaceCoordinates.fderiv,hd]
    rfl
  rw [coordinateMetric_evaluate]
  change fderiv ℝ (coordinateMap F q) x v ⬝ᵥ fderiv ℝ (coordinateMap F q) x w = _
  rw [he]
  let vv : TangentSpace 𝓘(ℝ,Base) x := v
  let ww : TangentSpace 𝓘(ℝ,Base) x := w
  let dv : TangentSpace planeModel (coordinateInverse q x) :=
    mfderiv 𝓘(ℝ,Base) planeModel (coordinateInverse q) x vv
  let dw : TangentSpace planeModel (coordinateInverse q x) :=
    mfderiv 𝓘(ℝ,Base) planeModel (coordinateInverse q) x ww
  change spaceCoordinates (mfderiv planeModel spaceModel F (coordinateInverse q x) dv) ⬝ᵥ
    spaceCoordinates (mfderiv planeModel spaceModel F (coordinateInverse q x) dw) = g.inner _ dv dw
  exact (spaceCoordinates_dot _ _).trans (hF.2 _ dv dw)

lemma coordinateMap_metric {g : SmoothMetric M} {F : M → Space}
    (hF : IsSmoothIsometricImmersion M g F) (q : M) {x : Base}
    (hx : x ∈ coordinateDomain q) :
    inducedCoordinateMetric (coordinateMap F q) x = coordinateMetric g q x := by
  ext k
  fin_cases k
  · change realMetric (coordinateMap F q) dx dx x = coordinateMetric g q x 0
    simpa [PhaseMean.evaluate,dx,dy] using coordinateMap_metric_evaluate hF q hx dx dx
  · change realMetric (coordinateMap F q) dx dy x = coordinateMetric g q x 1
    simpa [PhaseMean.evaluate,dx,dy] using coordinateMap_metric_evaluate hF q hx dx dy
  · change realMetric (coordinateMap F q) dy dy x = coordinateMetric g q x 2
    simpa [PhaseMean.evaluate,dx,dy] using coordinateMap_metric_evaluate hF q hx dy dy

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PreferredNormalPhasePullback
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pull the actual global preferred normal into the primitive's phase
coordinates, preserving smoothness, unit length and orthogonality. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4
open SurfaceJetCoordinates SmallModes RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace PreferredNormal
variable {F : M → Space} (n : PreferredNormal F)

omit [IsManifold planeModel ∞ M] in
lemma pullback_normal_at (hF : ContMDiff planeModel spaceModel ∞ F)
    {u : Base → M} {x : Base} (hu : ContMDiffAt 𝓘(ℝ,Base) planeModel ∞ u x) (v : Base) :
    coordDeriv v (spaceCoordinates ∘ F ∘ u) x ⬝ᵥ spaceCoordinates (n.vector (u x)) = 0 := by
  have hF' : ContMDiff planeModel 𝓘(ℝ,NormalFrame.Vec) ∞ (spaceCoordinates ∘ F) :=
    spaceCoordinates.contDiff.contMDiff.comp hF
  change fderiv ℝ ((spaceCoordinates ∘ F) ∘ u) x v ⬝ᵥ _ = 0
  rw [← mfderiv_eq_fderiv,mfderiv_comp x (hF'.mdifferentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).mdifferentiableAt
    (hu.mdifferentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
  rw [mfderiv_comp (u x)
    ((spaceCoordinates.contDiff (n := (∞ : ℕ∞ω))).contMDiff.mdifferentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).mdifferentiableAt
    (hF.mdifferentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).mdifferentiableAt,
    mfderiv_eq_fderiv,spaceCoordinates.fderiv]
  let vx : TangentSpace 𝓘(ℝ,Base) x := v
  let w : TangentSpace planeModel (u x) := mfderiv 𝓘(ℝ,Base) planeModel u x vx
  change spaceCoordinates (mfderiv planeModel spaceModel F (u x) w) ⬝ᵥ
    spaceCoordinates (n.vector (u x)) = 0
  exact (spaceCoordinates_dot _ _).trans (n.normal _ w)

lemma inPhase_smooth (q : M) (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) :
    ContDiffOn ℝ ∞ (n.inPhase q e) (surfacePhaseChart q e).target :=
  (spaceCoordinates.contDiff.contMDiff.comp n.smooth |>.comp_contMDiffOn
    (surfacePhaseChart_symm_smooth q e hi)).contDiffOn

omit [IsManifold planeModel ∞ M] in
lemma inPhase_unit (q : M) (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (x : Base) : n.inPhase q e x ⬝ᵥ n.inPhase q e x = 1 := by
  change spaceCoordinates (n.vector _) ⬝ᵥ spaceCoordinates (n.vector _) = 1
  rw [spaceCoordinates_dot,real_inner_self_eq_norm_sq,n.unit]
  norm_num

lemma inPhase_normal (hF : ContMDiff planeModel spaceModel ∞ F)
    (q : M) (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {x : Base} (hx : x ∈ (surfacePhaseChart q e).target)
    (v : Base) : coordDeriv v (surfacePhaseMap q e F) x ⬝ᵥ n.inPhase q e x = 0 := by
  exact n.pullback_normal_at hF
    ((surfacePhaseChart_symm_smooth q e hi x hx).contMDiffAt
      ((surfacePhaseChart q e).open_target.mem_nhds hx)) v

end PreferredNormal
end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_OuterPhaseGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fixed outer plateau, including points outside the partition weight,
retains the actual immersion, metric and normal in phase coordinates. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phaseRealChartMap_surface_germ_of_outer (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (F : M → Space)
    {x : SmallModes.Base} (hx : x ∈ (surfacePhaseChart (i : M) e).target)
    (ho : A.outer i =ᶠ[𝓝 ((surfacePhaseChart (i : M) e).symm x)] (fun _ => 1)) :
    A.phaseRealChartMap i e.symm F =ᶠ[𝓝 x] surfacePhaseMap (i : M) e F := by
  have hh := ho.comp_tendsto ((surfacePhaseChart (i : M) e).continuousAt_symm hx)
  filter_upwards [(surfacePhaseChart (i : M) e).open_target.mem_nhds hx,hh] with y hy hoy
  have hyt : e.symm (baseEquiv.symm y) ∈ (chart (i : M)).target := hy.2
  change spaceCoordinates (A.vectorChartRead i F (e.symm (baseEquiv.symm y))) =
    spaceCoordinates (F ((chart (i : M)).symm (e.symm (baseEquiv.symm y))))
  change A.outer i ((chart (i : M)).symm (e.symm (baseEquiv.symm y))) = 1 at hoy
  simp only [vectorChartRead,localize,indicator_of_mem hyt,hoy,one_pow,one_smul]

lemma realChartMap_germ_of_outer (i : A.centers) (F : M → Space) {p : M}
    (hp : p ∈ (chart (i : M)).source) (ho : A.outer i =ᶠ[𝓝 p] (fun _ => 1)) :
    A.realChartMap i F =ᶠ[𝓝 (coordinateChart (i : M) p)] coordinateMap F (i : M) := by
  let e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base := .refl _
  have hx : coordinateChart (i : M) p ∈ (surfacePhaseChart (i : M) e).target := by
    change (baseEquiv.symm (coordinateChart (i : M) p) ∈ Set.univ) ∧
      e.symm (baseEquiv.symm (coordinateChart (i : M) p)) ∈ (chart (i : M)).target
    refine ⟨mem_univ _,?_⟩
    rw [show coordinateChart (i : M) p = baseEquiv (chart (i : M) p) from rfl,
      baseEquiv.symm_apply_apply]
    exact (chart (i : M)).map_source hp
  have hback : (surfacePhaseChart (i : M) e).symm (coordinateChart (i : M) p) = p := by
    change (chart (i : M)).symm (baseEquiv.symm (coordinateChart (i : M) p)) = p
    rw [show coordinateChart (i : M) p = baseEquiv (chart (i : M) p) from rfl,
      baseEquiv.symm_apply_apply,(chart (i : M)).left_inv hp]
  have hh := A.phaseRealChartMap_surface_germ_of_outer i e F hx (by rwa [hback])
  exact hh

lemma realChartMap_metric_germ_of_outer (i : A.centers) {g : SmoothMetric M} {F : M → Space}
    (hF : IsSmoothIsometricImmersion M g F) {p : M}
    (hp : p ∈ (chart (i : M)).source) (ho : A.outer i =ᶠ[𝓝 p] (fun _ => 1)) :
    inducedCoordinateMetric (A.realChartMap i F) =ᶠ[𝓝 (coordinateChart (i : M) p)]
      coordinateMetric g (i : M) := by
  have hg := A.realChartMap_germ_of_outer i F hp ho
  have hpc : p ∈ (coordinateChart (i : M)).source := by
    simpa only [coordinateChart_source,chart_source] using hp
  have hpt : coordinateChart (i : M) p ∈ coordinateDomain (i : M) := by
    rw [← coordinateChart_target]
    exact (coordinateChart (i : M)).map_source hpc
  filter_upwards [hg.eventuallyEq_nhds,(coordinateDomain_open (i : M)).mem_nhds hpt] with y hy hyt
  rw [← coordinateMap_metric hF (i : M) hyt]
  simp only [inducedCoordinateMetric,realMetric,coordDeriv,hy.fderiv_eq]

lemma realChartMap_injective_of_outer (i : A.centers) {g : SmoothMetric M} {F : M → Space}
    (hF : IsSmoothIsometricImmersion M g F) {p : M}
    (hp : p ∈ (chart (i : M)).source) (ho : A.outer i =ᶠ[𝓝 p] (fun _ => 1)) :
    Function.Injective (fderiv ℝ (A.realChartMap i F) (coordinateChart (i : M) p)) := by
  rw [(A.realChartMap_germ_of_outer i F hp ho).fderiv_eq]
  apply coordinateMap_injective_of_immersion hF.1 (IsSmoothIsometricImmersion.mfderiv_injective hF)
  rw [← coordinateChart_target]
  apply (coordinateChart (i : M)).map_source
  simpa only [coordinateChart_source,chart_source] using hp

lemma preferred_normal_in_phase_of_outer (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (n : PreferredNormal F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {x : SmallModes.Base}
    (hx : x ∈ (surfacePhaseChart (i : M) e).target)
    (ho : A.outer i =ᶠ[𝓝 ((surfacePhaseChart (i : M) e).symm x)] (fun _ => 1))
    (v : SmallModes.Base) :
    coordDeriv v (A.phaseRealChartMap i e.symm F) x ⬝ᵥ n.inPhase (i : M) e x = 0 := by
  rw [coordDeriv,(A.phaseRealChartMap_surface_germ_of_outer i e F hx ho).fderiv_eq]
  exact n.inPhase_normal hF (i : M) e hi hx v

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_OuterPhaseConvexity
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The transverse phase Hessian stays positive on the whole prescribed
outer plateau, including its collar beyond the primitive support. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas
open JetPolynomial SurfaceJetCoordinates SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable (A : SmoothingAtlas M)

theorem phase_hessian_positive_of_outer (i : A.centers)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {phi : SmallModes.Base → ℝ} (hphi : ContDiff ℝ ∞ phi)
    (hphase : ∀ x, (realPhaseChart e x).1 = phi x)
    {p : M} (hp : p ∈ (surfacePhaseChart (i : M) e).source) (ho : A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (hpositive : ∀ v : SmallModes.Base, v ≠ 0 →
      0 < coordinateMetricHessian (coordinateMetric g (i : M)) phi (coordinateChart (i : M) p) v v) :
    0 < coordinateMetricHessian (inducedCoordinateMetric (A.phaseRealChartMap i e.symm F))
      Prod.fst (baseEquiv (e (chart (i : M) p))) dy dy := by
  let er := realPhaseChart e
  let x := baseEquiv (e (chart (i : M) p))
  have hx : x ∈ er.target := by
    change baseEquiv.symm (baseEquiv (e (chart (i : M) p))) ∈ e.target
    rw [baseEquiv.symm_apply_apply]
    exact e.map_source hp.2
  have hback : er.symm x = coordinateChart (i : M) p := by
    change baseEquiv (e.symm (baseEquiv.symm (baseEquiv (e (chart (i : M) p))))) = _
    rw [baseEquiv.symm_apply_apply]
    have hps : chart (i : M) p ∈ e.source := hp.2
    exact (congrArg baseEquiv (e.left_inv hps)).trans (show baseEquiv (chart (i : M) p) = coordinateChart (i : M) p from rfl)
  have her := realPhaseChart_smooth e he
  have hir := realPhaseChart_symm_smooth e hi
  have hcomp : phi ∘ er.symm =ᶠ[𝓝 x] Prod.fst := by
    filter_upwards [er.open_target.mem_nhds hx] with y hy
    change phi (er.symm y) = y.1
    rw [← hphase,er.right_inv hy]
  have hdet : coordDet (fderiv ℝ er.symm x) ≠ 0 :=
    coordDet_fderiv_ne_zero_of_local_inverse er.open_target er.open_source hir.contDiffOn
      her.contDiffOn er.symm.mapsTo (fun y hy => er.right_inv hy) hx
  have hI : Function.Injective (fderiv ℝ (A.realChartMap i F) (er.symm x)) := by
    rw [hback]
    exact A.realChartMap_injective_of_outer i hF hp.1 ho
  have hH := phase_chart_hessian_dy (A.realChartMap_smooth i hF.1) hphi hir x hcomp hI hdet
  have hmap : A.phaseRealChartMap i e.symm F = A.realChartMap i F ∘ er.symm := by
    funext y
    simp only [phaseRealChartMap,realChartMap,Function.comp_apply,er,realPhaseChart_symm_apply]
    have hb : (planeCoordinateIsometry : JetPolynomial.Base → SmallModes.Base) = baseEquiv := rfl
    have hbs : (planeCoordinateIsometry.symm : SmallModes.Base → JetPolynomial.Base) = baseEquiv.symm := rfl
    rw [hb,hbs,baseEquiv.symm_apply_apply]
  rw [hmap,hH,hback,
    coordinateMetricHessian_congr_germ (A.realChartMap_metric_germ_of_outer i hF hp.1 ho)]
  apply hpositive
  have hI' := inverse_chart_derivative_injective er her hir hx
  intro hz
  have hh : (dy : SmallModes.Base) = 0 := hI' (hz.trans (map_zero _).symm)
  exact (show (dy : SmallModes.Base) ≠ 0 by simp [dy]) hh


end ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseOuterImmersion
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact phase map remains an immersion on the full outer plateau. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma phaseRealChartMap_eq_real_comp (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (F : M → Space) :
    A.phaseRealChartMap i e.symm F = A.realChartMap i F ∘ (realPhaseChart e).symm := by
  funext y
  simp only [phaseRealChartMap,realChartMap,Function.comp_apply,realPhaseChart_symm_apply]
  have hb : (planeCoordinateIsometry : JetPolynomial.Base → SmallModes.Base) = baseEquiv := rfl
  have hbs : (planeCoordinateIsometry.symm : SmallModes.Base → JetPolynomial.Base) = baseEquiv.symm := rfl
  rw [hb,hbs,baseEquiv.symm_apply_apply]

lemma phase_injective_of_outer (i : A.centers)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {p : M} (hp : p ∈ (surfacePhaseChart (i : M) e).source)
    (ho : A.outer i =ᶠ[𝓝 p] (fun _ => 1)) :
    Function.Injective (fderiv ℝ (A.phaseRealChartMap i e.symm F)
      (surfacePhaseChart (i : M) e p)) := by
  let er := realPhaseChart e
  let x := surfacePhaseChart (i : M) e p
  have hx : x ∈ er.target := by
    change baseEquiv.symm (baseEquiv (e (chart (i : M) p))) ∈ e.target
    rw [baseEquiv.symm_apply_apply]
    exact e.map_source hp.2
  have hback : er.symm x = coordinateChart (i : M) p := by
    change baseEquiv (e.symm (baseEquiv.symm (baseEquiv (e (chart (i : M) p))))) = _
    rw [baseEquiv.symm_apply_apply]
    have hps : chart (i : M) p ∈ e.source := hp.2
    exact (congrArg baseEquiv (e.left_inv hps)).trans rfl
  have hI : Function.Injective (fderiv ℝ (A.realChartMap i F) (er.symm x)) := by
    rw [hback]
    exact A.realChartMap_injective_of_outer i hF hp.1 ho
  rw [A.phaseRealChartMap_eq_real_comp,fderiv_comp _
    ((A.realChartMap_smooth i hF.1).differentiable (by simp) _)
    ((realPhaseChart_symm_smooth e hi).differentiable (by simp) _)]
  exact hI.comp (inverse_chart_derivative_injective er (realPhaseChart_smooth e he)
    (realPhaseChart_symm_smooth e hi) hx)

omit [CompactSpace M] in
lemma phase_outer_neighborhood (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {T Ω : Set SmallModes.Base} (hΩ : IsOpen Ω)
    (hTΩ : T ⊆ Ω) (hΩe : Ω ⊆ (surfacePhaseChart (i : M) e).target)
    (hT : ∀ x ∈ T, A.outer i =ᶠ[𝓝 ((surfacePhaseChart (i : M) e).symm x)] (fun _ => 1)) :
    ∃ U : Set SmallModes.Base, IsOpen U ∧ T ⊆ U ∧ U ⊆ Ω ∧
      ∀ x ∈ U, A.outer i =ᶠ[𝓝 ((surfacePhaseChart (i : M) e).symm x)] (fun _ => 1) := by
  let P := {p : M | A.outer i =ᶠ[𝓝 p] (fun _ => 1)}
  have hP : IsOpen P := isOpen_setOfPred_eventually_nhds
  let E := surfacePhaseChart (i : M) e
  let U := Ω ∩ (E.target ∩ E.symm ⁻¹' P)
  have hU : IsOpen U := hΩ.inter (E.symm.isOpen_inter_preimage hP)
  exact ⟨U,hU,fun x hx => ⟨hTΩ hx,hΩe (hTΩ hx),hT x hx⟩,
    inter_subset_left,fun _ hx => hx.2.2⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CrossAtlasOuterGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The old and new analytic atlases represent the same immersion on a
common outer plateau, including all second forms and intrinsic crossings. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (A B : SmoothingAtlas M)

lemma phase_germ_of_common_outer (i : A.centers) (j : B.centers)
    (hc : (i : M) = (j : M))
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (F : M → Space)
    {x : Base} (hx : x ∈ (surfacePhaseChart (j : M) e).target)
    (ho : A.outer i =ᶠ[𝓝 ((surfacePhaseChart (j : M) e).symm x)] (fun _ => 1))
    (hw : B.weight j ((surfacePhaseChart (j : M) e).symm x) ≠ 0) :
    A.phaseRealChartMap i e.symm F =ᶠ[𝓝 x] B.phaseRealChartMap j e.symm F := by
  have hxA : x ∈ (surfacePhaseChart (i : M) e).target := by rwa [hc]
  have hoA : A.outer i =ᶠ[𝓝 ((surfacePhaseChart (i : M) e).symm x)] (fun _ => 1) := by rwa [hc]
  have hA := A.phaseRealChartMap_surface_germ_of_outer i e F hxA hoA
  have hB := B.phaseRealChartMap_surface_germ j e F hx hw
  rw [hc] at hA
  exact hA.trans hB.symm

lemma phase_second_of_common_outer (i : A.centers) (j : B.centers)
    (hc : (i : M) = (j : M))
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (F : M → Space)
    {x : Base} (hx : x ∈ (surfacePhaseChart (j : M) e).target)
    (ho : A.outer i =ᶠ[𝓝 ((surfacePhaseChart (j : M) e).symm x)] (fun _ => 1))
    (hw : B.weight j ((surfacePhaseChart (j : M) e).symm x) ≠ 0) (v w : Base) :
    realSecondForm (A.phaseRealChartMap i e.symm F) v w x =
      realSecondForm (B.phaseRealChartMap j e.symm F) v w x :=
  (realSecondForm_eventuallyEq (A.phase_germ_of_common_outer B i j hc e F hx ho hw) v w).eq_of_nhds

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PrescribedAtlasPlateau
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choose the analytic atlas patch with both its weight support and its
outer plateau prescribed by the primitive's compact neighborhood. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem exists_smoothingAtlas_prescribed_plateau (q : M) {K U P : Set M}
    (hK : IsCompact K) (hqK : q ∈ K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hUs : U ⊆ (chart q).source) (hP : IsCompact P) (hPs : P ⊆ (chart q).source) :
    ∃ (A : SmoothingAtlas M) (i : A.centers), (i : M) = q ∧
      (∀ p ∈ K, 0 < A.weight i p) ∧ tsupport (A.weight i) ⊆ U ∧
      (∀ j p, p ∈ tsupport (A.weight j) → A.outer j =ᶠ[𝓝 p] (fun _ => 1)) ∧
      ∀ p ∈ P, A.outer i =ᶠ[𝓝 p] (fun _ => 1) := by
  obtain ⟨A,i,hiq,hpos,hsupp,_hnon,ho⟩ := exists_smoothingAtlas_prescribed_patch q hK hqK hU hKU hUs
  have hPs' : P ⊆ (chart (i : M)).source := by simpa only [hiq] using hPs
  obtain ⟨B,hcenters,hw,hout,hplateau⟩ := A.enlarge_outer_plateau i hP hPs' ho
  have hcast {s t : Finset M} (h : s = t) (j : s) :
      ((h ▸ j : t) : M) = (j : M) := by
    subst t
    rfl
  refine ⟨B,hcenters.symm ▸ i,(hcast hcenters.symm i).trans hiq,?_,?_,hout,hplateau⟩
  · intro p hp
    rw [hw]
    exact hpos p hp
  · have he : B.weight (hcenters.symm ▸ i) = A.weight i := funext (hw i)
    rwa [he]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ProjectedFrameConstruction
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the collar interpolation of the velocity frame from boundary
non-antipodality, with no interpolation function assumed. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma nonopposite_region_open {Ω : Set E} (hΩ : IsOpen Ω) {B n : E → Vec}
    (hB : ContDiffOn ℝ ∞ B Ω) (hn : ContDiffOn ℝ ∞ n Ω) :
    IsOpen {x | x ∈ Ω ∧ B x ≠ 0 ∧ normalize (B x) ≠ -n x} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hb := hB.contDiffAt (hΩ.mem_nhds hx.1)
  have hn' := hn.contDiffAt (hΩ.mem_nhds hx.1)
  have hanti := ((normalize_smoothAt hb hx.2.1).continuousAt.ne_iff_eventually_ne
    hn'.continuousAt.neg).mp hx.2.2
  filter_upwards [hΩ.mem_nhds hx.1, hb.continuousAt.eventually_ne hx.2.1, hanti] with y hy hb' ha'
  exact ⟨hy, hb', ha'⟩

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_AdaptedPhasePrimitiveAtlas
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restrict the primitive's phase domain and choose its analytic atlas
inside the already prepared exterior collar. The phase functions are unchanged. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

theorem adapted_phase_primitive_atlas (q : M)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {K : Set M} (hK : IsCompact K) (hqK : q ∈ K)
    (hKs : K ⊆ (surfacePhaseChart q e).source)
    {V : Set Base} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (hKV : (surfacePhaseChart q e) '' K ⊆ V)
    (hVs : closure V ⊆ (surfacePhaseChart q e).target) :
    ∃ (A : SmoothingAtlas M) (i : A.centers)
      (f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base),
      (i : M) = q ∧ (∀ x, f x = e x) ∧ (∀ x, f.symm x = e.symm x) ∧
      ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ f.symm ∧
      (∀ p ∈ K, 0 < A.weight i p) ∧
      (∀ j p, p ∈ tsupport (A.weight j) → A.outer j =ᶠ[𝓝 p] (fun _ => 1)) ∧
      (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ f.source ∧
      MapsTo f f.source (baseEquiv ⁻¹' V) ∧
      K ⊆ (surfacePhaseChart (i : M) f).source ∧
      ∀ x ∈ closure V, A.outer i =ᶠ[𝓝 ((surfacePhaseChart q e).symm x)] (fun _ => 1) := by
  let E := surfacePhaseChart q e
  let U := E.source ∩ E ⁻¹' V
  have hU : IsOpen U := E.isOpen_inter_preimage hV
  have hKU : K ⊆ U := fun p hp => ⟨hKs hp,hKV (mem_image_of_mem E hp)⟩
  let P := E.symm '' closure V
  have hP : IsCompact P := hVc.image_of_continuousOn (E.symm.continuousOn.mono hVs)
  have hPs : P ⊆ (chart q).source := by
    rintro _ ⟨x,hx,rfl⟩
    exact (E.map_target (hVs hx)).1
  obtain ⟨A,i,hiq,hpos,hweight,ho,hplateau⟩ := exists_smoothingAtlas_prescribed_plateau q
    hK hqK hU hKU (fun _ hp => hp.1.1) hP hPs
  let W := (fun x : JetPolynomial.Base => baseEquiv (e x)) ⁻¹' V
  have hW : IsOpen W := hV.preimage (baseEquiv.continuous.comp he.continuous)
  let f := e.restrOpen W hW
  have hsource : (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ f.source := by
    rintro x ⟨p,hp,rfl⟩
    have hpU := hweight hp
    change chart (i : M) p ∈ e.source ∩ W
    rw [hiq]
    exact ⟨hpU.1.2,hpU.2⟩
  refine ⟨A,i,f,hiq,(fun _ => rfl),(fun _ => rfl),he,hi,hpos,ho,hsource,?_,?_,?_⟩
  · intro x hx
    exact hx.2
  · intro p hp
    have hu := hKU hp
    change p ∈ (chart (i : M)).source ∧ chart (i : M) p ∈ f.source
    rw [hiq]
    exact ⟨hu.1.1,hu.1.2,hu.2⟩
  · intro x hx
    exact hplateau _ ⟨x,hx,rfl⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveOuterGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the prescribed metric's convexity and the chosen outer plateau
into all geometric hypotheses of the supported primitive loop. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates JetPolynomial SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem primitive_outer_geometry (i : A.centers)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (n : PreferredNormal F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {phi : SmallModes.Base → ℝ} (hphi : ContDiff ℝ ∞ phi)
    (hphase : ∀ x, (realPhaseChart e x).1 = phi x)
    {T Ω : Set SmallModes.Base} (hΩ : IsOpen Ω) (hTΩ : T ⊆ Ω)
    (hΩe : Ω ⊆ (surfacePhaseChart (i : M) e).target)
    (houter : ∀ x ∈ T, A.outer i =ᶠ[𝓝 ((surfacePhaseChart (i : M) e).symm x)] (fun _ => 1))
    (hconvex : ∀ x ∈ Ω, ∀ v : SmallModes.Base, v ≠ 0 →
      0 < coordinateMetricHessian (coordinateMetric g (i : M)) phi
        (coordinateChart (i : M) ((surfacePhaseChart (i : M) e).symm x)) v v) :
    ∃ U : Set SmallModes.Base, IsOpen U ∧ T ⊆ U ∧ U ⊆ Ω ∧
      ContDiffOn ℝ ∞ (n.inPhase (i : M) e) U ∧
      (∀ x ∈ U, Function.Injective (fderiv ℝ (A.phaseRealChartMap i e.symm F) x)) ∧
      (∀ x ∈ U, coordDeriv dx (A.phaseRealChartMap i e.symm F) x ⬝ᵥ n.inPhase (i : M) e x = 0 ∧
        coordDeriv dy (A.phaseRealChartMap i e.symm F) x ⬝ᵥ n.inPhase (i : M) e x = 0 ∧
        n.inPhase (i : M) e x ⬝ᵥ n.inPhase (i : M) e x = 1) ∧
      ∀ x ∈ U, 0 < coordinateMetricHessian
        (inducedCoordinateMetric (A.phaseRealChartMap i e.symm F)) Prod.fst x dy dy := by
  obtain ⟨U,hU,hTU,hUΩ,ho⟩ := A.phase_outer_neighborhood i e hΩ hTΩ hΩe houter
  let E := surfacePhaseChart (i : M) e
  have hUE : U ⊆ E.target := hUΩ.trans hΩe
  refine ⟨U,hU,hTU,hUΩ,(n.inPhase_smooth (i : M) e hi).mono hUE,?_,?_,?_⟩
  · intro x hx
    have hp := E.map_target (hUE hx)
    have hh := A.phase_injective_of_outer i hF e he hi hp (ho x hx)
    change Function.Injective (fderiv ℝ (A.phaseRealChartMap i e.symm F) (E (E.symm x))) at hh
    rwa [E.right_inv (hUE hx)] at hh
  · intro x hx
    exact ⟨A.preferred_normal_in_phase_of_outer i hF.1 n e hi (hUE hx) (ho x hx) dx,
      A.preferred_normal_in_phase_of_outer i hF.1 n e hi (hUE hx) (ho x hx) dy,
      n.inPhase_unit (i : M) e x⟩
  · intro x hx
    have hh := A.phase_hessian_positive_of_outer i hF e he hi hphi hphase
      (E.map_target (hUE hx)) (ho x hx) (hconvex x (hUΩ hx))
    change 0 < coordinateMetricHessian _ Prod.fst (E (E.symm x)) dy dy at hh
    rwa [E.right_inv (hUE hx)] at hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_PrimitiveBoundaryCollar
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The old boundary inequalities extend to one compact collar. This
supplies the zero-amplitude conditions on the full analytic domain. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

lemma actual_intrinsic_crossing_continuousOn {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {U : Set Base} (hD : ∀ x ∈ U, gramDet (coordDeriv dx F x) (coordDeriv dy F x) ≠ 0)
    (hB : ∀ x ∈ U, realSecondForm F dy dy x ≠ 0)
    {v : Base → Base} (hv : ContinuousOn v U) :
    ContinuousOn (fun x => orderedCrossing F dy (v x) x
      (coordinateGaussianCurvature (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) x)) U := by
  let J := realBoundaryProfile F 1
  have hJ : Continuous J := (realBoundaryProfile_smooth hF 1).continuous
  have hκ : ContinuousOn (fun x => boundaryJetCurvature (J x)) U := by
    intro x hx
    exact ((continuousAt_boundaryJetCurvature (hD x hx)).comp hJ.continuousAt).continuousWithinAt
  have hcross : ContinuousOn (fun x => boundaryJetCrossing (J x) dy (v x)
      (boundaryJetCurvature (J x))) U := by
    intro x hx
    have hb : boundaryJetSecond (J x) dy dy ≠ 0 := by
      rw [boundaryJetSecond_actual hF]
      exact hB x hx
    exact (continuousAt_boundaryJetCrossing (J := J x) (v := dy) (w := v x)
      (κ := boundaryJetCurvature (J x)) (hD x hx) hb).comp_continuousWithinAt
      (f := fun y => (J y,dy,v y,boundaryJetCurvature (J y)))
      (hJ.continuousAt.continuousWithinAt.prodMk
        (continuousWithinAt_const.prodMk ((hv x hx).prodMk (hκ x hx))))
  exact hcross.congr (fun x hx => by
    dsimp only [J]
    rw [boundaryJetCrossing_actual hF,boundaryJetCurvature_actual hF x (hD x hx)])

theorem primitive_boundary_collar {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {Ω D : Set Base} (hΩ : IsOpen Ω) (hD : IsOpen D)
    (hDc : IsCompact (closure D)) (hDΩ : closure D ⊆ Ω)
    (hI : ∀ x ∈ Ω, gramDet (coordDeriv dx F x) (coordDeriv dy F x) ≠ 0)
    {n : Base → Vec} (hn : ContDiffOn ℝ ∞ n Ω)
    (hboundary : ∀ x ∈ frontier D, realSecondForm F dy dy x ≠ 0 ∧
      normalize (realSecondForm F dy dy x) ≠ -n x)
    {ι : Type*} [Finite ι] (C : ι → Set Base) (hC : ∀ i, IsClosed (C i))
    (v : ι → Base → Base) (hv : ∀ i, ContDiff ℝ ∞ (v i))
    (hold : ∀ i x, x ∈ C i → x ∈ frontier D →
      0 < orderedCrossing F dy (v i x) x
        (coordinateGaussianCurvature (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) x)) :
    ∃ V : Set Base, IsOpen V ∧ IsCompact (closure V) ∧ closure D ⊆ V ∧ closure V ⊆ Ω ∧
      (∀ x ∈ closure V \ D, realSecondForm F dy dy x ≠ 0 ∧
        normalize (realSecondForm F dy dy x) ≠ -n x) ∧
      ∀ i x, x ∈ C i → x ∈ closure V \ D →
        0 < orderedCrossing F dy (v i x) x
          (coordinateGaussianCurvature (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) x) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  let N := {x | x ∈ Ω ∧ realSecondForm F dy dy x ≠ 0 ∧
    normalize (realSecondForm F dy dy x) ≠ -n x}
  have hN : IsOpen N := nonopposite_region_open hΩ (realSecondForm_smoothOn hF hI dy dy) hn
  have hDN : frontier D ⊆ N := fun x hx => ⟨hDΩ (frontier_subset_closure hx),hboundary x hx⟩
  let Q := fun i x => orderedCrossing F dy (v i x) x
    (coordinateGaussianCurvature (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) x)
  have hQ (i : ι) : ContinuousOn (Q i) N :=
    actual_intrinsic_crossing_continuousOn hF (fun x hx => hI x hx.1)
      (fun _ hx => hx.2.1) ((hv i).continuous.continuousOn)
  let G := N ∩ ⋂ i, (C i)ᶜ ∪ (N ∩ (Q i) ⁻¹' Ioi 0)
  have hG : IsOpen G := hN.inter (isOpen_iInter_of_finite (fun i =>
    (hC i).isOpen_compl.union ((hQ i).isOpen_inter_preimage hN isOpen_Ioi)))
  have hDG : frontier D ⊆ G := by
    intro x hx
    refine ⟨hDN hx,mem_iInter.mpr fun i => ?_⟩
    by_cases hi : x ∈ C i
    · exact Or.inr ⟨hDN hx,hold i x hi hx⟩
    · exact Or.inl hi
  obtain ⟨V,hV,hVc,hDV,hVΩ,hVG⟩ := compact_phase_boundary_neighborhood hD hDc hΩ hDΩ hG hDG
  refine ⟨V,hV,hVc,hDV,hVΩ,fun x hx => (hVG hx).1.2,?_⟩
  intro i x hi hx
  exact (Or.resolve_left (mem_iInter.mp (hVG hx).2 i) (not_not.mpr hi)).2

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_AdaptedPrimitiveGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the entire analytic chart neighborhood from the actual
surface metric, preferred normal and primitive boundary. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SurfaceJetCoordinates SmallModes RealModes PhaseGeometry VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

theorem adapted_primitive_geometry_oai (j : B.centers)
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (n : PreferredNormal F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {D : Set M} (hD : IsOpen D) (hqD : (j : M) ∈ D)
    (hDs : closure D ⊆ (surfacePhaseChart (j : M) e).source)
    {Ω : Set Base} (hΩ : IsOpen Ω)
    (hDΩ : (surfacePhaseChart (j : M) e) '' closure D ⊆ Ω)
    (hΩe : Ω ⊆ (surfacePhaseChart (j : M) e).target)
    (hactive : ∀ x ∈ Ω, B.weight j ((surfacePhaseChart (j : M) e).symm x) ≠ 0)
    {phi : Base → ℝ} (hphi : ContDiff ℝ ∞ phi)
    (hphase : ∀ x, (JetPolynomial.realPhaseChart e x).1 = phi x)
    (hconvex : ∀ x ∈ Ω, ∀ v : Base, v ≠ 0 →
      0 < coordinateMetricHessian (coordinateMetric g (j : M)) phi
        (coordinateChart (j : M) ((surfacePhaseChart (j : M) e).symm x)) v v)
    (hboundary : ∀ x ∈ frontier ((surfacePhaseChart (j : M) e) '' D),
      realSecondForm (B.phaseRealChartMap j e.symm F) dy dy x ≠ 0 ∧
      normalize (realSecondForm (B.phaseRealChartMap j e.symm F) dy dy x) ≠ -n.inPhase (j : M) e x) :
    ∃ (V : Set Base) (A : SmoothingAtlas M) (i : A.centers)
      (f : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (U : Set Base),
      IsOpen V ∧ IsCompact (closure V) ∧
      (surfacePhaseChart (j : M) e) '' closure D ⊆ V ∧ closure V ⊆ Ω ∧
      (i : M) = (j : M) ∧ (∀ x, f x = e x) ∧ (∀ x, f.symm x = e.symm x) ∧
      ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ f.symm ∧
      (∀ p ∈ closure D, 0 < A.weight i p) ∧
      (∀ k p, p ∈ tsupport (A.weight k) → A.outer k =ᶠ[𝓝 p] (fun _ => 1)) ∧
      (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ f.source ∧
      MapsTo f f.source (baseEquiv ⁻¹' V) ∧
      closure D ⊆ (surfacePhaseChart (i : M) f).source ∧
      IsOpen U ∧ closure V ⊆ U ∧ U ⊆ Ω ∧
      ContDiffOn ℝ ∞ (n.inPhase (j : M) e) U ∧
      (∀ x ∈ U, Function.Injective (fderiv ℝ (A.phaseRealChartMap i f.symm F) x)) ∧
      (∀ x ∈ U, coordDeriv dx (A.phaseRealChartMap i f.symm F) x ⬝ᵥ n.inPhase (j : M) e x = 0 ∧
        coordDeriv dy (A.phaseRealChartMap i f.symm F) x ⬝ᵥ n.inPhase (j : M) e x = 0 ∧
        n.inPhase (j : M) e x ⬝ᵥ n.inPhase (j : M) e x = 1) ∧
      (∀ x ∈ U, 0 < coordinateMetricHessian
        (inducedCoordinateMetric (A.phaseRealChartMap i f.symm F)) Prod.fst x dy dy) ∧
      ∀ x ∈ closure V \ ((surfacePhaseChart (j : M) e) '' D),
        realSecondForm (A.phaseRealChartMap i f.symm F) dy dy x ≠ 0 ∧
        normalize (realSecondForm (A.phaseRealChartMap i f.symm F) dy dy x) ≠ -n.inPhase (j : M) e x := by
  let E := surfacePhaseChart (j : M) e
  have hDc : IsCompact (closure D) := isClosed_closure.isCompact
  obtain ⟨hED,hEDcl,_hEDfront,hEDc⟩ := compact_phase_disk_geometry E hD hDc hDs
  have hEDΩ : closure (E '' D) ⊆ Ω := by rwa [hEDcl]
  have hgram : ∀ x ∈ Ω, NormalFrame.gramDet
      (coordDeriv dx (B.phaseRealChartMap j e.symm F) x)
      (coordDeriv dy (B.phaseRealChartMap j e.symm F) x) ≠ 0 := by
    intro x hx
    have hh := B.phase_gram_at_source j e he hi hF
      (E.map_target (hΩe hx)) (hactive x hx)
    change NormalFrame.gramDet _ _ ≠ 0 at hh
    have heq := E.right_inv (hΩe hx)
    change baseEquiv (e (chart (j : M) (E.symm x))) = x at heq
    rwa [heq] at hh
  obtain ⟨V,hV,hVc,hDV,hVΩ,hzero,_hcross⟩ := GeometryPreservation.primitive_boundary_collar
    (B.phaseRealChartMap_smooth j hi hF.1) hΩ hED hEDc hEDΩ hgram
    ((n.inPhase_smooth (j : M) e hi).mono hΩe) hboundary
    (fun _ : Fin 0 => (∅ : Set Base)) (fun _ => isClosed_empty)
    (fun _ : Fin 0 => (fun _ : Base => (0 : Base))) (fun _ => contDiff_const)
    (fun i => Fin.elim0 i)
  have hDV' : E '' closure D ⊆ V := by rwa [← hEDcl]
  obtain ⟨A,i,f,hij,hfe,hfi,hfs,hfis,hw,houter,hcover,hsource,hDf,hplateau⟩ :=
    adapted_phase_primitive_atlas (j : M) e he hi hDc (subset_closure hqD) hDs hV hVc hDV'
      (hVΩ.trans hΩe)
  have hΩA : Ω ⊆ (surfacePhaseChart (i : M) e).target := by rwa [hij]
  have hpA : ∀ x ∈ closure V,
      A.outer i =ᶠ[𝓝 ((surfacePhaseChart (i : M) e).symm x)] (fun _ => 1) := by
    simpa only [hij] using hplateau
  have hcvA : ∀ x ∈ Ω, ∀ v : Base, v ≠ 0 →
      0 < coordinateMetricHessian (coordinateMetric g (i : M)) phi
        (coordinateChart (i : M) ((surfacePhaseChart (i : M) e).symm x)) v v := by
    simpa only [hij] using hconvex
  obtain ⟨U,hU,hVU,hUΩ,hn,hI,hN,hH⟩ := A.primitive_outer_geometry i hF n e he hi
    hphi hphase hΩ hVΩ hΩA hpA hcvA
  have hm : A.phaseRealChartMap i f.symm F = A.phaseRealChartMap i e.symm F := by
    rw [show (f.symm : JetPolynomial.Base → JetPolynomial.Base) = e.symm from funext hfi]
  have hn' : n.inPhase (i : M) e = n.inPhase (j : M) e := by rw [hij]
  refine ⟨V,A,i,f,U,hV,hVc,hDV',hVΩ,hij,hfe,hfi,hfs,hfis,hw,houter,hcover,hsource,hDf,
    hU,hVU,hUΩ,?_,?_,?_,?_,?_⟩
  · rwa [hn'] at hn
  · rwa [hm]
  · rw [hm]
    simpa only [hn'] using hN
  · rwa [hm]
  · intro x hx
    rw [hm,A.phase_second_of_common_outer B i j hij e F (hΩe (hVΩ hx.1))
      (hplateau x hx.1) (hactive x (hVΩ hx.1)) dy dy]
    exact hzero x hx

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.adapted_primitive_geometry_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.adapted_primitive_geometry_oai.{u_1}
