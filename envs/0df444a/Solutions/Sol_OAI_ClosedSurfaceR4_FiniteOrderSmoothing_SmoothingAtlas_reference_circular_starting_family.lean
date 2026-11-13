-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.reference_circular_starting_family
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:34:57.606197+00:00
-- url     : https://prove2.me/submissions/66ee70d8-f391-4ee8-b130-05d715e01bad

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
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
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
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
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI010
import Definitions.Def_OAIQ249SI011
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_nonempty
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_PhaseBoundaryCurve_crossing_pos_of_coordinate_crossings
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_global_cubic_remainder_bound
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_phase_gram_at_source
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_induced_metric_upper_bound
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_uniform_prepared_spherical_immersion

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



lemma WeightedBound.mono_order {U : Set E} {s C : ℝ} {m r : ℕ} {f : E → F}
    (h : WeightedBound U s m C f) (hr : r ≤ m) : WeightedBound U s r C f :=
  fun j hj => h j (hj.trans hr)


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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ChartModel
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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

lemma coordinateCenter_mem (p : M) : coordinateCenter p ∈ coordinateDomain p := by
  simp [coordinateCenter, coordinateDomain]

lemma coordinateMap_at_center (F : M → Space) (p : M) :
    coordinateMap F p (coordinateCenter p) = spaceCoordinates (F p) := by
  simp [coordinateMap, coordinateCenter]

lemma coordinateMap_smoothOn [IsManifold planeModel ∞ M] {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (p : M) :
    ContDiffOn ℝ ∞ (coordinateMap F p) (coordinateDomain p) := by
  apply ContMDiffOn.contDiffOn
  have hChart := contMDiffOn_extChartAt_symm (I := planeModel) (n := (∞ : ℕ∞ω)) p
  have h1 := hF.comp_contMDiffOn hChart
  have h2 := spaceCoordinates.contDiff.contMDiff.comp_contMDiffOn h1
  exact h2.comp planeCoordinates.symm.contDiff.contMDiff.contMDiffOn
    (fun x hx => hx)

lemma mfderiv_coordinateMap_center {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (p : M) :
    fderiv ℝ (coordinateMap F p) (coordinateCenter p) =
      spaceCoordinates.toContinuousLinearMap.comp
        ((mfderiv planeModel spaceModel F p).comp
          planeCoordinates.symm.toContinuousLinearMap) := by
  have hd := (hF p).mdifferentiableAt (by simp)
  have heq : mfderiv planeModel spaceModel F p =
      fderiv ℝ (F ∘ (extChartAt planeModel p).symm) (extChartAt planeModel p p) := by
    simpa [writtenInExtChartAt, planeModel, spaceModel, chartAt_self_eq,
      differentiableWithinAt_univ] using hd.mfderiv
  have h0 : DifferentiableAt ℝ (F ∘ (extChartAt planeModel p).symm)
      (extChartAt planeModel p p) := by
    simpa [writtenInExtChartAt, planeModel, spaceModel, chartAt_self_eq,
      differentiableWithinAt_univ] using
      hd.differentiableWithinAt_writtenInExtChartAt
  have h1 : HasFDerivAt (spaceCoordinates ∘ F ∘ (extChartAt planeModel p).symm)
      (spaceCoordinates.toContinuousLinearMap.comp
        (fderiv ℝ (F ∘ (extChartAt planeModel p).symm) (extChartAt planeModel p p)))
      (planeCoordinates.symm (coordinateCenter p)) := by
    simpa [coordinateCenter] using spaceCoordinates.hasFDerivAt.comp
      (extChartAt planeModel p p) h0.hasFDerivAt
  have hc := h1.comp (coordinateCenter p) planeCoordinates.symm.hasFDerivAt
  rw [heq]
  have hc' := hc.fderiv
  simp only [coordinateMap, Function.comp_assoc, ContinuousLinearMap.comp_assoc] at hc' ⊢
  exact hc'

lemma coordinateMap_immersion_center {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (p : M)
    (hImm : Function.Injective (mfderiv planeModel spaceModel F p)) :
    Function.Injective (fderiv ℝ (coordinateMap F p) (coordinateCenter p)) := by
  rw [mfderiv_coordinateMap_center hF p]
  exact spaceCoordinates.injective.comp (hImm.comp planeCoordinates.symm.injective)

end ClosedSurfaceR4

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

lemma coordinateChart_apply (p q : M) : coordinateChart p q = chartCoordinates p q := rfl

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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasMargins
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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




end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasPhases
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasImmersionGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SphericalJets
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The radial normal of a spherical surface immersion.  The identities are for
actual Fréchet derivatives and the orthogonal projection defining the second
fundamental form, not an abstract second-jet model.
-/

noncomputable section

open scoped ContDiff

namespace ClosedSurfaceR4.SphericalJets

lemma derivative_apply {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    (x v w : Plane) :
    fderiv ℝ (fun y => fderiv ℝ F y w) x v =
      fderiv ℝ (fderiv ℝ F) x v w := by
  have hDF := (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x
  rw [fderiv_clm_apply hDF (differentiableAt_const w)]
  simp

theorem radial_secondForm_decomposition (F : Plane → Space) (x v w : Plane) :
    secondForm F x v w = sphericalSecondForm F x v w +
      (inner ℝ (fderiv ℝ F x v) (fderiv ℝ F x w)) • (-F x) := by
  simp only [sphericalSecondForm, smul_neg, add_neg_cancel_right]

lemma firstDerivative_scale {F : Plane → Space} (hF : ContDiff ℝ ∞ F) (r : ℝ) (x : Plane) :
    fderiv ℝ (fun y => r • F y) x = r • fderiv ℝ F x :=
  fderiv_const_smul (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x) r

lemma secondDerivative_scale {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    (r : ℝ) (x v w : Plane) :
    fderiv ℝ (fderiv ℝ (fun y => r • F y)) x v w =
      r • fderiv ℝ (fderiv ℝ F) x v w := by
  have he : fderiv ℝ (fun y => r • F y) = fun y => r • fderiv ℝ F y := by
    funext y
    exact firstDerivative_scale hF r y
  rw [he]
  change fderiv ℝ (r • fderiv ℝ F) x v w = _
  rw [fderiv_const_smul
    ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) x) r]
  rfl

lemma normalSpace_scale {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    {r : ℝ} (hr : r ≠ 0) (x : Plane) :
    normalSpace (fun y => r • F y) x = normalSpace F x := by
  unfold normalSpace
  rw [firstDerivative_scale hF r x]
  change (LinearMap.range (r • (fderiv ℝ F x).toLinearMap))ᗮ = _
  rw [LinearMap.range_smul _ _ hr]

theorem secondForm_scale {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    {r : ℝ} (hr : r ≠ 0) (x v w : Plane) :
    secondForm (fun y => r • F y) x v w = r • secondForm F x v w := by
  unfold secondForm
  simp only [normalSpace_scale hF hr, secondDerivative_scale hF, map_smul]

/-- Equation `spherical-radial-form` for the actual second fundamental form.
The scaled induced metric appears in the coefficient of the inward radial
normal, as in the manuscript. -/
theorem scaled_spherical_radial_form {F : Plane → Space} (hF : ContDiff ℝ ∞ F)
    {r : ℝ} (hr : r ≠ 0) (x v w : Plane) :
    secondForm (fun y => r • F y) x v w = r • sphericalSecondForm F x v w +
      (r⁻¹ * inner ℝ (fderiv ℝ (fun y => r • F y) x v)
        (fderiv ℝ (fun y => r • F y) x w)) • (-F x) := by
  rw [secondForm_scale hF hr, radial_secondForm_decomposition F,
    firstDerivative_scale hF r x]
  simp only [smul_apply, real_inner_smul_left,
    real_inner_smul_right, smul_add, smul_smul]
  congr 1
  congr 1
  field_simp

end ClosedSurfaceR4.SphericalJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasNormalizationBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed C2 atlas budget for radial normalization. A smooth extension
through zero is used only outside the region contributing to localization. -/
noncomputable section
open Set Metric Manifold
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SphericalJets WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma exists_weighted_bound (m : ℕ) {H : M → Space}
    (hH : ContMDiff planeModel spaceModel ∞ H) :
    ∃ C : ℝ, 0 ≤ C ∧ A.WeightedBound 1 m C H := by
  classical
  choose C hC hb using fun i : A.centers => compact_smooth_bound
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hH)
    (localize_compact (i : M) (A.weight_support i) H) m
  exact ⟨∑ i, C i,Finset.sum_nonneg (fun i _ => hC i),fun i =>
    (hb i).mono_const (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CenteredAtlasDifferentials
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered quadratic phase covectors expressed through actual chart
transitions, with the Jacobian nondegeneracy needed for parameter selection. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma coordinateTransition_det_ne (q p : M) {x : CurvePlane}
    (hx : x ∈ (coordinateTransition q p).source) :
    coordDet (fderiv ℝ (coordinateTransition q p) x) ≠ 0 := by
  let e := coordinateTransition q p
  exact coordDet_fderiv_ne_zero_of_local_inverse e.open_source e.open_target
    (coordinateTransition_smoothOn q p) (coordinateTransition_symm_smoothOn q p)
    e.mapsTo (fun y hy => e.left_inv hy) hx

end ClosedSurfaceR4.PhaseGeometry

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_EuclideanChartRead
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth Euclidean representatives agree with the actual chart map near
points where a partition weight is nonzero. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma euclideanChartRead_smooth (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) :
    ContDiff ℝ ∞ (A.euclideanChartRead i F) :=
  (A.vectorChartRead_smooth i hF).comp (EuclideanSpace.equiv (Fin 2) ℝ).contDiff

omit [CompactSpace M] in
lemma euclideanChartRead_eq (i : A.centers) (F : M → Space) :
    A.euclideanChartRead i F = (chartAt Plane (i : M)).target.indicator
      (fun x => (A.outer i ((chartAt Plane (i : M)).symm x))^2 •
        F ((chartAt Plane (i : M)).symm x)) := by
  funext x
  by_cases hx : x ∈ (chartAt Plane (i : M)).target
  · simp [euclideanChartRead,vectorChartRead,localize,chart,hx]
    rfl
  · simp [euclideanChartRead,vectorChartRead,localize,chart,hx]

omit [CompactSpace M] in
lemma outer_one_chart_germ (i : A.centers) {p : M} (hp : A.weight i p ≠ 0) :
    (fun y => A.outer i ((chartAt Plane (i : M)).symm y)) =ᶠ[𝓝 (chartAt Plane (i : M) p)]
      (fun _ => (1 : ℝ)) := by
  have hps : p ∈ (chartAt Plane (i : M)).source := by
    simpa only [chart_source] using A.weight_support i (subset_tsupport _ hp)
  have hpt := (chartAt Plane (i : M)).map_source hps
  have hc : ContinuousAt (fun y => A.weight i ((chartAt Plane (i : M)).symm y))
      (chartAt Plane (i : M) p) :=
    (A.weight_smooth i).continuous.continuousAt.comp
      (((chartAt Plane (i : M)).continuousOn_symm _ hpt).continuousAt
        ((chartAt Plane (i : M)).open_target.mem_nhds hpt))
  have hn : ∀ᶠ y in 𝓝 (chartAt Plane (i : M) p),
      A.weight i ((chartAt Plane (i : M)).symm y) ≠ 0 :=
    hc.eventually_ne (by simpa only [(chartAt Plane (i : M)).left_inv hps] using hp)
  exact hn.mono fun y hy => A.outer_one i _ (subset_tsupport _ hy)

omit [CompactSpace M] in
lemma euclideanChartRead_germ (i : A.centers) (F : M → Space) {p : M}
    (hp : A.weight i p ≠ 0) :
    A.euclideanChartRead i F =ᶠ[𝓝 (chartAt Plane (i : M) p)]
      F ∘ (chartAt Plane (i : M)).symm := by
  have hps : p ∈ (chartAt Plane (i : M)).source := by
    simpa only [chart_source] using A.weight_support i (subset_tsupport _ hp)
  filter_upwards [(chartAt Plane (i : M)).open_target.mem_nhds
    ((chartAt Plane (i : M)).map_source hps),A.outer_one_chart_germ i hp] with y hy ho
  rw [A.euclideanChartRead_eq,indicator_of_mem hy,ho,one_pow,one_smul]
  rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RealNormalProjectionBridge
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate normal projection is the Euclidean orthogonal projection
onto the complement of the actual tangent image. -/
noncomputable section
open Set
open scoped Matrix
namespace ClosedSurfaceR4
open RealModes SmallModes

lemma realNormalPart_starProjection (L : SmallModes.Base →L[ℝ] Space) (W : Space)
    (hD : NormalFrame.gramDet (spaceCoordinates (L dx)) (spaceCoordinates (L dy)) ≠ 0) :
    realNormalPart (spaceCoordinates (L dx)) (spaceCoordinates (L dy)) (spaceCoordinates W) =
      spaceCoordinates ((LinearMap.range L.toLinearMap)ᗮ.starProjection W) := by
  let X := spaceCoordinates (L dx)
  let Y := spaceCoordinates (L dy)
  let Z := spaceCoordinates W
  let a := ((Y ⬝ᵥ Y)*(X ⬝ᵥ Z)-(X ⬝ᵥ Y)*(Y ⬝ᵥ Z))/NormalFrame.gramDet X Y
  let b := ((X ⬝ᵥ X)*(Y ⬝ᵥ Z)-(X ⬝ᵥ Y)*(X ⬝ᵥ Z))/NormalFrame.gramDet X Y
  let V := W-a • L dx-b • L dy
  have hV : spaceCoordinates V = realNormalPart X Y Z := by
    simp only [V,map_sub,map_smul,realNormalPart]
    rfl
  have hperp := realNormalPart_perp X Y Z hD
  have hinnerx : inner ℝ (L dx) V = 0 := by
    rw [← spaceCoordinates_dot,hV]
    exact hperp.1
  have hinnery : inner ℝ (L dy) V = 0 := by
    rw [← spaceCoordinates_dot,hV]
    exact hperp.2
  have hm : V ∈ (LinearMap.range L.toLinearMap)ᗮ := by
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨v,rfl⟩
    change inner ℝ (L v) V = 0
    rw [base_eq_basis v,map_add,map_smul,map_smul,inner_add_left,
      real_inner_smul_left,real_inner_smul_left,hinnerx,hinnery]
    ring
  have ht : W-V ∈ LinearMap.range L.toLinearMap := by
    refine ⟨a • dx+b • dy,?_⟩
    change L (a • dx+b • dy) = W-V
    simp only [map_add,map_smul,V]
    module
  have hp : W-V ∈ ((LinearMap.range L.toLinearMap)ᗮ)ᗮ :=
    (LinearMap.range L.toLinearMap).le_orthogonal_orthogonal ht
  have he := Submodule.eq_starProjection_of_mem_orthogonal hm hp
  exact hV.symm.trans (congrArg spaceCoordinates he.symm)

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SphericalCoordinateSecondForm
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linear chart coordinates preserve the actual second normal projection. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4
open RealModes SmallModes

lemma spherical_secondForm_coordinates {F : Plane → Space}
    (hF : ContDiff ℝ ∞ F) (x v w : SmallModes.Base)
    (hD : NormalFrame.gramDet
      (spaceCoordinates (fderiv ℝ F (planeCoordinates.symm x) (planeCoordinates.symm dx)))
      (spaceCoordinates (fderiv ℝ F (planeCoordinates.symm x) (planeCoordinates.symm dy))) ≠ 0) :
    realSecondForm (spaceCoordinates ∘ F ∘ planeCoordinates.symm) v w x =
      spaceCoordinates (SphericalJets.secondForm F (planeCoordinates.symm x)
        (planeCoordinates.symm v) (planeCoordinates.symm w)) := by
  let e := planeCoordinates.symm.toContinuousLinearMap
  let L := (fderiv ℝ F (e x)).comp e
  have hfirst (z u : SmallModes.Base) :
      coordDeriv u (spaceCoordinates ∘ F ∘ planeCoordinates.symm) z =
        spaceCoordinates (fderiv ℝ F (e z) (e u)) := by
    simp only [coordDeriv,fderiv_comp z spaceCoordinates.differentiableAt
      ((hF.differentiable (by simp) _).comp _ planeCoordinates.symm.differentiableAt),
      spaceCoordinates.fderiv,fderiv_comp z (hF.differentiable (by simp) _)
        planeCoordinates.symm.differentiableAt,planeCoordinates.symm.fderiv,
      ContinuousLinearMap.comp_apply]
    rfl
  have hsecond : coordDeriv v (coordDeriv w (spaceCoordinates ∘ F ∘ planeCoordinates.symm)) x =
      spaceCoordinates (fderiv ℝ (fderiv ℝ F) (e x) (e v) (e w)) := by
    have he : coordDeriv w (spaceCoordinates ∘ F ∘ planeCoordinates.symm) =
        spaceCoordinates ∘ (fun z => fderiv ℝ F z (e w)) ∘ planeCoordinates.symm := by
      funext z
      exact hfirst z w
    rw [he]
    have hd := ((hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp) (e x))
    rw [coordDeriv,fderiv_comp x spaceCoordinates.differentiableAt,
      spaceCoordinates.fderiv]
    · have hcomp : fderiv ℝ ((fun z => fderiv ℝ F z (e w)) ∘ planeCoordinates.symm) x =
          (fderiv ℝ (fun z => fderiv ℝ F z (e w)) (e x)).comp e :=
        ((hd.clm_apply (differentiableAt_const (e w))).hasFDerivAt.comp x e.hasFDerivAt).fderiv
      rw [hcomp]
      simp only [ContinuousLinearMap.comp_apply]
      rw [SphericalJets.derivative_apply hF]
      rfl
    · exact (hd.clm_apply (differentiableAt_const (e w))).comp x planeCoordinates.symm.differentiableAt
  have hr : LinearMap.range L.toLinearMap = LinearMap.range (fderiv ℝ F (e x)).toLinearMap := by
    ext z
    constructor
    · rintro ⟨u,rfl⟩
      exact ⟨e u,rfl⟩
    · rintro ⟨u,rfl⟩
      refine ⟨planeCoordinates u,?_⟩
      change fderiv ℝ F (e x) (planeCoordinates.symm (planeCoordinates u)) = _
      rw [ContinuousLinearEquiv.symm_apply_apply]
      rfl
  rw [realSecondForm,hfirst x dx,hfirst x dy,hsecond]
  have hp := realNormalPart_starProjection L
    (fderiv ℝ (fderiv ℝ F) (e x) (e v) (e w)) hD
  simp only [hr] at hp
  exact hp

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityCoordinateData
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth velocity coordinates and their calibrated collar values. -/
noncomputable section
open Set
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma dot_normalize_self {v : Vec} (hv : v ≠ 0) :
    v ⬝ᵥ normalize v = Real.sqrt (v ⬝ᵥ v) := by
  have hp := dot_self_pos hv
  have hn := (Real.sqrt_pos.mpr hp).ne'
  simp only [normalize, dotProduct_smul, smul_eq_mul]
  apply (inv_mul_eq_iff_eq_mul₀ hn).mpr
  nlinarith [Real.sq_sqrt hp.le]

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PureRadialCrossing
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At a prepared point, a pure radial second form gives the strict ordered
crossing inequality even for proportional nonzero tangent directions. -/
noncomputable section
open scoped Matrix
namespace ClosedSurfaceR4.VelocityFrame
open RealModes SmallModes NormalFrame

lemma normalize_positive_smul {n : Vec} (hn : n ⬝ᵥ n = 1) {c : ℝ} (hc : 0 < c) :
    normalize (c • n) = n := by
  have hs : Real.sqrt (c*c) = c := by
    nlinarith [Real.sq_sqrt (show 0 ≤ c*c by positivity),Real.sqrt_nonneg (c*c)]
  simp only [normalize,smul_dotProduct,dotProduct_smul,smul_eq_mul,hn,mul_one,hs,smul_smul,
    inv_mul_cancel₀ hc.ne',one_smul]

lemma orderedCrossing_pure_radial {F : RField 4} (p v w : Base) (n : Vec)
    {r : ℝ} (hr : 0 < r) (hn : n ⬝ᵥ n = 1)
    (hv : coordDeriv v F p ≠ 0) (hw : coordDeriv w F p ≠ 0)
    (hvv : realSecondForm F v v p =
      (r⁻¹*(coordDeriv v F p ⬝ᵥ coordDeriv v F p)) • n)
    (hvw : realSecondForm F v w p =
      (r⁻¹*(coordDeriv v F p ⬝ᵥ coordDeriv w F p)) • n) :
    orderedCrossing F v w p ((r⁻¹)^2) =
      (r⁻¹)^2*(coordDeriv v F p ⬝ᵥ coordDeriv v F p)*
        (coordDeriv w F p ⬝ᵥ coordDeriv w F p) ∧
      0 < orderedCrossing F v w p ((r⁻¹)^2) := by
  have hpos : 0 < r⁻¹*(coordDeriv v F p ⬝ᵥ coordDeriv v F p) :=
    mul_pos (inv_pos.mpr hr) (dot_self_pos hv)
  have he : orderedCrossing F v w p ((r⁻¹)^2) =
      (r⁻¹)^2*(coordDeriv v F p ⬝ᵥ coordDeriv v F p)*
        (coordDeriv w F p ⬝ᵥ coordDeriv w F p) := by
    simp only [orderedCrossing,hvv,hvw,normalize_positive_smul hn hpos,smul_dotProduct,
      smul_eq_mul,hn,mul_one,NormalFrame.gramDet]
    ring
  exact ⟨he,he.symm ▸ mul_pos (mul_pos (sq_pos_of_pos (inv_pos.mpr hr))
    (dot_self_pos hv)) (dot_self_pos hw)⟩

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PreparedRadialSecondForm
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact pure-radial second form at a prepared spherical point, in
the same coordinates used by the ordered boundary invariant. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4
open RealModes SmallModes SphericalJets

lemma sphereCoordinates_firstDerivative {F : Plane → Space}
    (hF : ContDiff ℝ ∞ F) (x v : SmallModes.Base) :
    coordDeriv v (spaceCoordinates ∘ F ∘ planeCoordinates.symm) x =
      spaceCoordinates (fderiv ℝ F (planeCoordinates.symm x) (planeCoordinates.symm v)) := by
  simp only [coordDeriv,fderiv_comp x spaceCoordinates.differentiableAt
    ((hF.differentiable (by simp) _).comp _ planeCoordinates.symm.differentiableAt),
    spaceCoordinates.fderiv,fderiv_comp x (hF.differentiable (by simp) _)
      planeCoordinates.symm.differentiableAt,planeCoordinates.symm.fderiv,
    ContinuousLinearMap.comp_apply]
  rfl

lemma scaled_flat_spherical_secondForm {F : Plane → Space}
    (hF : ContDiff ℝ ∞ F) {r : ℝ} (hr : r ≠ 0) (x : SmallModes.Base)
    (hflat : ∀ v w, sphericalSecondForm F (planeCoordinates.symm x) v w = 0)
    (hD : NormalFrame.gramDet (coordDeriv dx (scaledSphereCoordinates F r) x)
      (coordDeriv dy (scaledSphereCoordinates F r) x) ≠ 0) (v w : SmallModes.Base) :
    realSecondForm (scaledSphereCoordinates F r) v w x =
      (r⁻¹*(coordDeriv v (scaledSphereCoordinates F r) x ⬝ᵥ
        coordDeriv w (scaledSphereCoordinates F r) x)) •
          spaceCoordinates (-F (planeCoordinates.symm x)) := by
  have hs : ContDiff ℝ ∞ (fun y => r • F y) := hF.const_smul r
  have hd : ∀ u, coordDeriv u (scaledSphereCoordinates F r) x =
      spaceCoordinates (fderiv ℝ (fun y => r • F y) (planeCoordinates.symm x) (planeCoordinates.symm u)) :=
    fun u => sphereCoordinates_firstDerivative hs x u
  have hD' := hD
  rw [hd dx,hd dy] at hD'
  change realSecondForm (spaceCoordinates ∘ (fun y => r • F y) ∘ planeCoordinates.symm) v w x = _
  rw [spherical_secondForm_coordinates hs x v w hD',scaled_spherical_radial_form hF hr,
    hflat,smul_zero,zero_add,map_smul,hd v,hd w,spaceCoordinates_dot]

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PureRadialGauss
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The curvature in the initial ordered crossing invariant is the actual
Gaussian curvature computed from the induced metric, rather than a freely
specified scalar. -/
noncomputable section
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.RealModes
open SmallModes NormalFrame VelocityFrame

lemma coordinateGauss_pure_radial {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (p : Base) (n : RVec 4) {r : ℝ}
    (hn : n ⬝ᵥ n = 1)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0)
    (hB : ∀ v w, realSecondForm F v w p =
      (r⁻¹*(coordDeriv v F p ⬝ᵥ coordDeriv w F p)) • n) :
    coordinateGauss (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p =
      (r⁻¹)^2*gramDet (coordDeriv dx F p) (coordDeriv dy F p) := by
  rw [← gauss_metric_identity hF p hD,hB dx dx,hB dy dy,hB dx dy]
  simp only [smul_dotProduct,dotProduct_smul,smul_eq_mul,hn,mul_one,NormalFrame.gramDet]
  ring

lemma coordinateGaussianCurvature_pure_radial {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (p : Base) (n : RVec 4) {r : ℝ} (hn : n ⬝ᵥ n = 1)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0)
    (hB : ∀ v w, realSecondForm F v w p =
      (r⁻¹*(coordDeriv v F p ⬝ᵥ coordDeriv w F p)) • n) :
    coordinateGaussianCurvature (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p =
      (r⁻¹)^2 := by
  rw [coordinateGaussianCurvature,coordinateGauss_pure_radial hF p n hn hD hB]
  change (r⁻¹)^2*gramDet (coordDeriv dx F p) (coordDeriv dy F p)/
    gramDet (coordDeriv dx F p) (coordDeriv dy F p) = _
  exact mul_div_cancel_right₀ _ hD

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalSecondFormNaturality
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact second-form identities through a local smooth coordinate change. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry

lemma pure_radial_comp_on {F : RField 4} {φ : Base → Base}
    {U V : Set Base} (hU : IsOpen U) (hV : IsOpen V)
    (hF : ContDiffOn ℝ ∞ F V) (hφ : ContDiffOn ℝ ∞ φ U)
    {p : Base} (hp : p ∈ U) (hφp : φ p ∈ V)
    (hD : NormalFrame.gramDet (coordDeriv dx F (φ p)) (coordDeriv dy F (φ p)) ≠ 0)
    (hdet : coordDet (fderiv ℝ φ p) ≠ 0) (n : RVec 4) (r : ℝ)
    (hB : ∀ v w, realSecondForm F v w (φ p) =
      (r⁻¹*(coordDeriv v F (φ p) ⬝ᵥ coordDeriv w F (φ p))) • n)
    (v w : Base) :
    realSecondForm (F ∘ φ) v w p =
      (r⁻¹*(coordDeriv v (F ∘ φ) p ⬝ᵥ coordDeriv w (F ∘ φ) p)) • n := by
  rw [realSecondForm_comp_on hU hV hF hφ hp hφp v w hD hdet,hB]
  have hf := ((hF _ hφp).contDiffAt (hV.mem_nhds hφp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hg := ((hφ _ hp).contDiffAt (hU.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  simp only [coordDeriv,fderiv_comp p hf hg,ContinuousLinearMap.comp_apply]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalIntrinsicCrossing
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Intrinsic curvature and ordered crossings depend only on the local
smooth germ. This applies the radial calculation in an actual chart. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.RealModes
open SmallModes NormalFrame VelocityFrame PhaseGeometry

lemma realMetric_eventuallyEq {F G : RField 4} {p : Base} (h : F =ᶠ[𝓝 p] G)
    (v w : Base) : realMetric F v w =ᶠ[𝓝 p] realMetric G v w := by
  filter_upwards [coordDeriv_eventuallyEq h v,coordDeriv_eventuallyEq h w] with x hv hw
  simp only [realMetric,hv,hw]

private lemma scalarDeriv_eventuallyEq {f g : Base → ℝ} {p : Base}
    (h : f =ᶠ[𝓝 p] g) (v : Base) : coordDeriv v f =ᶠ[𝓝 p] coordDeriv v g :=
  h.fderiv.mono fun _ hx => congrArg (fun D : Base →L[ℝ] ℝ => D v) hx

lemma coordinateGauss_congr_germ {E F G E' F' G' : Base → ℝ} {p : Base}
    (hE : E =ᶠ[𝓝 p] E') (hF : F =ᶠ[𝓝 p] F') (hG : G =ᶠ[𝓝 p] G') :
    coordinateGauss E F G p = coordinateGauss E' F' G' p := by
  simp only [coordinateGauss,hE.eq_of_nhds,hF.eq_of_nhds,hG.eq_of_nhds,
    (scalarDeriv_eventuallyEq hE dx).eq_of_nhds,
    (scalarDeriv_eventuallyEq hE dy).eq_of_nhds,
    (scalarDeriv_eventuallyEq hF dx).eq_of_nhds,
    (scalarDeriv_eventuallyEq hF dy).eq_of_nhds,
    (scalarDeriv_eventuallyEq hG dx).eq_of_nhds,
    (scalarDeriv_eventuallyEq hG dy).eq_of_nhds,
    (scalarDeriv_eventuallyEq (scalarDeriv_eventuallyEq hF dy) dx).eq_of_nhds,
    (scalarDeriv_eventuallyEq (scalarDeriv_eventuallyEq hE dy) dy).eq_of_nhds,
    (scalarDeriv_eventuallyEq (scalarDeriv_eventuallyEq hG dx) dx).eq_of_nhds]

lemma inducedCurvature_congr_germ {F G : RField 4} {p : Base} (h : F =ᶠ[𝓝 p] G) :
    coordinateGaussianCurvature (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p =
    coordinateGaussianCurvature (realMetric G dx dx) (realMetric G dx dy) (realMetric G dy dy) p := by
  have hE := realMetric_eventuallyEq h dx dx
  have hF := realMetric_eventuallyEq h dx dy
  have hG := realMetric_eventuallyEq h dy dy
  simp only [coordinateGaussianCurvature,coordinateGauss_congr_germ hE hF hG,
    hE.eq_of_nhds,hF.eq_of_nhds,hG.eq_of_nhds]

lemma coordinateGaussianCurvature_pure_radial_on {F : RField 4} {U : Set Base}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) {p : Base} (hp : p ∈ U)
    (n : RVec 4) {r : ℝ} (hn : n ⬝ᵥ n = 1)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0)
    (hB : ∀ v w, realSecondForm F v w p =
      (r⁻¹*(coordDeriv v F p ⬝ᵥ coordDeriv w F p)) • n) :
    coordinateGaussianCurvature (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p =
      (r⁻¹)^2 := by
  obtain ⟨G,hG,_,_,he⟩ := smooth_extension_near hU hF.contMDiffOn hp
  have hd : gramDet (coordDeriv dx G p) (coordDeriv dy G p) ≠ 0 := by
    simpa only [(coordDeriv_eventuallyEq he dx).eq_of_nhds,
      (coordDeriv_eventuallyEq he dy).eq_of_nhds] using hD
  have hb : ∀ v w, realSecondForm G v w p =
      (r⁻¹*(coordDeriv v G p ⬝ᵥ coordDeriv w G p)) • n := by
    intro v w
    simpa only [(realSecondForm_eventuallyEq he v w).eq_of_nhds,
      (coordDeriv_eventuallyEq he v).eq_of_nhds,
      (coordDeriv_eventuallyEq he w).eq_of_nhds] using hB v w
  rw [← inducedCurvature_congr_germ he]
  exact coordinateGaussianCurvature_pure_radial hG.contDiff p n hn hd hb

lemma orderedCrossing_intrinsic_pure_radial_on {F : RField 4} {U : Set Base}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) {p : Base} (hp : p ∈ U)
    (v w : Base) (n : RVec 4) {r : ℝ} (hr : 0 < r) (hn : n ⬝ᵥ n = 1)
    (hD : gramDet (coordDeriv dx F p) (coordDeriv dy F p) ≠ 0)
    (hB : ∀ a b, realSecondForm F a b p =
      (r⁻¹*(coordDeriv a F p ⬝ᵥ coordDeriv b F p)) • n)
    (hv : coordDeriv v F p ≠ 0) (hw : coordDeriv w F p ≠ 0) :
    0 < orderedCrossing F v w p
      (coordinateGaussianCurvature (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) p) := by
  rw [coordinateGaussianCurvature_pure_radial_on hU hF hp n hn hD hB]
  exact (orderedCrossing_pure_radial p v w n hr hn hv hw (hB v v) (hB v w)).2

end ClosedSurfaceR4.RealModes

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
local instance quadraticAtlasSectionSpace_r583964_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ScaledInitialMap
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The initial contraction of an approximate immersion. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.initialFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.initialDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.initialDualSmul
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.initialFiberNormed
local instance initialSectionNormed_r583964_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance initialSectionSpace_r583964_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma inducedTensor_const_smul {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (a : ℝ) :
    inducedTensor (a • F) = a^2 • inducedTensor F := by
  funext p
  ext v w
  have hd : (mfderiv planeModel spaceModel (a • F) p : Plane →L[ℝ] Space) =
      a • (mfderiv planeModel spaceModel F p : Plane →L[ℝ] Space) :=
    const_smul_mfderiv ((hF p).mdifferentiableAt (by simp)) a
  change inner ℝ ((mfderiv planeModel spaceModel (a • F) p : Plane →L[ℝ] Space) v)
    ((mfderiv planeModel spaceModel (a • F) p : Plane →L[ℝ] Space) w) =
    a^2*inner ℝ (mfderiv planeModel spaceModel F p v) (mfderiv planeModel spaceModel F p w)
  have hv := congrArg (fun L : Plane →L[ℝ] Space => L (show Plane from v)) hd
  have hw := congrArg (fun L : Plane →L[ℝ] Space => L (show Plane from w)) hd
  change (mfderiv planeModel spaceModel (a • F) p v : Space) =
    a • (mfderiv planeModel spaceModel F p v : Space) at hv
  change (mfderiv planeModel spaceModel (a • F) p w : Space) =
    a • (mfderiv planeModel spaceModel F p w : Space) at hw
  calc
    _ = inner ℝ (a • (mfderiv planeModel spaceModel F p v : Space))
        (a • (mfderiv planeModel spaceModel F p w : Space)) :=
      congrArg₂ (fun x y : Space => inner ℝ x y) hv hw
    _ = _ := by rw [real_inner_smul_left,real_inner_smul_right]; ring

end ClosedSurfaceR4.FiniteOrderSmoothing

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

lemma second_eq (F : M → Space) {p : M} (hp : p ∈ c.carrier) :
    c.second F p = realSecondForm (B.phaseRealChartMap c.index c.phase.symm F)
      dy dy (c.coordinate p) := by
  apply B.phaseCurveSecondField_eq c.index c.phase c.cutoff F (fun _ => dy) (fun _ => dy)
    (c.source hp).1
  · exact B.outer_one c.index p (subset_tsupport _ (c.active p hp))
  · exact c.cutoff_properties.2.2.1 _ ⟨p,hp,rfl⟩

end PhaseBoundaryCurve
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ConstantNormBoundaryGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The initial inward normal has a strictly positive pairing with every
nonzero directional second form, at every point of a constant-radius sphere. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.RealModes
open SmallModes NormalFrame VelocityFrame

lemma constant_norm_radial_first {F : RField 4} {R : ℝ} {x : Base}
    (hF : DifferentiableAt ℝ F x) (hR : ∀ y, F y ⬝ᵥ F y = R) (v : Base) :
    F x ⬝ᵥ coordDeriv v F x = 0 := by
  have he : (fun y => F y ⬝ᵥ F y) = fun _ => R := funext hR
  have hd : coordDeriv v (fun y => F y ⬝ᵥ F y) x = 0 := by
    rw [he]
    simp [coordDeriv]
  rw [real_partial_dot hF hF,dotProduct_comm (coordDeriv v F x) (F x)] at hd
  linarith

lemma constant_norm_radial_second {F : RField 4} {U : Set Base} {R : ℝ}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (hR : ∀ y, F y ⬝ᵥ F y = R)
    {x : Base} (hx : x ∈ U) (v w : Base) :
    F x ⬝ᵥ coordDeriv v (coordDeriv w F) x =
      -(coordDeriv v F x ⬝ᵥ coordDeriv w F x) := by
  have hFx := (hF x hx).contDiffAt (hU.mem_nhds hx)
  have he : (fun y => F y ⬝ᵥ coordDeriv w F y) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact constant_norm_radial_first
      (((hF y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hR w
  have hd : coordDeriv v (fun y => F y ⬝ᵥ coordDeriv w F y) x = 0 := by
    change fderiv ℝ _ x v = 0
    rw [he.fderiv_eq]
    simp
  rw [real_partial_dot (hFx.differentiableAt (by simp))
    ((contDiffAt_coordDeriv hFx w).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))] at hd
  linarith

lemma constant_norm_secondForm_inward {F : RField 4} {U : Set Base} {R : ℝ}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (hR : ∀ y, F y ⬝ᵥ F y = R)
    {x : Base} (hx : x ∈ U) (v w : Base) :
    realSecondForm F v w x ⬝ᵥ (-F x) = coordDeriv v F x ⬝ᵥ coordDeriv w F x := by
  have hFx := ((hF x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hX : coordDeriv dx F x ⬝ᵥ (-F x) = 0 := by
    rw [dotProduct_neg,dotProduct_comm,constant_norm_radial_first hFx hR,neg_zero]
  have hY : coordDeriv dy F x ⬝ᵥ (-F x) = 0 := by
    rw [dotProduct_neg,dotProduct_comm,constant_norm_radial_first hFx hR,neg_zero]
  unfold realSecondForm realNormalPart
  simp only [sub_dotProduct,smul_dotProduct,smul_eq_mul,hX,hY,mul_zero,sub_zero]
  rw [dotProduct_neg,dotProduct_comm,constant_norm_radial_second hU hF hR hx,neg_neg]

lemma positive_pairing_excludes_antipode {X n : Vec} (hp : 0 < X ⬝ᵥ n) :
    X ≠ 0 ∧ normalize X ≠ -n := by
  have hn : X ≠ 0 := by
    intro hz
    rw [hz,zero_dotProduct] at hp
    exact lt_irrefl _ hp
  refine ⟨hn,?_⟩
  intro he
  have hs := dot_normalize_self hn
  rw [he,dotProduct_neg] at hs
  linarith [Real.sqrt_nonneg (X ⬝ᵥ X)]

theorem constant_norm_boundary_geometry {F : RField 4} {U : Set Base} {R r : ℝ}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (hR : ∀ y, F y ⬝ᵥ F y = R)
    (hr : 0 < r) {x : Base} (hx : x ∈ U)
    (hI : Function.Injective (fderiv ℝ F x)) {v : Base} (hv : v ≠ 0) :
    0 < realSecondForm F v v x ⬝ᵥ (r⁻¹ • (-F x)) ∧
    realSecondForm F v v x ≠ 0 ∧
    normalize (realSecondForm F v v x) ≠ -(r⁻¹ • (-F x)) := by
  have hd : coordDeriv v F x ≠ 0 := by
    intro hz
    exact hv (hI (by simpa only [coordDeriv,map_zero] using hz))
  have hp : 0 < realSecondForm F v v x ⬝ᵥ (r⁻¹ • (-F x)) := by
    rw [dotProduct_smul,constant_norm_secondForm_inward hU hF hR hx]
    exact mul_pos (inv_pos.mpr hr) (dot_self_pos hd)
  exact ⟨hp,positive_pairing_excludes_antipode hp⟩

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseSphericalGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Initial inward radial positivity in every fixed nonlinear phase chart.
It supplies the whole-curve part of the finite boundary invariant. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes SmallModes VelocityFrame NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace PhaseBoundaryCurve
variable {B : SmoothingAtlas M} (c : PhaseBoundaryCurve B)

theorem spherical_second_positive {G : M → Space} {r : ℝ} (hr : 0 < r)
    (hunit : ∀ p, ‖G p‖ = 1) {g : SmoothMetric M}
    (hF : IsSmoothIsometricImmersion M g (r • G))
    {p : M} (hp : p ∈ c.carrier) :
    0 < c.second (r • G) p ⬝ᵥ spaceCoordinates (-G p) ∧
      c.second (r • G) p ≠ 0 ∧
      spaceCoordinates (-G p) ≠ -normalize (c.second (r • G) p) := by
  let H := surfacePhaseMap (c.index : M) c.phase (r • G)
  let x := c.coordinate p
  have hps : p ∈ (surfacePhaseChart (c.index : M) c.phase).source := c.source hp
  have hx : x ∈ (surfacePhaseChart (c.index : M) c.phase).target :=
    (surfacePhaseChart (c.index : M) c.phase).map_source hps
  have hback : (surfacePhaseChart (c.index : M) c.phase).symm x = p :=
    (surfacePhaseChart (c.index : M) c.phase).left_inv hps
  have hg := B.phaseRealChartMap_surface_germ c.index c.phase (r • G) hx
    (by rw [hback]; exact c.active p hp)
  have hHs : ContDiffOn ℝ ∞ H (surfacePhaseChart (c.index : M) c.phase).target := by
    apply ContMDiffOn.contDiffOn
    exact spaceCoordinates.contDiff.contMDiff.comp_contMDiffOn
      (hF.1.comp_contMDiffOn (surfacePhaseChart_symm_smooth (c.index : M) c.phase c.inverse_smooth))
  have hR : ∀ y, H y ⬝ᵥ H y = r^2 := by
    intro y
    simp only [H,surfacePhaseMap,Function.comp_apply,Pi.smul_apply,spaceCoordinates_dot]
    rw [real_inner_self_eq_norm_sq,norm_smul,Real.norm_eq_abs,hunit,mul_one,sq_abs]
  have hD : gramDet (coordDeriv dx H x) (coordDeriv dy H x) ≠ 0 := by
    change gramDet (fderiv ℝ H x dx) (fderiv ℝ H x dy) ≠ 0
    rw [← hg.fderiv_eq]
    exact B.phase_gram_at_source c.index c.phase c.smooth c.inverse_smooth hF (c.source hp) (c.active p hp)
  have hh := constant_norm_boundary_geometry (surfacePhaseChart (c.index : M) c.phase).open_target
    hHs hR hr hx (injective_of_gramDet_ne_zero _ hD) (show (dy : SmallModes.Base) ≠ 0 by simp [dy])
  have hrad : r⁻¹ • (-H x) = spaceCoordinates (-G p) := by
    change r⁻¹ • (-spaceCoordinates ((r • G) ((surfacePhaseChart (c.index : M) c.phase).symm x))) = _
    rw [hback]
    simp only [Pi.smul_apply,map_smul,map_neg,smul_neg,smul_smul,inv_mul_cancel₀ hr.ne',one_smul]
  rw [hrad] at hh
  have hsec : c.second (r • G) p = realSecondForm H dy dy x :=
    (c.second_eq (r • G) hp).trans (realSecondForm_eventuallyEq hg dy dy).eq_of_nhds
  rw [hsec]
  refine ⟨hh.1,hh.2.1,?_⟩
  intro hbad
  apply hh.2.2
  simp only [hbad,neg_neg]

end PhaseBoundaryCurve
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_UniformMetricPathBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First-order metric bounds fixed before finite spherical modifications. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.pathBoundFiberSpace
local instance pathBoundDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.pathBoundDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.pathBoundFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.pathBoundFiberNormed
local instance pathBoundSectionNormed_r583964_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance pathBoundSectionSpace_r583964_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma uniform_induced_tensor_bound {C : ℝ} (hC : 0 ≤ C) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ F : M → Space, ContMDiff planeModel spaceModel ∞ F →
      A.WeightedBound 1 (m+1) C F → A.TensorWeightedBound 1 m D (inducedTensor F) := by
  obtain ⟨D,hD,hbound⟩ := A.global_cubic_remainder_bound m 0 C le_rfl hC
  refine ⟨D,hD,fun F hF hb => ?_⟩
  have hz : A.WeightedBound 1 (m+1) (0*(1*1)) (0 : M → Space) := by
    intro i
    simp only [zero_mul]
    change WeightedEstimates.WeightedBound univ 1 (m+1) 0 (localize (i : M) (A.weight i) 0)
    have he : localize (i : M) (A.weight i) (0 : M → Space) = 0 := by
      funext x
      by_cases hx : x ∈ (chart (i : M)).target <;> simp [localize,hx]
    rw [he]
    exact weightedBound_zero univ 1 (m+1)
  have ht := hbound 1 1 zero_lt_one le_rfl zero_le_one le_rfl 0 F
    contMDiff_const hF hz (by simpa only [one_pow,mul_one] using hb)
  have he : linearMetricTensor (0 : M → Space) F = 0 := by
    funext p
    ext v w
    change inner ℝ (show Space from mfderiv planeModel spaceModel (0 : M → Space) p v)
        (show Space from mfderiv planeModel spaceModel F p w) +
      inner ℝ (show Space from mfderiv planeModel spaceModel F p v)
        (show Space from mfderiv planeModel spaceModel (0 : M → Space) p w) = 0
    have hd : (mfderiv planeModel spaceModel (fun _ : M => (0 : Space)) p :
        TangentSpace planeModel p →L[ℝ] Space) = 0 := mfderiv_const
    change inner ℝ ((mfderiv planeModel spaceModel (fun _ : M => (0 : Space)) p) v)
        (show Space from mfderiv planeModel spaceModel F p w) +
      inner ℝ (show Space from mfderiv planeModel spaceModel F p v)
        ((mfderiv planeModel spaceModel (fun _ : M => (0 : Space)) p) w) = 0
    rw [hd]
    change inner ℝ (0 : Space) (show Space from mfderiv planeModel spaceModel F p w) +
      inner ℝ (show Space from mfderiv planeModel spaceModel F p v) (0 : Space) = 0
    rw [inner_zero_left,inner_zero_right,add_zero]
  simpa only [he,zero_add,one_pow,div_one,mul_one] using ht

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FiniteSurfaceCorrection
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite spherical jet corrections on the actual surface. The disjoint
coordinate balls are chosen before restoring and normalizing the corrections. -/
noncomputable section
open Set Filter Metric Manifold
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.SphericalJets

lemma sphericalSecondForm_congr_germ {F G : Plane → Space} {p : Plane}
    (h : F =ᶠ[𝓝 p] G) (v w : Plane) :
    sphericalSecondForm F p v w = sphericalSecondForm G p v w := by
  simp only [sphericalSecondForm,secondForm,normalSpace,h.eq_of_nhds,h.fderiv_eq,
    h.fderiv.fderiv_eq]

end ClosedSurfaceR4.SphericalJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_UniformSmallStartingMetric
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The initial spherical scale can be fixed before all finite modifications
so that the entire family of induced metrics is small in C1. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
local instance smallStartFiberNormed_r583964_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance smallStartFiberSpace_r583964_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance smallStartDualAdd_r583964_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance smallStartDualSmul_r583964_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance smallStartSectionNormed_r583964_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance smallStartSectionSpace_r583964_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem uniform_small_scaled_metric (g : SmoothMetric M) {C ε : ℝ}
    (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧
      ∀ F : M → Space, ContMDiff planeModel spaceModel ∞ F →
        A.WeightedBound 1 2 C F →
        A.TensorWeightedBound 1 1 ε (inducedTensor (r • F)) ∧
        ∀ p v, inducedForm (r • F) p v v ≤ (1/2 : ℝ)*g.inner p v v := by
  obtain ⟨E,hE,hbound⟩ := A.uniform_induced_tensor_bound hC 1
  obtain ⟨D,hD,hupper⟩ := A.uniform_induced_metric_upper_bound g hC
  let a := min 1 (min (ε/(E+1)) (1/(2*(D+1))))
  have ha : 0 < a := lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  let r := Real.sqrt a
  have hr : 0 < r := Real.sqrt_pos.mpr ha
  have hr2 : r^2 = a := Real.sq_sqrt ha.le
  have hr1 : r ≤ 1 := by
    have : r^2 ≤ 1 := hr2 ▸ min_le_left _ _
    nlinarith
  have hsmall : r^2*E ≤ ε := by
    have hs : r^2 ≤ ε/(E+1) := hr2 ▸ (min_le_right _ _).trans (min_le_left _ _)
    have hh := (le_div_iff₀ (by positivity : 0 < E+1)).mp hs
    nlinarith [sq_nonneg r]
  have hshort : r^2*D ≤ (1/2 : ℝ) := by
    have hs : r^2 ≤ 1/(2*(D+1)) := hr2 ▸ (min_le_right _ _).trans (min_le_right _ _)
    have hh := (le_div_iff₀ (by positivity : 0 < 2*(D+1))).mp hs
    nlinarith [sq_nonneg r]
  refine ⟨r,hr,hr1,?_⟩
  intro F hF hb
  constructor
  · rw [inducedTensor_const_smul hF]
    have hs := A.tensorWeightedBound_const_smul (A.inducedTensor_smooth hF)
      (hbound F hF hb) (r^2)
    intro i
    apply (hs i).mono_const
    simpa only [abs_of_nonneg (sq_nonneg r)] using hsmall
  · intro p v
    have he := congrArg (fun T : ∀ p : M, CovariantTwoTensor p => T p v v)
      (inducedTensor_const_smul hF r)
    change inducedForm (r • F) p v v = r^2*inducedForm F p v v at he
    rw [he]
    have hu := hupper F hF (fun i => (hb i).mono_order (by omega)) p v
    have hg : 0 ≤ g.inner p v v := by
      by_cases hv : v = 0
      · simp [hv]
      · exact (g.pos p v hv).le
    exact (mul_le_mul_of_nonneg_left hu (sq_nonneg r)).trans
      (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hshort hg)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PreparedPointCoordinates
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A prepared spherical point has the exact radial second form in its
selected atlas chart, using a genuine smooth representative of the chart map. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold Matrix
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes SphericalJets
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem prepared_point_radial_form {G : M → Space}
    (hG : ContMDiff planeModel spaceModel ∞ G) {r : ℝ} (hr : r ≠ 0)
    (hI : ∀ p, Function.Injective (mfderiv planeModel spaceModel (r • G) p))
    (i : A.centers) {p : M} (hp : A.weight i p ≠ 0)
    (hflat : ∀ v w, sphericalSecondForm (G ∘ (chartAt Plane (i : M)).symm)
      (chartAt Plane (i : M) p) v w = 0) (v w : SmallModes.Base) :
    realSecondForm (coordinateMap (r • G) (i : M)) v w (coordinateChart (i : M) p) =
      (r⁻¹*(coordDeriv v (coordinateMap (r • G) (i : M)) (coordinateChart (i : M) p) ⬝ᵥ
        coordDeriv w (coordinateMap (r • G) (i : M)) (coordinateChart (i : M) p))) •
          spaceCoordinates (-G p) := by
  let F := A.euclideanChartRead i G
  let x := coordinateChart (i : M) p
  have hx : planeCoordinates.symm x = chartAt Plane (i : M) p := by
    simp [x,coordinateChart_apply,chartCoordinates]
  have he := A.euclideanChartRead_germ i G hp
  have hf : ContDiff ℝ ∞ F := A.euclideanChartRead_smooth i hG
  have hflatF : ∀ a b, sphericalSecondForm F (planeCoordinates.symm x) a b = 0 := by
    intro a b
    rw [hx]
    exact (sphericalSecondForm_congr_germ he a b).trans (hflat a b)
  have hs : scaledSphereCoordinates F r =ᶠ[𝓝 x] coordinateMap (r • G) (i : M) := by
    have ht : Tendsto planeCoordinates.symm (𝓝 x) (𝓝 (chartAt Plane (i : M) p)) := by
      rw [← hx]
      exact planeCoordinates.symm.continuous.continuousAt.tendsto
    filter_upwards [he.comp_tendsto ht] with y hy
    simp only [scaledSphereCoordinates,coordinateMap,Function.comp_apply,Pi.smul_apply]
    change F (planeCoordinates.symm y) = _ at hy
    dsimp only [F]
    dsimp only [F] at hy
    rw [hy]
    rfl
  have hscaled : ContMDiff planeModel spaceModel ∞ (r • G) :=
    (show ContMDiff planeModel 𝓘(ℝ) ∞ (fun _ : M => r) from contMDiff_const).smul hG
  have hps : p ∈ (coordinateChart (i : M)).source := by
    simpa only [coordinateChart_source,chart_source] using A.weight_support i (subset_tsupport _ hp)
  have hD := gramDet_ne_zero_of_injective _
    (coordinateMap_injective_of_immersion hscaled hI (i : M)
      (by rw [← coordinateChart_target]; exact (coordinateChart (i : M)).map_source hps))
  have hD' : NormalFrame.gramDet (coordDeriv dx (scaledSphereCoordinates F r) x)
      (coordDeriv dy (scaledSphereCoordinates F r) x) ≠ 0 := by
    rw [(coordDeriv_eventuallyEq hs dx).eq_of_nhds,(coordDeriv_eventuallyEq hs dy).eq_of_nhds]
    exact hD
  have hvalue : F (planeCoordinates.symm x) = G p := by
    dsimp only [F]
    rw [hx,he.eq_of_nhds]
    exact congrArg G ((chartAt Plane (i : M)).left_inv (by simpa only [coordinateChart_source] using hps))
  have hh := scaled_flat_spherical_secondForm hf hr x hflatF hD' v w
  rw [(realSecondForm_eventuallyEq hs v w).eq_of_nhds,
    (coordDeriv_eventuallyEq hs v).eq_of_nhds,
    (coordDeriv_eventuallyEq hs w).eq_of_nhds,hvalue] at hh
  exact hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_RadialFormCoordinateTransfer
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pure radial form is independent of the selected surface chart. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold Matrix
namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma radial_form_coordinate_transfer {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (q p a : M) (haq : a ∈ (coordinateChart q).source)
    (hap : a ∈ (coordinateChart p).source)
    (hD : NormalFrame.gramDet (coordDeriv dx (coordinateMap F q) (coordinateChart q a))
      (coordDeriv dy (coordinateMap F q) (coordinateChart q a)) ≠ 0)
    (n : RVec 4) (r : ℝ)
    (hB : ∀ v w, realSecondForm (coordinateMap F q) v w (coordinateChart q a) =
      (r⁻¹*(coordDeriv v (coordinateMap F q) (coordinateChart q a) ⬝ᵥ
        coordDeriv w (coordinateMap F q) (coordinateChart q a))) • n)
    (v w : Base) :
    realSecondForm (coordinateMap F p) v w (coordinateChart p a) =
      (r⁻¹*(coordDeriv v (coordinateMap F p) (coordinateChart p a) ⬝ᵥ
        coordDeriv w (coordinateMap F p) (coordinateChart p a))) • n := by
  have hx := coordinateTransition_mem_chart q p hap haq
  have he := coordinateTransition_apply_chart q p hap
  have ht : coordinateTransition q p (coordinateChart p a) ∈ coordinateDomain q := by
    rw [he,← coordinateChart_target]
    exact (coordinateChart q).map_source haq
  have hb := pure_radial_comp_on (coordinateTransition q p).open_source
    (coordinateDomain_open q) (coordinateMap_smoothOn hF q)
    (coordinateTransition_smoothOn q p) hx ht
    (by simpa only [he] using hD) (coordinateTransition_det_ne q p hx) n r
    (by simpa only [he] using hB) v w
  have hg := coordinateMap_transition_eventuallyEq F q p hx
  rw [(realSecondForm_eventuallyEq hg v w).eq_of_nhds,
    (coordDeriv_eventuallyEq hg v).eq_of_nhds,
    (coordDeriv_eventuallyEq hg w).eq_of_nhds] at hb
  exact hb

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SphericalInitialBoundary
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global inward normal of a scaled spherical immersion satisfies
the nonvanishing and antipode exclusions for every nonzero direction. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4
open SmallModes RealModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem spherical_initial_boundary_geometry {G : M → Space}
    (hG : ContMDiff planeModel spaceModel ∞ G) (hunit : ∀ p, ‖G p‖ = 1)
    {r : ℝ} (hr : 0 < r)
    (hI : ∀ p, Function.Injective (mfderiv planeModel spaceModel (r • G) p))
    (p : M) {v : SmallModes.Base} (hv : v ≠ 0) :
    0 < realSecondForm (coordinateMap (r • G) p) v v (coordinateCenter p) ⬝ᵥ
        spaceCoordinates (-G p) ∧
      realSecondForm (coordinateMap (r • G) p) v v (coordinateCenter p) ≠ 0 ∧
      normalize (realSecondForm (coordinateMap (r • G) p) v v (coordinateCenter p)) ≠
        -spaceCoordinates (-G p) := by
  have hs : ContMDiff planeModel spaceModel ∞ (r • G) :=
    (show ContMDiff planeModel 𝓘(ℝ) ∞ (fun _ : M => r) from contMDiff_const).smul hG
  have hR : ∀ y, coordinateMap (r • G) p y ⬝ᵥ coordinateMap (r • G) p y = r^2 := by
    intro y
    simp only [coordinateMap,Function.comp_apply,Pi.smul_apply,spaceCoordinates_dot]
    rw [real_inner_self_eq_norm_sq,norm_smul,Real.norm_eq_abs,hunit,mul_one,sq_abs]
  have hn : r⁻¹ • (-coordinateMap (r • G) p (coordinateCenter p)) =
      spaceCoordinates (-G p) := by
    rw [coordinateMap_at_center,Pi.smul_apply,map_smul,map_neg,smul_neg,smul_smul,
      inv_mul_cancel₀ hr.ne',one_smul]
  have hh := constant_norm_boundary_geometry (coordinateDomain_open p)
    (coordinateMap_smoothOn hs p) hR hr (coordinateCenter_mem p)
    (coordinateMap_immersion_center hs p (hI p)) hv
  simpa only [hn] using hh

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PreparedPointCrossings
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Initial crossing inequalities in every chart through a prepared point.
The curvature is the actual curvature of the scaled induced metric. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold Matrix
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes SphericalJets VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem prepared_point_crossings {G : M → Space}
    (hG : ContMDiff planeModel spaceModel ∞ G) (hunit : ∀ p, ‖G p‖ = 1)
    {r : ℝ} (hr : 0 < r)
    (hI : ∀ p, Function.Injective (mfderiv planeModel spaceModel (r • G) p))
    (i : A.centers) {p : M} (hp : A.weight i p ≠ 0)
    (hflat : ∀ v w, sphericalSecondForm (G ∘ (chartAt Plane (i : M)).symm)
      (chartAt Plane (i : M) p) v w = 0)
    (q : M) (hq : p ∈ (coordinateChart q).source) :
    (∀ v w, realSecondForm (coordinateMap (r • G) q) v w (coordinateChart q p) =
      (r⁻¹*(coordDeriv v (coordinateMap (r • G) q) (coordinateChart q p) ⬝ᵥ
        coordDeriv w (coordinateMap (r • G) q) (coordinateChart q p))) • spaceCoordinates (-G p)) ∧
    coordinateGaussianCurvature (realMetric (coordinateMap (r • G) q) dx dx)
      (realMetric (coordinateMap (r • G) q) dx dy)
      (realMetric (coordinateMap (r • G) q) dy dy) (coordinateChart q p) = (r⁻¹)^2 ∧
    ∀ v w : Base, v ≠ 0 → w ≠ 0 →
      0 < orderedCrossing (coordinateMap (r • G) q) v w (coordinateChart q p)
        (coordinateGaussianCurvature (realMetric (coordinateMap (r • G) q) dx dx)
          (realMetric (coordinateMap (r • G) q) dx dy)
          (realMetric (coordinateMap (r • G) q) dy dy) (coordinateChart q p)) := by
  have hs : ContMDiff planeModel spaceModel ∞ (r • G) :=
    (show ContMDiff planeModel 𝓘(ℝ) ∞ (fun _ : M => r) from contMDiff_const).smul hG
  have hi : p ∈ (coordinateChart (i : M)).source := by
    simpa only [coordinateChart_source,chart_source] using A.weight_support i (subset_tsupport _ hp)
  have hdi := coordinateMap_injective_of_immersion hs hI (i : M)
    (by rw [← coordinateChart_target]; exact (coordinateChart (i : M)).map_source hi)
  have hrad := A.prepared_point_radial_form hG hr.ne' hI i hp hflat
  have hB := radial_form_coordinate_transfer hs (i : M) q p hi hq
    (gramDet_ne_zero_of_injective _ hdi) (spaceCoordinates (-G p)) r hrad
  have hdom : coordinateChart q p ∈ coordinateDomain q := by
    rw [← coordinateChart_target]
    exact (coordinateChart q).map_source hq
  have hImm := coordinateMap_injective_of_immersion hs hI q hdom
  have hD := gramDet_ne_zero_of_injective _ hImm
  have hn : spaceCoordinates (-G p) ⬝ᵥ spaceCoordinates (-G p) = 1 := by
    rw [spaceCoordinates_dot,real_inner_self_eq_norm_sq,norm_neg,hunit]
    norm_num
  refine ⟨hB,coordinateGaussianCurvature_pure_radial_on (coordinateDomain_open q)
    (coordinateMap_smoothOn hs q) hdom _ hn hD hB,?_⟩
  intro v w hv hw
  apply orderedCrossing_intrinsic_pure_radial_on (coordinateDomain_open q)
    (coordinateMap_smoothOn hs q) hdom v w _ hr hn hD hB
  · intro hz
    exact hv (hImm (by simpa only [coordDeriv,map_zero] using hz))
  · intro hz
    exact hw (hImm (by simpa only [coordDeriv,map_zero] using hz))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ReferenceStartingFamily
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform finite-point spherical preparation on a prescribed atlas.
The same atlas can therefore be used for the circular boundary preparation. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SphericalJets
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem reference_small_metric_prepared_family (g : SmoothMetric M) {I : M → Space}
    (hI : ContMDiff planeModel spaceModel ∞ I) (hunit : ∀ p, ‖I p‖ = 1)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel I p))
    {η : ℝ} (hη : 0 < η) :
    ∃ r D c : ℝ,
      0 < r ∧ r ≤ 1 ∧ 0 ≤ D ∧ 0 < c ∧
      A.WeightedBound 1 2 D I ∧
      A.TensorWeightedBound 1 1 η (inducedTensor (r • I)) ∧
      (∀ p v, inducedForm (r • I) p v v ≤ (1/2 : ℝ)*g.inner p v v) ∧
      ∀ (P : Finset M) (ε : ℝ), 0 < ε →
      ∃ (a : P → A.centers) (G : M → Space) (n : PreferredNormal (r • G)),
        (∀ p, A.weight (a p) p ≠ 0) ∧ ContMDiff planeModel spaceModel ∞ G ∧
        (∀ p, ‖G p‖ = 1) ∧
        (∀ p, Function.Injective (mfderiv planeModel spaceModel (r • G) p)) ∧
        n.vector = (fun p => -G p) ∧
        A.WeightedBound 1 1 ε (G-I) ∧ A.WeightedBound 1 2 D G ∧
        (∀ p v, c*g.inner p v v ≤ inducedForm G p v v) ∧
        A.TensorWeightedBound 1 1 η (inducedTensor (r • G)) ∧
        (∀ p v, inducedForm (r • G) p v v ≤ (1/2 : ℝ)*g.inner p v v) ∧
        ∀ p : P, G p = I p ∧
          fderiv ℝ (G ∘ (chartAt Plane (a p : M)).symm) (chartAt Plane (a p : M) p) =
            fderiv ℝ (I ∘ (chartAt Plane (a p : M)).symm) (chartAt Plane (a p : M) p) ∧
          ∀ v w, sphericalSecondForm (G ∘ (chartAt Plane (a p : M)).symm)
            (chartAt Plane (a p : M) p) v w = 0 := by
  obtain ⟨D,c,hD,hc,hprep⟩ := A.uniform_prepared_spherical_immersion g hI hunit hImm
  obtain ⟨D₀,hD₀,hIbound⟩ := A.exists_weighted_bound 2 hI
  let E := D+D₀
  have hE : 0 ≤ E := add_nonneg hD hD₀
  have hIb : A.WeightedBound 1 2 E I := fun i => (hIbound i).mono_const (by dsimp [E] <;> linarith)
  obtain ⟨r,hr,hr1,hsmall⟩ := A.uniform_small_scaled_metric g hE hη
  have href := hsmall I hI hIb
  refine ⟨r,E,c,hr,hr1,hE,hc,hIb,href.1,href.2,?_⟩
  intro P ε hε
  obtain ⟨a,G,ha,hG,hu,hGI,hclose,hbound,hlower,hflat⟩ := hprep P ε hε
  have hGb : A.WeightedBound 1 2 E G := fun i => (hbound i).mono_const (by dsimp [E] <;> linarith)
  let n := (sphericalPreferredNormal hG hu).const_smul hG r
  have hscaled : ∀ p, Function.Injective (mfderiv planeModel spaceModel (r • G) p) := by
    intro p v w h
    have hd := const_smul_mfderiv ((hG p).mdifferentiableAt (by simp)) r
    have he := congrArg (fun z : Space => r⁻¹ • z) h
    rw [hd] at he
    change r⁻¹ • (r • (mfderiv planeModel spaceModel G p v)) =
      r⁻¹ • (r • (mfderiv planeModel spaceModel G p w)) at he
    simp only [smul_smul,inv_mul_cancel₀ hr.ne',one_smul] at he
    exact hGI p he
  exact ⟨a,G,n,ha,hG,hu,hscaled,rfl,hclose,hGb,hlower,
    (hsmall G hG hGb).1,(hsmall G hG hGb).2,hflat⟩

end SmoothingAtlas
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ReferenceBoundaryStartingFamily
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reference and finite-point starting immersions with the same scale,
including the actual finite boundary invariant. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem reference_circular_starting_family_oai (g : SmoothMetric M) {I : M → Space}
    (hI : ContMDiff planeModel spaceModel ∞ I) (hunit : ∀ p, ‖I p‖ = 1)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel I p))
    {η : ℝ} (hη : 0 < η) :
    ∃ r D c : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 ≤ D ∧ 0 < c ∧
      A.WeightedBound 1 2 D I ∧
      A.TensorWeightedBound 1 1 η (inducedTensor (r • I)) ∧
      (∀ p v, inducedForm (r • I) p v v ≤ (1/2 : ℝ)*g.inner p v v) ∧
      ∀ (n : ℕ) (B : SmoothingAtlas M) (d : CircularFamilyGeometry B (Fin n))
        (ε : ℝ), 0 < ε →
      ∃ (G : M → Space) (g₀ : SmoothMetric M) (normal : PreferredNormal (r • G)),
        ContMDiff planeModel spaceModel ∞ G ∧ (∀ p, ‖G p‖ = 1) ∧
        IsSmoothIsometricImmersion M g₀ (r • G) ∧
        g₀.inner = inducedTensor (r • G) ∧ Nonempty (MetricGoodPhaseData g₀ (r • G)) ∧
        normal.vector = (fun p => -G p) ∧
        A.WeightedBound 1 1 ε (G-I) ∧ A.WeightedBound 1 2 D G ∧
        (∀ p v, c*g.inner p v v ≤ g₀.inner p v v) ∧
        A.TensorWeightedBound 1 1 η g₀.inner ∧
        (∀ p v, g₀.inner p v v ≤ (1/2 : ℝ)*g.inner p v v) ∧
        FiniteBoundaryGeometry d.curves (boundaryCrossingSet d.curves univ) (r • G) normal := by
  obtain ⟨r,D,c,hr,hr1,hD,hc,hIbound,hImetric,hIshort,hprep⟩ :=
    A.reference_small_metric_prepared_family g hI hunit hImm hη
  refine ⟨r,D,r^2*c,hr,hr1,hD,mul_pos (sq_pos_of_pos hr) hc,
    hIbound,hImetric,hIshort,?_⟩
  intro n B d ε hε
  let E := (boundaryCrossingSet_finite d.curves univ d.pair_finite).toFinset
  obtain ⟨a,G,normal,ha,hG,hu,hGI,hn,hclose,hbound,hlower,hmetric,hshort,hflat⟩ := hprep E ε hε
  have hbase (p : M) (v : Base) (hv : v ≠ 0) :=
    spherical_initial_boundary_geometry hG hu hr hGI p hv
  have hs : ContMDiff planeModel spaceModel ∞ (r • G) :=
    (show ContMDiff planeModel 𝓘(ℝ) ∞ (fun _ : M => r) from contMDiff_const).smul hG
  let g₀ := A.immersionMetric hs hGI
  have hF : IsSmoothIsometricImmersion M g₀ (r • G) := ⟨hs,fun _ _ _ => rfl⟩
  have hdata : Nonempty (MetricGoodPhaseData g₀ (r • G)) :=
    MetricGoodPhaseData.nonempty g₀ hs hGI (fun p => ⟨dy,dy,
      (hbase p dy (by simp [dy])).2.1⟩)
  have hscaled (p : M) (v : TangentSpace planeModel p) :
      (r^2*c)*g.inner p v v ≤ g₀.inner p v v := by
    change (r^2*c)*g.inner p v v ≤ inducedTensor (r • G) p v v
    rw [inducedTensor_const_smul hG r]
    change (r^2*c)*g.inner p v v ≤ r^2*inducedForm G p v v
    calc
      _ = r^2*(c*g.inner p v v) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hlower p v) (sq_nonneg r)
  refine ⟨G,g₀,normal,hG,hu,hF,rfl,hdata,hn,hclose,hbound,hscaled,hmetric,hshort,?_⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro j p hp
    exact ((d.curves j).spherical_second_positive hr hu hF hp).2.1
  · intro j p hp
    rw [hn]
    exact ((d.curves j).spherical_second_positive hr hu hF hp).2.2
  · intro j k _ p _ hp _
    rw [hn]
    exact ((d.curves j).spherical_second_positive hr hu hF hp).1
  · intro j k _ p hp hj hk
    apply (d.curves j).crossing_pos_of_coordinate_crossings (d.curves k) hF hj hk
    have hsource : p ∈ (coordinateChart ((d.curves j).index : M)).source := by
      rw [coordinateChart_source,← chart_source]
      exact ((d.curves j).source hj).1
    have hpE : p ∈ E := by simpa only [E,Set.Finite.mem_toFinset] using hp
    exact (A.prepared_point_crossings hG hu hr hGI (a ⟨p,hpE⟩)
      (ha ⟨p,hpE⟩) (hflat ⟨p,hpE⟩).2.2 ((d.curves j).index : M) hsource).2.2

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.reference_circular_starting_family_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.reference_circular_starting_family_oai.{u_1}
