-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.geometric_normal_extension
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:35:27.180807+00:00
-- url     : https://prove2.me/submissions/c5efee62-c2c2-4d31-8d35-ade8070aee22

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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI011
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_compact_surface_boundary_matching
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_compact_surface_phase_exterior_preservation
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_finite_curve_disk_normal

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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasPartition
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

namespace ClosedSurfaceR4
open Set PhaseGeometry SmallModes RealModes PhaseGrid

lemma finite_positive_threshold {ι : Type*} [Fintype ι] (v : ι → ℝ) (hv : ∀ i, 0 < v i) :
    ∃ z : ℝ, 0 < z ∧ z ≤ 1 ∧ ∀ i, z ≤ v i := by
  classical
  let s : Finset ℝ := insert 1 (Finset.univ.image v)
  have hs : s.Nonempty := ⟨1,Finset.mem_insert_self _ _⟩
  refine ⟨s.min' hs,?_,Finset.min'_le s 1 (Finset.mem_insert_self _ _),?_⟩
  · have hm := s.min'_mem hs
    simp only [s,Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and] at hm
    rcases hm with he | ⟨i,hi⟩
    · rw [he]; norm_num
    · rw [← hi]; exact hv i
  · intro i
    exact Finset.min'_le s (v i) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))

end ClosedSurfaceR4

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
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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
local instance coordinateFiberSpace_rdffae5_1 : NormedSpace ℝ TensorFiber := inferInstance
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
local instance chartReadSectionNormed_rdffae5_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance chartReadSectionSpace_rdffae5_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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
local instance metricReferenceSectionNormed_rdffae5_1 (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricReferenceSectionSpace_rdffae5_1 (p : M) :
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
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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
local instance metricReadExactDualSmul_rdffae5_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReadExactFiberNormed
local instance metricReadExactSectionNormed_rdffae5_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricReadExactSectionSpace_rdffae5_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
local instance metricJetsFiberNormed_rdffae5_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance metricJetsFiberSpace_rdffae5_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance metricJetsDualAdd_rdffae5_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance metricJetsDualSmul_rdffae5_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance metricJetsSectionNormed_rdffae5_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricJetsSectionSpace_rdffae5_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_JetMetricCoordinatePullback
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
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
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_BoundaryNormalMatching
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform strict data for the interior/exterior normal interpolation.
The new canonical yy normal and the exterior normal both pair positively
with every later curve meeting the support boundary. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

lemma profilePreferred_real (F : RField 4) (z : ℝ) (p : Base) :
    profilePreferred (realBoundaryProfile F z p) = normalize (realSecondForm F dy dy p) := rfl

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_GeometricNormalExtension
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Complete the global preferred-normal construction from the original
boundary crossing data and the local normal produced by the exact primitive. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes SmallModes NormalFrame VelocityFrame GeometryPreservation
variable {M κ : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] [Fintype κ]
namespace SmoothingAtlas
variable (A B : SmoothingAtlas M)

theorem geometric_normal_extension_oai
    {g : SmoothMetric M} {F : M → Space} (hF : IsSmoothIsometricImmersion M g F)
    (n : PreferredNormal F)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (curves : κ → PhaseBoundaryCurve B)
    (hold : ∀ k p, p ∈ (curves k).carrier → (curves k).second F p ≠ 0 ∧
      spaceCoordinates (n.vector p) ≠ -normalize ((curves k).second F p))
    (i : A.centers) (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {D : Set M} (hD : IsOpen D) (hDr : interior (closure D) = D)
    (hDs : closure D ⊆ (chart (i : M)).source)
    (hDe : MapsTo (chart (i : M)) (closure D) e.source)
    (hDw : ∀ p ∈ closure D, A.weight i p ≠ 0)
    (E : Set M) (hE : E.Finite) (hEf : Disjoint E (frontier D))
    (v : κ → SmallModes.Base → SmallModes.Base) (hv : ∀ k, Continuous (v k))
    (hvector : ∀ k p, p ∈ (curves k).carrier → p ∈ closure D →
      v k (baseEquiv (e (chart (i : M) p))) =
        fderiv ℝ (surfacePhaseTransition ((curves k).index : M) (curves k).phase (i : M) e)
          ((curves k).coordinate p) dy)
    (hboundary : ∀ p ∈ frontier D,
      realSecondForm (A.phaseRealChartMap i e.symm F) dy dy
        (baseEquiv (e (chart (i : M) p))) ≠ 0 ∧
      spaceCoordinates (n.vector p) ≠ -normalize (realSecondForm (A.phaseRealChartMap i e.symm F)
        dy dy (baseEquiv (e (chart (i : M) p)))))
    (hpositive : ∀ k p, p ∈ (curves k).carrier → p ∈ frontier D →
      0 < (curves k).second F p ⬝ᵥ spaceCoordinates (n.vector p))
    (hcross : ∀ k p, p ∈ (curves k).carrier → p ∈ frontier D →
      let q := baseEquiv (e (chart (i : M) p))
      let H := A.phaseRealChartMap i e.symm F
      0 < orderedCrossing H dy (v k q) q
        (coordinateGaussianCurvature (realMetric H dx dx) (realMetric H dx dy) (realMetric H dy dy) q)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ∀ h : SmoothMetric M, IsSmoothIsometricImmersion M h W →
      ∀ b d : ℝ, 0 ≤ b → 0 ≤ d → b+d < ρ →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 d (W-V) →
      (∀ p ∉ closure D, V =ᶠ[𝓝 p] G) →
      ∀ z : ℝ, ∀ U₀ : Set SmallModes.Base, IsOpen U₀ → ∀ ν : SmallModes.Base → Vec,
      ContDiffOn ℝ ∞ ν U₀ →
      (∀ x ∈ U₀, ν x ⬝ᵥ ν x = 1) →
      (∀ x ∈ U₀, ∀ w : SmallModes.Base,
        SmallModes.coordDeriv w (A.phaseRealChartMap i e.symm W) x ⬝ᵥ ν x = 0) →
      MapsTo (fun p => baseEquiv (e (chart (i : M) p))) (closure D) U₀ →
      (∀ p ∈ frontier D, ν (baseEquiv (e (chart (i : M) p))) =
        profilePreferred (realBoundaryProfile (A.phaseRealChartMap i e.symm W) z
          (baseEquiv (e (chart (i : M) p))))) →
      (∀ k p, p ∈ (curves k).carrier → p ∈ D →
        let q := baseEquiv (e (chart (i : M) p))
        realSecondForm (A.phaseRealChartMap i e.symm W) (v k q) (v k q) q ≠ 0 ∧
        ν q ≠ -normalize (realSecondForm (A.phaseRealChartMap i e.symm W) (v k q) (v k q) q)) →
      ∃ N : PreferredNormal W,
        (∀ k p, p ∈ (curves k).carrier → (curves k).second W p ≠ 0 ∧
          spaceCoordinates (N.vector p) ≠ -normalize ((curves k).second W p)) ∧
        ∀ p ∈ E, (p ∈ D → N.vector p = A.phaseNormalLift i e ν p) ∧
          (p ∉ D → N.vector p = A.unitProjectedNormalField W n.vector p) := by
  classical
  have hsource : closure D ⊆ ((chart (i : M)).trans e).source :=
    fun p hp => ⟨hDs hp,hDe hp⟩
  have hread {h : SmoothMetric M} {W : M → Space} (hW : IsSmoothIsometricImmersion M h W)
      (k : κ) (p : M) (hp : p ∈ (curves k).carrier) (hpD : p ∈ closure D) :
      (curves k).second W p =
        realSecondForm (A.phaseRealChartMap i e.symm W)
          (v k (baseEquiv (e (chart (i : M) p))))
          (v k (baseEquiv (e (chart (i : M) p))))
          (baseEquiv (e (chart (i : M) p))) := by
    rw [(curves k).second_transition A i e he hi hW hp (hsource hpD) (hDw p hpD),
      hvector k p hp hpD]
  obtain ⟨r,hr,hglue⟩ := A.finite_curve_disk_normal B hF n houter curves hold i e he hi
    hD hDr hDs hDe hDw E hE hEf
  obtain ⟨a,ha,hanti⟩ := A.compact_surface_phase_exterior_preservation A hF n houter i e he hi
    (isClosed_frontier.isCompact) (fun p hp => hsource (frontier_subset_closure hp))
    (fun p hp => hDw p (frontier_subset_closure hp))
    (fun p hp => (hboundary p hp).1) (fun p hp => (hboundary p hp).2)
  have hpair (k : κ) := A.compact_surface_boundary_matching hF n houter i e he hi
    ((curves k).compact.inter_right isClosed_frontier)
    (fun p hp => hsource (frontier_subset_closure hp.2))
    (fun p hp => hDw p (frontier_subset_closure hp.2)) (v k) (hv k)
    (fun p hp => (hboundary p hp.2).1) (fun p hp => (hboundary p hp.2).2)
    (fun p hp => by dsimp only; rw [← hread hF k p hp.1 (frontier_subset_closure hp.2)]; exact hpositive k p hp.1 hp.2)
    (fun p hp => hcross k p hp.1 hp.2)
  choose t ht hpair' using hpair
  obtain ⟨s,hs,_,hst⟩ := finite_positive_threshold t ht
  refine ⟨min r (min a s),lt_min hr (lt_min ha hs),?_⟩
  intro G V W hG hV h hW b d hb hd hbd hGF hWV hext z U₀ hU₀ ν hν hunit hnormal hDU hcanonical hlocal
  have hbd_r := hbd.trans_le (min_le_left r (min a s))
  have hbd_a := hbd.trans_le ((min_le_right r (min a s)).trans (min_le_left a s))
  have hbd_s := hbd.trans_le ((min_le_right r (min a s)).trans (min_le_right a s))
  have hclosure (p : M) (hp : p ∈ frontier D) : p ∈ closure (closure D)ᶜ := by
    rw [closure_compl,hDr]
    exact hD.frontier_eq ▸ hp |>.2
  apply hglue G V W hG hV h hW b d hb hd hbd_r hGF hWV hext U₀ hU₀ ν hν hunit hnormal hDU
  · intro p hp
    rw [hcanonical p hp,profilePreferred_real]
    exact (hanti G V W hG hV hW.1 b d hb hd hbd_a hGF hWV (closure D)ᶜ hext p
      ⟨hp,hclosure p hp⟩).2.2
  · intro k p hp hpD
    rw [hread hW k p hp (subset_closure hpD)]
    exact hlocal k p hp hpD
  · intro k p hp hpD
    rw [hread hW k p hp (frontier_subset_closure hpD),hcanonical p hpD]
    have hh := hpair' k G V W hG hV hW.1 b d hb hd (hbd_s.trans_le (hst k))
      hGF hWV (closure D)ᶜ hext p ⟨⟨hp,hpD⟩,hclosure p hpD⟩ z
    exact ⟨hh.2,hh.1⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.geometric_normal_extension_oai.{u_1, u_2} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.geometric_normal_extension_oai.{u_1, u_2}
