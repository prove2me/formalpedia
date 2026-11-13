-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_curve_disk_normal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:33:07.974383+00:00
-- url     : https://prove2.me/submissions/4ad20f46-e0c0-40b4-966d-9bc00087e824

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
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_PhaseBoundaryCurve_exterior_preservation
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_PhaseBoundaryCurve_second_smooth

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

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SecondForms
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
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseGeometry Set

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

namespace SmoothingAtlas

variable (A : SmoothingAtlas M)

variable [CompactSpace M]

omit [CompactSpace M] in
lemma restore_localize (i : A.centers) (f : M → V) (x : M) :
    restore (i : M) (A.outer i) (localize (i : M) (A.weight i) f) x =
      (A.weight i x) ^ 2 • f x := by
  by_cases hx : x ∈ (chart (i : M)).source
  · rw [restore, indicator_of_mem hx, localize_chart _ _ _ hx]
    by_cases hzero : A.weight i x = 0
    · simp only [hzero, zero_pow (by decide : 2 ≠ 0), zero_smul, smul_zero]
    · rw [A.outer_one i x (subset_tsupport _ hzero), one_smul]
  · have hz : A.weight i x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (A.weight_support i h))
    simp only [restore, indicator_of_notMem hx, hz, zero_pow (by decide : 2 ≠ 0), zero_smul]

omit [CompactSpace M] in
lemma sum_restore_localize (f : M → V) :
    (∑ i : A.centers, restore (i : M) (A.outer i) (localize (i : M) (A.weight i) f)) = f := by
  funext x
  simp only [Finset.sum_apply, A.restore_localize]
  rw [← Finset.sum_smul, A.partition, one_smul]

end SmoothingAtlas
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

lemma localize_add (p : M) (ψ : M → ℝ) (f g : M → V) :
    localize p ψ (f + g) = localize p ψ f + localize p ψ g := by
  funext x
  by_cases hx : x ∈ (chart p).target <;> simp [localize, hx, smul_add]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalizedCompositionBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed smooth cutoff and chart transition operators preserve weighted
norms with constants independent of the input and its scale. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set WeightedEstimates
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A compactly supported coordinate change costs a fixed constant in each
weighted derivative norm; it introduces no additional scale loss. -/
theorem compact_localized_composition_bound {O K : Set Base}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {χ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχK : tsupport χ ⊆ K)
    {T : Base → Base} (hT : ContDiffOn ℝ ∞ T O) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f →
      WeightedBound Set.univ s m C f →
      WeightedBound Set.univ s m (D * C) (fun x => χ x • f (T x)) := by
  obtain ⟨U, hU, hKU, hUO, hUc⟩ := exists_open_between_and_isCompact_closure hK hO hKO
  have hsub : U ⊆ O := subset_closure.trans hUO
  obtain ⟨A, hA, hbA⟩ := compact_coefficient_bound hO.uniqueDiffOn hUc hUO hχ.contDiffOn m
  obtain ⟨B, hB, hbB⟩ := compact_coefficient_bound hO.uniqueDiffOn hUc hUO hT m
  refine ⟨2 ^ m * A * ((m.factorial : ℝ) * B ^ m), by positivity, ?_⟩
  intro f s C hs hs1 hC hf hb
  have hTj : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ U,
      ‖iteratedFDerivWithin ℝ j T U x‖ ≤ B := by
    intro j _ hj x hx
    have ht : ContDiffAt ℝ (j : ℕ∞ω) T x :=
      (hT.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hO.mem_nhds (hsub hx))
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx]
    have h := hbB j hj x (subset_closure hx)
    rwa [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn ht (hsub hx)] at h
  have hχb : WeightedBound U s m A χ := by
    intro j hj x hx
    have ht : ContDiffAt ℝ (j : ℕ∞ω) χ x := (hχ.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx]
    have h := hbA j hj x (subset_closure hx)
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn ht (hsub hx)] at h
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hs.le hs1)).trans h
  have hc := hb.comp_coordinates hU.uniqueDiffOn uniqueDiffOn_univ hs hs1 hB hC
    (hT.mono hsub) hf.contDiffOn (fun _ _ => mem_univ _) hTj
  have hcomp : ContDiffOn ℝ ∞ (fun x => f (T x)) U :=
    hf.contDiffOn.comp (hT.mono hsub) (fun _ _ => mem_univ _)
  have hp := hχb.smul_real hU.uniqueDiffOn hs.le (zero_le_one.trans hA)
    (by positivity) hχ.contDiffOn hcomp hc
  have hlocal : ContDiffOn ℝ ∞ (fun x => χ x • f (T x)) U := hχ.contDiffOn.smul hcomp
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  by_cases hx : x ∈ U
  · have ht : ContDiffAt ℝ (j : ℕ∞ω) (fun x => χ x • f (T x)) x :=
      (hlocal.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hU.mem_nhds hx)
    have h := hp j hj x hx
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · have hxK : x ∉ K := fun hk => hx (hKU hk)
    have hxχ : x ∉ tsupport χ := fun hx' => hxK (hχK hx')
    have heq : (fun y => χ y • f (T y)) =ᶠ[𝓝 x] (fun _ => (0 : V)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxχ] with y hy
      simp only [Pi.zero_apply] at hy
      rw [hy, zero_smul]
    have hd := (heq.iteratedFDeriv ℝ j).self_of_nhds
    rw [hd]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero]
    positivity

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasWeightedBounds
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-atlas weighted norms and bounds for the actual restoration operator. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [IsManifold planeModel ∞ M] in
lemma localize_sum {ι : Type*} (b : Finset ι) (p : M) (ψ : M → ℝ) (f : ι → M → V) :
    localize p ψ (∑ i ∈ b, f i) = fun x => ∑ i ∈ b, localize p ψ (f i) x := by
  funext x
  by_cases hx : x ∈ (chart p).target <;>
    simp [localize, hx, Finset.sum_apply, Finset.smul_sum]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_VectorPlaneRestore
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restore coordinate-plane vector fields to a smooth global displacement,
with a fixed-atlas weighted estimate and no derivative loss. -/
noncomputable section
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base planeCoordinateIsometry weightedBound_comp_isometry)
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma vectorPlaneRestore_smooth (f : A.centers → SmallModes.Base → V)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) : ContMDiff planeModel 𝓘(ℝ, V) ∞ (A.vectorPlaneRestore f) := by
  have hh : ContMDiff planeModel 𝓘(ℝ, V) ∞
      (fun x => ∑ i : A.centers, restore (i : M) (A.outer i) (f i ∘ planeCoordinateIsometry) x) :=
    ContMDiff.sum (fun i _ => restore_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
      ((hf i).comp planeCoordinateIsometry.contDiff))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  simp only [vectorPlaneRestore, Finset.sum_apply]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_VectorReadBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed atlas bounds for the genuine smooth coordinate representatives.
The constants precede the map and scale, and no derivative order is lost. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma localize_outer_restore (i j : A.centers) (f : JetPolynomial.Base → V) :
    localize (i : M) (A.outer i) (restore (j : M) (A.outer j) f) =
      fun x => localize (i : M) (A.outer i) (A.outer j) x •
        f (transition (i : M) (j : M) x) := by
  funext x
  by_cases hi : x ∈ (chart (i : M)).target
  · by_cases hj : (chart (i : M)).symm x ∈ (chart (j : M)).source
    · simp only [localize,restore,indicator_of_mem hi,indicator_of_mem hj]
      rw [smul_smul]
      rfl
    · have hz : A.outer j ((chart (i : M)).symm x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hj (A.outer_support j h))
      simp only [localize,restore,indicator_of_mem hi,indicator_of_notMem hj,hz,smul_zero,zero_smul]
  · simp only [localize,indicator_of_notMem hi,zero_smul]

lemma localize_outer_restore_bound (i j : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : JetPolynomial.Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f →
      WeightedEstimates.WeightedBound univ s m C f →
      WeightedEstimates.WeightedBound univ s m (D*C)
        (localize (i : M) (A.outer i) (restore (j : M) (A.outer j) f)) := by
  let K := (chart (i : M)) '' (tsupport (A.outer i) ∩ tsupport (A.outer j))
  have hK : IsCompact K :=
    ((isClosed_tsupport _).inter (isClosed_tsupport _)).isCompact.image_of_continuousOn
      ((chart (i : M)).continuousOn.mono (fun _ h => A.outer_support i h.1))
  have hKO : K ⊆ (transition (i : M) (j : M)).source := by
    rintro x ⟨p,hp,rfl⟩
    refine ⟨(chart (i : M)).map_source (A.outer_support i hp.1),?_⟩
    change (chart (i : M)).symm (chart (i : M) p) ∈ (chart (j : M)).source
    rw [(chart (i : M)).left_inv (A.outer_support i hp.1)]
    exact A.outer_support j hp.2
  obtain ⟨D,hD,hd⟩ := compact_localized_composition_bound (V := V)
    (transition (i : M) (j : M)).open_source hK hKO
    (localize_smooth (i : M) (A.outer_smooth i) (A.outer_support i) (A.outer_smooth j))
    (localize_tsupport_inter (i : M) (A.outer_support i) (A.outer j))
    (transition_smooth (i : M) (j : M)) m
  refine ⟨D,hD,?_⟩
  intro f s C hs hs1 hC hf hb
  rw [A.localize_outer_restore]
  exact hd f s C hs hs1 hC hf hb

theorem vectorChartRead_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContMDiff planeModel 𝓘(ℝ,V) ∞ F →
      A.WeightedBound s m C F →
      WeightedEstimates.WeightedBound univ s m (D*C) (A.vectorChartRead i F) := by
  classical
  choose D hD hd using fun j : A.centers => A.localize_outer_restore_bound (V := V) i j m
  refine ⟨∑ j : A.centers, D j,Finset.sum_nonneg (fun j _ => hD j),?_⟩
  intro F s C hs hs1 hC hF hb
  have he : A.vectorChartRead i F = fun x => ∑ j : A.centers,
      localize (i : M) (A.outer i)
        (restore (j : M) (A.outer j) (localize (j : M) (A.weight j) F)) x := by
    unfold vectorChartRead
    conv_lhs => rw [← A.sum_restore_localize F]
    exact localize_sum Finset.univ _ _ _
  rw [he,Finset.sum_mul]
  apply WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ hs.le
  · intro j _
    exact (localize_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
      (restore_smooth (j : M) (A.outer_smooth j) (A.outer_support j)
        (localize_smooth (j : M) (A.weight_smooth j) (A.weight_support j) hF))).contDiffOn
  · intro j _
    exact hd j _ s C hs hs1 hC
      (localize_smooth (j : M) (A.weight_smooth j) (A.weight_support j) hF) (hb j)

theorem vectorPlaneRead_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContMDiff planeModel 𝓘(ℝ,V) ∞ F →
      A.WeightedBound s m C F →
      WeightedEstimates.WeightedBound univ s m (D*C) (A.vectorPlaneRead i F) := by
  obtain ⟨D,hD,hd⟩ := A.vectorChartRead_bound (V := V) i m
  refine ⟨D,hD,?_⟩
  intro F s C hs hs1 hC hF hb
  exact weightedBound_comp_isometry planeCoordinateIsometry.symm
    (A.vectorChartRead_smooth i hF) (hd F s C hs hs1 hC hF hb)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

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
lemma planeCoordinateIsometry_chart (p x : M) :
    planeCoordinateIsometry (chart p x) = planeCoordinates (chartAt Plane p x) := rfl

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_C1ImmersionJets
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted first jets detect immersion on the region where a partition
weight is nonzero. They depend continuously on the localized C1 data. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

omit [CompactSpace M] in
lemma fderiv_comp_chart_symm {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ,V) 1 f) (p : M) {x : Base}
    (hx : x ∈ (chart p).target) :
    fderiv ℝ (f ∘ (chart p).symm) x =
      (mfderiv planeModel 𝓘(ℝ,V) f ((chart p).symm x)).comp
        (mfderiv 𝓘(ℝ,Base) planeModel (chart p).symm x) := by
  rw [← mfderiv_eq_fderiv]
  exact mfderiv_comp x (hf.mdifferentiable one_ne_zero).mdifferentiableAt
    ((chart_mdifferentiable p).mdifferentiableAt_symm hx)

end ClosedSurfaceR4.FiniteOrderSmoothing

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityFrame
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
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

lemma normalize_unit {v : Vec} (hv : v ≠ 0) : normalize v ⬝ᵥ normalize v = 1 := by
  have hp := dot_self_pos hv
  have hs : Real.sqrt (v ⬝ᵥ v) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  simp only [normalize, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  have heq := Real.sq_sqrt hp.le
  field_simp
  nlinarith [heq]

lemma dot_normalize_zero {v w : Vec} (h : w ⬝ᵥ v = 0) : w ⬝ᵥ normalize v = 0 := by
  simp [normalize, dotProduct_smul, h]

lemma blend_nonzero {u v : Vec} (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1)
    (huv : -1 < u ⬝ᵥ v) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : blend u v t ≠ 0 := by
  by_cases ht0 : t = 0
  · intro hz
    have huz : u = 0 := by simpa [blend, ht0] using hz
    rw [huz] at hu
    norm_num at hu
  by_cases ht1 : t = 1
  · intro hz
    have hvz : v = 0 := by simpa [blend, ht1] using hz
    rw [hvz] at hv
    norm_num at hv
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
  have hs : blend u v t ⬝ᵥ blend u v t =
      (1 - 2 * t) ^ 2 + 2 * t * (1 - t) * (1 + u ⬝ᵥ v) := by
    simp only [blend, add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hu, hv, dotProduct_comm v u]
    ring
  have hp : 0 < (1 - 2 * t) ^ 2 + 2 * t * (1 - t) * (1 + u ⬝ᵥ v) :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos
      (mul_pos (mul_pos (by norm_num) htpos) (sub_pos.mpr htlt)) (by linarith))
  intro hz
  rw [hz] at hs
  simp only [dotProduct_zero] at hs
  linarith

lemma first_unit {u v : Vec} (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1)
    (huv : -1 < u ⬝ᵥ v) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    first u v t ⬝ᵥ first u v t = 1 := normalize_unit (blend_nonzero hu hv huv ht)

lemma first_perp {u v w : Vec} (hu : w ⬝ᵥ u = 0) (hv : w ⬝ᵥ v = 0) (t : ℝ) :
    w ⬝ᵥ first u v t = 0 := by
  apply dot_normalize_zero
  simp [blend, dotProduct_add, dotProduct_smul, hu, hv]

lemma normalize_of_unit {v : Vec} (hv : v ⬝ᵥ v = 1) : normalize v = v := by
  simp [normalize, hv]

lemma first_zero {u v : Vec} (hu : u ⬝ᵥ u = 1) : first u v 0 = u := by
  simpa [first, blend] using normalize_of_unit hu

lemma first_one {u v : Vec} (hv : v ⬝ᵥ v = 1) : first u v 1 = v := by
  simpa [first, blend] using normalize_of_unit hv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma normalize_smoothAt {v : E → Vec} {x : E} (hv : ContDiffAt ℝ ∞ v x) (hn : v x ≠ 0) :
    ContDiffAt ℝ ∞ (fun z => normalize (v z)) x := by
  have hd : ContDiffAt ℝ ∞ (fun z => v z ⬝ᵥ v z) x :=
    ContDiffAt.sum (fun i _ => (contDiffAt_pi.mp hv i).mul (contDiffAt_pi.mp hv i))
  have hp := dot_self_pos hn
  exact ((hd.sqrt hp.ne').inv (Real.sqrt_pos.mpr hp).ne').smul hv

lemma first_smoothAt {u v : E → Vec} {t : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ ∞ u x) (hv : ContDiffAt ℝ ∞ v x) (ht : ContDiffAt ℝ ∞ t x)
    (hu1 : u x ⬝ᵥ u x = 1) (hv1 : v x ⬝ᵥ v x = 1)
    (huv : -1 < u x ⬝ᵥ v x) (ht01 : t x ∈ Set.Icc (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (fun z => first (u z) (v z) (t z)) x :=
  normalize_smoothAt (((contDiffAt_const.sub ht).smul hu).add (ht.smul hv))
    (blend_nonzero hu1 hv1 huv ht01)

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasNormalProjection
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.OAI.ClosedSurfaceR4.VelocityFrame.planeLift_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Project a global ambient field to the normal bundle using the fixed
finite atlas. No orientation or global tangent frame is chosen. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes SmallModes NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma localizedNormalField_smooth (i : A.centers) {n : M → Space}
    (hn : ContMDiff planeModel spaceModel ∞ n) :
    ContDiff ℝ ∞ (A.localizedNormalField i n) :=
  spaceCoordinates.contDiff.comp
    ((localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hn).comp
      planeCoordinateIsometry.symm.contDiff)

omit [CompactSpace M] in
lemma localizedNormalField_support (i : A.centers) (n : M → Space) :
    tsupport (A.localizedNormalField i n) ⊆ tsupport (A.planeWeight i) := by
  apply closure_mono
  intro x hx
  contrapose! hx
  apply not_not.mpr
  have hw : A.planeWeight i x = 0 := by
    simpa only [Function.mem_support,not_not] using hx
  clear hx
  have hx := hw
  dsimp [localizedNormalField]
  by_cases hxt : planeCoordinateIsometry.symm x ∈ (chart (i : M)).target
  · simp only [planeWeight,chartWeight,Function.comp_apply,indicator_of_mem hxt] at hx
    simp [localize,hxt,hx]
  · simp [localize,hxt]

lemma localProjectedNormal_smooth (i : A.centers) {F n : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hn : ContMDiff planeModel spaceModel ∞ n)
    (hD : ∀ x ∈ tsupport (A.planeWeight i),
      gramDet (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
        (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ≠ 0) :
    ContDiff ℝ ∞ (A.localProjectedNormal i F n) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport (A.planeWeight i)
  · exact contDiffAt_realNormalPart
      (contDiff_real_coordDeriv (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)) dx).contDiffAt
      (contDiff_real_coordDeriv (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)) dy).contDiffAt
      (A.localizedNormalField_smooth i hn).contDiffAt (hD x hx)
  · have hz : A.localizedNormalField i n =ᶠ[𝓝 x] 0 :=
      notMem_tsupport_iff_eventuallyEq.mp (fun hs => hx (A.localizedNormalField_support i n hs))
    apply (contDiffAt_const (c := (0 : RVec 4))).congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    simp [localProjectedNormal,hy,realNormalPart]

lemma projectedNormalField_smooth {F n : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hn : ContMDiff planeModel spaceModel ∞ n)
    (hD : ∀ i x, x ∈ tsupport (A.planeWeight i) →
      gramDet (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
        (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ≠ 0) :
    ContMDiff planeModel spaceModel ∞ (A.projectedNormalField F n) :=
  A.vectorPlaneRestore_smooth _ (fun i => spaceCoordinates.symm.contDiff.comp
    (A.localProjectedNormal_smooth i hF hn (hD i)))

omit [CompactSpace M] in
lemma localProjectedNormal_zero (i : A.centers) (F n : M → Space) {x : SmallModes.Base}
    (hx : A.planeWeight i x = 0) : A.localProjectedNormal i F n x = 0 := by
  have hz : A.localizedNormalField i n x = 0 := by
    dsimp [localizedNormalField]
    by_cases hxt : planeCoordinateIsometry.symm x ∈ (chart (i : M)).target
    · simp only [planeWeight,chartWeight,Function.comp_apply,indicator_of_mem hxt] at hx
      simp [localize,hxt,hx]
    · simp [localize,hxt]
  simp [localProjectedNormal,hz,realNormalPart]

lemma vectorPlaneRead_fderiv_at_weight (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {p : M} (hp : p ∈ tsupport (A.weight i)) :
    fderiv ℝ (A.vectorPlaneRead i F) (planeCoordinateIsometry (chart (i : M) p)) =
      (mfderiv planeModel spaceModel F p).comp
        ((mfderiv 𝓘(ℝ,JetPolynomial.Base) planeModel (chart (i : M)).symm
          (chart (i : M) p)).comp planeCoordinateIsometry.symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
  have hs := A.weight_support i hp
  unfold vectorPlaneRead
  rw [fderiv_comp _ ((A.vectorChartRead_smooth i hF).differentiable (by simp) _)
    planeCoordinateIsometry.symm.differentiableAt]
  simp only [LinearIsometryEquiv.symm_apply_apply,planeCoordinateIsometry.symm.fderiv]
  rw [A.vectorChartRead_fderiv i hF ⟨p,hp,rfl⟩,
    fderiv_comp_chart_symm (hF.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (i : M) ((chart (i : M)).map_source hs),
    (chart (i : M)).left_inv hs]
  rfl

lemma vectorPlaneRead_normal (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (n : M → Space)
    (hn : ∀ p v, inner ℝ (show Space from mfderiv planeModel spaceModel F p v) (n p) = 0)
    {p : M} (hp : p ∈ tsupport (A.weight i)) (u : SmallModes.Base) :
    coordDeriv u (spaceCoordinates ∘ A.vectorPlaneRead i F)
      (planeCoordinateIsometry (chart (i : M) p)) ⬝ᵥ spaceCoordinates (n p) = 0 := by
  rw [coordDeriv,fderiv_comp _ spaceCoordinates.differentiableAt
    ((A.vectorPlaneRead_smooth i hF).differentiable (by simp) _),spaceCoordinates.fderiv,
    ContinuousLinearMap.comp_apply,A.vectorPlaneRead_fderiv_at_weight i hF hp]
  change spaceCoordinates (surfaceDifferential F p _) ⬝ᵥ spaceCoordinates (n p) = 0
  rw [spaceCoordinates_dot]
  exact hn p _

lemma localProjectedNormal_normal (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (n : M → Space)
    (p : M) (hp : p ∈ tsupport (A.weight i))
    (hD : gramDet
      (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p)))
      (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p))) ≠ 0)
    (v : TangentSpace planeModel p) :
    inner ℝ (show Space from mfderiv planeModel spaceModel F p v)
      (spaceCoordinates.symm (A.localProjectedNormal i F n
        (planeCoordinateIsometry (chart (i : M) p)))) = 0 := by
  let x := planeCoordinateIsometry (chart (i : M) p)
  let u := planeCoordinateIsometry (surfaceDifferential (chart (i : M)) p v)
  have hd := congrArg (fun L : TangentSpace planeModel p →L[ℝ] Space => L v)
    (A.vectorPlaneRead_differential i hF hp)
  simp only [ContinuousLinearMap.comp_apply] at hd
  have hc := fderiv_comp x spaceCoordinates.differentiableAt
    ((A.vectorPlaneRead_smooth i hF).differentiable (by simp) x)
  have hpj := realNormalPart_perp
    (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
    (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
    (A.localizedNormalField i n x) hD
  rw [← spaceCoordinates_dot,ContinuousLinearEquiv.apply_symm_apply]
  change spaceCoordinates (surfaceDifferential F p v) ⬝ᵥ _ = 0
  rw [hd]
  change spaceCoordinates (fderiv ℝ (A.vectorPlaneRead i F) x u) ⬝ᵥ
    A.localProjectedNormal i F n x = 0
  have heval : coordDeriv u (spaceCoordinates ∘ A.vectorPlaneRead i F) x =
      spaceCoordinates (fderiv ℝ (A.vectorPlaneRead i F) x u) := by
    rw [coordDeriv,hc,spaceCoordinates.fderiv]
    rfl
  rw [← heval,coordDeriv_eq_basis]
  simp only [add_dotProduct,smul_dotProduct,localProjectedNormal,hpj.1,hpj.2,
    smul_eq_mul,mul_zero,add_zero]

lemma projectedNormalField_normal {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (n : M → Space)
    (hD : ∀ i x, x ∈ tsupport (A.planeWeight i) →
      gramDet (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
        (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ≠ 0)
    (p : M) (v : TangentSpace planeModel p) :
    inner ℝ (show Space from mfderiv planeModel spaceModel F p v) (A.projectedNormalField F n p) = 0 := by
  classical
  change inner ℝ (surfaceDifferential F p v) (A.projectedNormalField F n p) = 0
  unfold projectedNormalField vectorPlaneRestore
  rw [Finset.sum_apply,inner_sum]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hz : A.weight i p = 0
  · by_cases hs : p ∈ (chart (i : M)).source
    · have hx : A.planeWeight i (planeCoordinateIsometry (chart (i : M) p)) = 0 := by
        simp [planeWeight,chartWeight,(chart (i : M)).map_source hs,
          (chart (i : M)).left_inv hs,hz]
      simp [restore,hs,A.localProjectedNormal_zero i F n hx]
    · simp [restore,hs]
  · have hp := subset_tsupport (A.weight i) hz
    have hs := A.weight_support i hp
    have hx : planeCoordinateIsometry (chart (i : M) p) ∈ tsupport (A.planeWeight i) := by
      apply subset_tsupport
      simpa [planeWeight,chartWeight,(chart (i : M)).map_source hs,
        (chart (i : M)).left_inv hs] using hz
    simp only [restore,indicator_of_mem hs,Function.comp_apply,real_inner_smul_right]
    have hn := A.localProjectedNormal_normal i hF n p hp (hD i _ hx) v
    change inner ℝ (surfaceDifferential F p v)
      (spaceCoordinates.symm (A.localProjectedNormal i F n
        (planeCoordinateIsometry (chart (i : M) p)))) = 0 at hn
    rw [hn,mul_zero]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_BoundaryProfileGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal frames and scaled second-form coefficients are smooth functions of
exactly the five derivative components retained by the primitive construction. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame RealModes VelocityFrame

lemma contDiffAt_profileNormalPart {J : BoundaryProfile}
    (hJ : gramDet (J 0) (J 1) ≠ 0) : ContDiffAt ℝ ∞ profileNormalPart J := by
  exact contDiffAt_realNormalPart
    (ContinuousLinearMap.proj 0 : BoundaryProfile →L[ℝ] Vec).contDiff.contDiffAt
    (ContinuousLinearMap.proj 1 : BoundaryProfile →L[ℝ] Vec).contDiff.contDiffAt
    (ContinuousLinearMap.proj 2 : BoundaryProfile →L[ℝ] Vec).contDiff.contDiffAt hJ

lemma isOpen_regularBoundaryProfiles : IsOpen regularBoundaryProfiles := by
  apply isOpen_iff_mem_nhds.mpr
  intro J hJ
  have hd : Continuous (fun K : BoundaryProfile => gramDet (K 0) (K 1)) := by
    unfold gramDet dotProduct
    fun_prop
  exact (hd.continuousAt.eventually_ne hJ.1).and
    ((contDiffAt_profileNormalPart hJ.1).continuousAt.eventually_ne hJ.2)

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasNormalProjectionBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The atlas projection is a convex sum of the actual pointwise normal
projections. Local exterior estimates therefore pass to the global field. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes SmallModes NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma localizedNormalField_at_source (i : A.centers) (n : M → Space) {p : M}
    (hp : p ∈ (chart (i : M)).source) :
    A.localizedNormalField i n (planeCoordinateIsometry (chart (i : M) p)) =
      (A.weight i p)^2 • spaceCoordinates (n p) := by
  simp [localizedNormalField,localize,(chart (i : M)).map_source hp,
    (chart (i : M)).left_inv hp]

lemma restored_localProjectedNormal (i : A.centers) (F n : M → Space) (p : M) :
    restore (i : M) (A.outer i)
      ((spaceCoordinates.symm ∘ A.localProjectedNormal i F n) ∘ planeCoordinateIsometry) p =
        (A.weight i p)^2 • A.chartProjectedNormal i F n p := by
  by_cases hs : p ∈ (chart (i : M)).source
  · simp only [restore,indicator_of_mem hs,Function.comp_apply]
    by_cases hz : A.weight i p = 0
    · have hx : A.planeWeight i (planeCoordinateIsometry (chart (i : M) p)) = 0 := by
        simp [planeWeight,chartWeight,(chart (i : M)).map_source hs,
          (chart (i : M)).left_inv hs,hz]
      simp [A.localProjectedNormal_zero i F n hx,hz]
    · have hp := subset_tsupport (A.weight i) hz
      rw [A.outer_one i p hp,one_smul,localProjectedNormal,
        A.localizedNormalField_at_source i n hs,(realNormalPart_linear _ _).map_smul,
        map_smul]
      rfl
  · have hz : A.weight i p = 0 := image_eq_zero_of_notMem_tsupport
      (fun hp => hs (A.weight_support i hp))
    simp [restore,hs,hz]

lemma projectedNormalField_eq_sum (F n : M → Space) (p : M) :
    A.projectedNormalField F n p =
      ∑ i : A.centers, (A.weight i p)^2 • A.chartProjectedNormal i F n p := by
  unfold projectedNormalField vectorPlaneRestore
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact A.restored_localProjectedNormal i F n p

lemma projectedNormalField_sub_eq (F n : M → Space) (p : M) :
    A.projectedNormalField F n p - n p =
      ∑ i : A.centers, (A.weight i p)^2 • (A.chartProjectedNormal i F n p - n p) := by
  rw [A.projectedNormalField_eq_sum]
  simp only [smul_sub,Finset.sum_sub_distrib,← Finset.sum_smul,A.partition,one_smul]

/-- A local exterior error is not multiplied by the number of atlas
patches: the squared weights add to one. -/
theorem projectedNormalField_sub_bound (F n : M → Space) (p : M) {ε : ℝ}
    (hlocal : ∀ i : A.centers, A.weight i p ≠ 0 →
      ‖A.chartProjectedNormal i F n p - n p‖ ≤ ε) :
    ‖A.projectedNormalField F n p - n p‖ ≤ ε := by
  rw [A.projectedNormalField_sub_eq]
  calc
    _ ≤ ∑ i : A.centers, ‖(A.weight i p)^2 • (A.chartProjectedNormal i F n p - n p)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : A.centers, (A.weight i p)^2 * ε := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hz : A.weight i p = 0
      · simp [hz]
      · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        exact mul_le_mul_of_nonneg_left (hlocal i hz) (sq_nonneg _)
    _ = ε := by rw [← Finset.sum_mul,A.partition,one_mul]

lemma projectedNormalField_ne_zero (F n : M → Space) (p : M)
    (hn : ‖n p‖ = 1) (hclose : ‖A.projectedNormalField F n p - n p‖ < 1) :
    A.projectedNormalField F n p ≠ 0 := by
  intro hz
  simp [hz,hn] at hclose

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

namespace ClosedSurfaceR4.GeometryPreservation
open RealModes NormalFrame VelocityFrame

/-- Uniform stability of the unnormalized projection on a compact family
of old tangent frames. This is the estimate used before normalizing the
finite-atlas sum. -/
theorem compact_raw_normal_projection {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {A B n : X → Vec} (hA : Continuous A) (hB : Continuous B) (hn : Continuous n)
    (hD : ∀ x, gramDet (A x) (B x) ≠ 0)
    (hunit : ∀ x, n x ⬝ᵥ n x = 1)
    (hAn : ∀ x, A x ⬝ᵥ n x = 0) (hBn : ∀ x, B x ⬝ᵥ n x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, ∀ A' B' : Vec,
      ‖A'-A x‖ < δ → ‖B'-B x‖ < δ →
      gramDet A' B' ≠ 0 ∧ ‖realNormalPart A' B' (n x)-n x‖ < ε := by
  let J : X → BoundaryProfile := fun x => ![A x,B x,n x,0,0]
  have hJ : Continuous J := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact hA
    · exact hB
    · exact hn
    · exact continuous_const
    · exact continuous_const
  have he (x : X) : profileNormalPart (J x) = n x :=
    realNormalPart_of_perp _ _ _ (hAn x) (hBn x)
  have hreg : Set.range J ⊆ regularBoundaryProfiles := by
    rintro _ ⟨x,rfl⟩
    refine ⟨hD x,?_⟩
    rw [he]
    intro hz
    have hh := hunit x
    norm_num [hz] at hh
  have hK := isCompact_range hJ
  obtain ⟨r,hr,hsub⟩ := hK.exists_cthickening_subset_open isOpen_regularBoundaryProfiles hreg
  have hc : ContinuousOn profileNormalPart (Metric.cthickening r (Set.range J)) :=
    fun H hH => (contDiffAt_profileNormalPart (hsub hH).1).continuousAt.continuousWithinAt
  obtain ⟨d,hd,hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.cthickening.uniformContinuousOn_of_continuous hc) ε hε
  refine ⟨min r d,lt_min hr hd,?_⟩
  intro x A' B' hA' hB'
  let H : BoundaryProfile := ![A',B',n x,0,0]
  have herr : ‖H-J x‖ < min r d := by
    have hbnd : ‖H-J x‖ ≤ max ‖A'-A x‖ ‖B'-B x‖ := by
      apply (pi_norm_le_iff_of_nonneg (le_trans (norm_nonneg _) (le_max_left _ _))).mpr
      intro i
      fin_cases i
      · exact le_max_left _ _
      · exact le_max_right _ _
      · simp [H,J]
      · simp [H,J]
      · simp [H,J]
    exact hbnd.trans_lt (max_lt hA' hB')
  have hH : H ∈ Metric.cthickening r (Set.range J) :=
    Metric.thickening_subset_cthickening r (Set.range J)
      (Metric.mem_thickening_iff.mpr ⟨J x,mem_range_self x,by
        simpa only [dist_eq_norm] using herr.trans_le (min_le_left r d)⟩)
  have hJ' : J x ∈ Metric.cthickening r (Set.range J) :=
    Metric.self_subset_cthickening (Set.range J) (mem_range_self x)
  have hh := hclose H hH (J x) hJ' (by
    simpa only [dist_eq_norm] using herr.trans_le (min_le_right r d))
  refine ⟨(hsub hH).1,?_⟩
  change ‖profileNormalPart H-n x‖ < ε
  simpa only [dist_eq_norm,he] using hh

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasPhaseStability
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed local good-phase charts persist under a global C2 perturbation. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial PhaseGeometry WeightedEstimates RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma vectorPlaneRead_sub {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : A.centers) (F G : M → V) :
    A.vectorPlaneRead i (F-G) = A.vectorPlaneRead i F - A.vectorPlaneRead i G := by
  funext x
  by_cases hx : planeCoordinateIsometry.symm x ∈ (chart (i : M)).target <;>
    simp [vectorPlaneRead,vectorChartRead,localize,hx,smul_sub]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_NormalizedJetCorrection
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Second jets of radial normalization, for the finite-point flattening
of the starting spherical immersion. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.SphericalJets

lemma radialNormalize_smoothAt {x : Space} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ radialNormalize x :=
  ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id

end ClosedSurfaceR4.SphericalJets

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ProjectedNormalLocal
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative normalization of the atlas projection on an exterior open set. -/
noncomputable section
open Set Manifold
open scoped ContDiff
namespace ClosedSurfaceR4.SphericalJets

lemma radialNormalize_unit {u : Space} (hu : u ≠ 0) : ‖radialNormalize u‖ = 1 := by
  rw [radialNormalize,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)]

lemma radialNormalize_sub_unit_bound {u v : Space} (hu : u ≠ 0) (hv : ‖v‖ = 1) :
    ‖radialNormalize u-v‖ ≤ 2*‖u-v‖ := by
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have he : ‖radialNormalize u-u‖ = |1-‖u‖| := by
    have he : ‖u‖⁻¹ • u-u = (‖u‖⁻¹-1) • u := by rw [sub_smul,one_smul]
    rw [radialNormalize,he,norm_smul,Real.norm_eq_abs]
    calc
      |‖u‖⁻¹-1| *‖u‖ = |(‖u‖⁻¹-1)*‖u‖| := by rw [abs_mul,abs_of_nonneg hn.le]
      _ = |1-‖u‖| := by congr 1; field_simp
  have habs : |1-‖u‖| ≤ ‖u-v‖ := by
    rw [abs_sub_comm,← hv]
    exact abs_norm_sub_norm_le u v
  calc
    ‖radialNormalize u-v‖ ≤ ‖radialNormalize u-u‖+‖u-v‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2*‖u-v‖ := by rw [he]; linarith

end ClosedSurfaceR4.SphericalJets
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes SmallModes NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem unitProjectedNormalField_properties {F n : M → Space} {U : Set M}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hn : ContMDiff planeModel spaceModel ∞ n)
    (hD : ∀ i x, x ∈ tsupport (A.planeWeight i) →
      gramDet (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
        (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ≠ 0)
    (hne : ∀ p ∈ U, A.projectedNormalField F n p ≠ 0) :
    ContMDiffOn planeModel spaceModel ∞ (A.unitProjectedNormalField F n) U ∧
      (∀ p ∈ U, ‖A.unitProjectedNormalField F n p‖ = 1) ∧
      (∀ p ∈ U, ∀ v : TangentSpace planeModel p,
        inner ℝ (surfaceDifferential F p v) (A.unitProjectedNormalField F n p) = 0) := by
  have hP := A.projectedNormalField_smooth hF hn hD
  refine ⟨?_,?_,?_⟩
  · intro p hp
    exact ((SphericalJets.radialNormalize_smoothAt (hne p hp)).contMDiffAt.comp p (hP p)).contMDiffWithinAt
  · intro p hp
    exact SphericalJets.radialNormalize_unit (hne p hp)
  · intro p hp v
    change inner ℝ (surfaceDifferential F p v)
      (‖A.projectedNormalField F n p‖⁻¹ • A.projectedNormalField F n p) = 0
    have hh := A.projectedNormalField_normal hF n hD p v
    change inner ℝ (surfaceDifferential F p v) (A.projectedNormalField F n p) = 0 at hh
    rw [real_inner_smul_right,hh,mul_zero]

omit [CompactSpace M] in
theorem unitProjectedNormalField_sub_bound {F n : M → Space} {p : M} {δ : ℝ}
    (hn : ‖n p‖ = 1) (hδ : δ < 1)
    (hlocal : ∀ i : A.centers, A.weight i p ≠ 0 →
      ‖A.chartProjectedNormal i F n p - n p‖ ≤ δ) :
    A.projectedNormalField F n p ≠ 0 ∧
      ‖A.unitProjectedNormalField F n p-n p‖ ≤ 2*δ := by
  have hb := A.projectedNormalField_sub_bound F n p hlocal
  have hne := A.projectedNormalField_ne_zero F n p hn (hb.trans_lt hδ)
  exact ⟨hne,(SphericalJets.radialNormalize_sub_unit_bound hne hn).trans
    (mul_le_mul_of_nonneg_left hb (by norm_num))⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasProjectionStability
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One tolerance controls normal projection through every chart of the finite atlas. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes SmallModes NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma compact_chart_projection_stability (i : A.centers) {F n : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hn : ContMDiff planeModel spaceModel ∞ n)
    (hunit : ∀ p, ‖n p‖ = 1)
    (hN : ∀ p v, inner ℝ (surfaceDifferential F p v) (n p) = 0)
    (hD : ∀ p ∈ tsupport (A.weight i),
      gramDet (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p)))
      (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p))) ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ G : M → Space, ∀ p ∈ tsupport (A.weight i),
      ‖coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i G)
        (planeCoordinateIsometry (chart (i : M) p))-
        coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p))‖ < δ →
      ‖coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i G)
        (planeCoordinateIsometry (chart (i : M) p))-
        coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p))‖ < δ →
      ‖A.chartProjectedNormal i G n p-n p‖ < ε := by
  let S := {p : M // p ∈ tsupport (A.weight i)}
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isClosed_tsupport (A.weight i)).isCompact
  let c : S → SmallModes.Base := fun p => planeCoordinateIsometry (chart (i : M) p.1)
  have hc : Continuous c := planeCoordinateIsometry.continuous.comp
    (((chart (i : M)).continuousOn.mono (A.weight_support i)).domRestrict)
  have hread := spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)
  have hX := (contDiff_real_coordDeriv hread dx).continuous.comp hc
  have hY := (contDiff_real_coordDeriv hread dy).continuous.comp hc
  have hnn : Continuous (fun p : S => spaceCoordinates (n p.1)) :=
    spaceCoordinates.continuous.comp (hn.continuous.comp continuous_subtype_val)
  let L := ‖spaceCoordinates.symm.toContinuousLinearMap‖
  have hL : 0 ≤ L := norm_nonneg _
  obtain ⟨δ,hδ,hnear⟩ := GeometryPreservation.compact_raw_normal_projection hX hY hnn
    (fun p => hD p.1 p.2) (fun p => by
      rw [spaceCoordinates_dot,real_inner_self_eq_norm_sq,hunit]; norm_num)
    (fun p => A.vectorPlaneRead_normal i hF n hN p.2 dx)
    (fun p => A.vectorPlaneRead_normal i hF n hN p.2 dy) (div_pos hε (by positivity : 0 < L+1))
  refine ⟨δ,hδ,?_⟩
  intro G p hp hx hy
  have hh := (hnear ⟨p,hp⟩ _ _ hx hy).2
  let r := realNormalPart
    (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i G) (c ⟨p,hp⟩))
    (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i G) (c ⟨p,hp⟩))
    (spaceCoordinates (n p))-spaceCoordinates (n p)
  change ‖r‖ < ε/(L+1) at hh
  have he : A.chartProjectedNormal i G n p-n p = spaceCoordinates.symm r := by
    simp only [r,chartProjectedNormal,map_sub,ContinuousLinearEquiv.symm_apply_apply,c]
  rw [he]
  calc
    ‖spaceCoordinates.symm r‖ ≤ L*‖r‖ := spaceCoordinates.symm.toContinuousLinearMap.le_opNorm r
    _ ≤ (L+1)*‖r‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (L+1)*(ε/(L+1)) := mul_lt_mul_of_pos_left hh (by positivity)
    _ = ε := mul_div_cancel₀ _ (by positivity)

theorem compact_atlas_projection_stability {F n : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hn : ContMDiff planeModel spaceModel ∞ n)
    (hunit : ∀ p, ‖n p‖ = 1)
    (hN : ∀ p v, inner ℝ (surfaceDifferential F p v) (n p) = 0)
    (hD : ∀ i p, p ∈ tsupport (A.weight i) →
      gramDet (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p)))
      (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p))) ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ G : M → Space, ∀ p : M,
      (∀ i : A.centers, A.weight i p ≠ 0 → ∀ v ∈ ({dx,dy} : Set SmallModes.Base),
        ‖coordDeriv v (spaceCoordinates ∘ A.vectorPlaneRead i G)
          (planeCoordinateIsometry (chart (i : M) p))-
          coordDeriv v (spaceCoordinates ∘ A.vectorPlaneRead i F)
          (planeCoordinateIsometry (chart (i : M) p))‖ < δ) →
      A.projectedNormalField G n p ≠ 0 ∧
        ‖A.unitProjectedNormalField G n p-n p‖ < ε := by
  classical
  let η := min (1/2 : ℝ) (ε/3)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hi := fun i => A.compact_chart_projection_stability i hF hn hunit hN (hD i) hη
  choose d hd hnear using hi
  obtain ⟨δ,hδ,_,hle⟩ := finite_positive_threshold d hd
  refine ⟨δ,hδ,?_⟩
  intro G p hp
  have hh := A.unitProjectedNormalField_sub_bound (F := G) (p := p) (hunit p)
    (lt_of_le_of_lt (min_le_left _ _) (by norm_num : (1/2:ℝ)<1)) (fun i hz =>
      (hnear i G p (subset_tsupport _ hz)
        ((hp i hz dx (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).trans_le (hle i))
        ((hp i hz dy (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).trans_le (hle i))).le)
  exact ⟨hh.1,hh.2.trans_lt (by have := min_le_right (1/2:ℝ) (ε/3); dsimp [η] at * <;> linarith)⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ImmersedAtlasNormal
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Discharge the projection's Gram hypotheses from the actual immersion. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes SmallModes NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma planeRead_gram_of_immersion {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hI : ∀ p, Function.Injective (surfaceDifferential F p))
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (i : A.centers) {p : M} (hp : p ∈ tsupport (A.weight i)) :
    gramDet (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F)
      (planeCoordinateIsometry (chart (i : M) p)))
    (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F)
      (planeCoordinateIsometry (chart (i : M) p))) ≠ 0 := by
  have he := A.vectorPlaneRead_eventually_coordinateMap F i (houter i) hp
  change gramDet (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) _ dx)
    (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) _ dy) ≠ 0
  rw [he.fderiv_eq]
  apply gramDet_ne_zero_of_injective
  apply coordinateMap_injective_of_immersion hF hI (i : M)
  change planeCoordinateIsometry (chart (i : M) p) ∈ (coordinateChart (i : M)).target
  rw [planeCoordinateIsometry_chart]
  exact (coordinateChart (i : M)).map_source (A.weight_support i hp)

lemma planeWeight_gram_of_immersion {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hI : ∀ p, Function.Injective (surfaceDifferential F p))
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (i : A.centers) {x : SmallModes.Base} (hx : x ∈ tsupport (A.planeWeight i)) :
    gramDet (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
      (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ≠ 0 := by
  have hh := (A.supportedPlaneWeight i).tsupport_subset hx
  rcases hh with ⟨q,hq,rfl⟩
  rcases hq with ⟨p,hp,rfl⟩
  exact A.planeRead_gram_of_immersion hF hI houter i hp

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_OuterChartDifferential
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recover the actual differential wherever the outer chart cutoff equals
one on a neighborhood, including a collar beyond the primitive support. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma vectorChartRead_comp_chart_of_outer (i : A.centers) (F : M → Space)
    {p : M} (hp : p ∈ (chart (i : M)).source)
    (houter : A.outer i =ᶠ[𝓝 p] fun _ => (1 : ℝ)) :
    F =ᶠ[𝓝 p] A.vectorChartRead i F ∘ chart (i : M) := by
  filter_upwards [(chart (i : M)).open_source.mem_nhds hp,houter] with q hq hone
  simp only [Function.comp_apply,vectorChartRead,localize,
    indicator_of_mem ((chart (i : M)).map_source hq),
    (chart (i : M)).left_inv hq,hone,one_pow,one_smul]

lemma vectorChartRead_differential_of_outer (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    {p : M} (hp : p ∈ (chart (i : M)).source)
    (houter : A.outer i =ᶠ[𝓝 p] fun _ => (1 : ℝ)) :
    surfaceDifferential F p = (fderiv ℝ (A.vectorChartRead i F) (chart (i : M) p)).comp
      (surfaceDifferential (chart (i : M)) p) := by
  have hc := ((chart_smooth (i : M)) p hp).contMDiffAt
    ((chart (i : M)).open_source.mem_nhds hp)
  have he := A.vectorChartRead_comp_chart_of_outer i F hp houter
  unfold surfaceDifferential
  rw [he.mfderiv_eq,mfderiv_comp p
    ((A.vectorChartRead_smooth i hF).differentiable (by simp) _).mdifferentiableAt
    (hc.mdifferentiableAt (by simp)),mfderiv_eq_fderiv]
  rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_NormalInterpolation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convex interpolation of unit normals on the exterior collar retains
normality and every strictly positive pairing along the later curves. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

lemma dot_gt_neg_one_of_ne_antipode {u v : Vec}
    (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) (hne : u ≠ -v) : -1 < u ⬝ᵥ v := by
  have hsum : u+v ≠ 0 := by
    intro hz
    exact hne (eq_neg_of_add_eq_zero_left hz)
  have hp := dot_self_pos hsum
  simp only [add_dotProduct,dotProduct_add,hu,hv,dotProduct_comm v u] at hp
  linarith

lemma first_pairing_pos {u v w : Vec} {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hu : 0 < w ⬝ᵥ u) (hv : 0 < w ⬝ᵥ v) :
    0 < w ⬝ᵥ first u v t := by
  have hp : 0 < w ⬝ᵥ blend u v t := by
    simp only [blend,dotProduct_add,dotProduct_smul,smul_eq_mul]
    by_cases ht0 : t = 0
    · simpa only [ht0,sub_zero,one_mul,zero_mul,add_zero] using hu
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr ht.2) hu.le) (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) hv)
  have hn : blend u v t ≠ 0 := by
    intro hz
    rw [hz,dotProduct_zero] at hp
    exact lt_irrefl 0 hp
  change 0 < w ⬝ᵥ normalize (blend u v t)
  rw [normalize,dotProduct_smul]
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr (dot_self_pos hn))) hp

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_NormalCollarGluing
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Glue the local adjusted normal to the exterior projected normal.
The cutoff support conditions remove every use of an unavailable chart. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma first_contMDiffAt {a b : M → Vec} {t : M → ℝ} {p : M}
    (ha : ContMDiffAt planeModel 𝓘(ℝ,Vec) ∞ a p)
    (hb : ContMDiffAt planeModel 𝓘(ℝ,Vec) ∞ b p)
    (ht : ContMDiffAt planeModel 𝓘(ℝ) ∞ t p)
    (ha1 : a p ⬝ᵥ a p = 1) (hb1 : b p ⬝ᵥ b p = 1)
    (hne : a p ≠ -b p) (htr : t p ∈ Icc (0 : ℝ) 1) :
    ContMDiffAt planeModel 𝓘(ℝ,Vec) ∞ (fun x => first (a x) (b x) (t x)) p := by
  let H : Vec × (Vec × ℝ) → Vec := fun x => first x.1 x.2.1 x.2.2
  have hH : ContDiffAt ℝ ∞ H (a p,b p,t p) :=
    first_smoothAt contDiffAt_fst (contDiffAt_snd.fst) (contDiffAt_snd.snd)
      ha1 hb1 (dot_gt_neg_one_of_ne_antipode ha1 hb1 hne) htr
  have hm : ContMDiffAt 𝓘(ℝ,Vec × (Vec × ℝ)) 𝓘(ℝ,Vec) ∞ H (a p,b p,t p) :=
    hH.contMDiffAt
  have hout := hm.comp (g := H) p (ha.prodMk_space (hb.prodMk_space ht))
  exact hout

theorem normal_collar_gluing {U V : Set M} (hU : IsOpen U) (hV : IsOpen V)
    {a b : M → Vec} {chi : M → ℝ}
    (ha : ContMDiffOn planeModel 𝓘(ℝ,Vec) ∞ a U)
    (hb : ContMDiffOn planeModel 𝓘(ℝ,Vec) ∞ b V)
    (hchi : ContMDiff planeModel 𝓘(ℝ) ∞ chi)
    (hchiu : tsupport chi ⊆ U) (hchiv : tsupport (fun x => 1-chi x) ⊆ V)
    (hchi01 : ∀ x, chi x ∈ Icc (0 : ℝ) 1)
    (ha1 : ∀ x ∈ U, a x ⬝ᵥ a x = 1) (hb1 : ∀ x ∈ V, b x ⬝ᵥ b x = 1)
    (hne : ∀ x ∈ U ∩ V, b x ≠ -a x) :
    let g := fun x => first (b x) (a x) (chi x)
    ContMDiff planeModel 𝓘(ℝ,Vec) ∞ g ∧ (∀ x, g x ⬝ᵥ g x = 1) ∧
      (∀ x, chi x = 1 → g x = a x) ∧ (∀ x, chi x = 0 → g x = b x) ∧
      (∀ x (w : Vec), (x ∈ U → w ⬝ᵥ a x = 0) →
        (x ∈ V → w ⬝ᵥ b x = 0) → w ⬝ᵥ g x = 0) ∧
      (∀ x (w : Vec), (x ∈ U → 0 < w ⬝ᵥ a x) →
        (x ∈ V → 0 < w ⬝ᵥ b x) → 0 < w ⬝ᵥ g x) := by
  dsimp only
  have ha_mem (x : M) (hx : chi x ≠ 0) : x ∈ U :=
    hchiu (subset_tsupport chi hx)
  have hb_mem (x : M) (hx : chi x ≠ 1) : x ∈ V := by
    apply hchiv
    apply subset_tsupport
    change 1-chi x ≠ 0
    exact sub_ne_zero.mpr (Ne.symm hx)
  have ha_eq (x : M) (hx : chi x = 1) : first (b x) (a x) (chi x) = a x := by
    rw [hx,first_one (ha1 x (ha_mem x (by simpa only [hx] using one_ne_zero)))]
  have hb_eq (x : M) (hx : chi x = 0) : first (b x) (a x) (chi x) = b x := by
    rw [hx,first_zero (hb1 x (hb_mem x (by simpa only [hx] using zero_ne_one)))]
  refine ⟨?_,?_,ha_eq,hb_eq,?_,?_⟩
  · intro x
    by_cases hxU : x ∈ U
    · by_cases hxV : x ∈ V
      · exact first_contMDiffAt (hb.contMDiffAt (hV.mem_nhds hxV))
          (ha.contMDiffAt (hU.mem_nhds hxU)) (hchi x) (hb1 x hxV) (ha1 x hxU)
          (hne x ⟨hxU,hxV⟩) (hchi01 x)
      · have hz : (fun y => 1-chi y) =ᶠ[𝓝 x] 0 :=
          notMem_tsupport_iff_eventuallyEq.mp (fun hs => hxV (hchiv hs))
        apply (ha.contMDiffAt (hU.mem_nhds hxU)).congr_of_eventuallyEq
        filter_upwards [hz] with y hy
        exact ha_eq y (sub_eq_zero.mp hy).symm
    · have hz : chi =ᶠ[𝓝 x] 0 :=
        notMem_tsupport_iff_eventuallyEq.mp (fun hs => hxU (hchiu hs))
      have hxV : x ∈ V := hb_mem x (by rw [hz.eq_of_nhds]; exact zero_ne_one)
      apply (hb.contMDiffAt (hV.mem_nhds hxV)).congr_of_eventuallyEq
      filter_upwards [hz] with y hy
      exact hb_eq y hy
  · intro x
    by_cases h0 : chi x = 0
    · rw [hb_eq x h0]; exact hb1 x (hb_mem x (by rw [h0]; exact zero_ne_one))
    by_cases h1 : chi x = 1
    · rw [ha_eq x h1]; exact ha1 x (ha_mem x h0)
    exact first_unit (hb1 x (hb_mem x h1)) (ha1 x (ha_mem x h0))
      (dot_gt_neg_one_of_ne_antipode (hb1 x (hb_mem x h1)) (ha1 x (ha_mem x h0))
        (hne x ⟨ha_mem x h0,hb_mem x h1⟩)) (hchi01 x)
  · intro x w hwa hwb
    by_cases h0 : chi x = 0
    · rw [hb_eq x h0]; exact hwb (hb_mem x (by rw [h0]; exact zero_ne_one))
    by_cases h1 : chi x = 1
    · rw [ha_eq x h1]; exact hwa (ha_mem x h0)
    exact first_perp (hwb (hb_mem x h1)) (hwa (ha_mem x h0)) _
  · intro x w hwa hwb
    by_cases h0 : chi x = 0
    · rw [hb_eq x h0]; exact hwb (hb_mem x (by rw [h0]; exact zero_ne_one))
    by_cases h1 : chi x = 1
    · rw [ha_eq x h1]; exact hwa (ha_mem x h0)
    exact first_pairing_pos (hchi01 x) (hwb (hb_mem x h1)) (hwa (ha_mem x h0))

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PreferredNormalGluing
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The collar construction produces the actual global preferred normal
carried by the finite primitive induction. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4
open RealModes VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma coordinate_dot_self_of_unit {v : Space} (hv : ‖v‖ = 1) :
    spaceCoordinates v ⬝ᵥ spaceCoordinates v = 1 := by
  rw [spaceCoordinates_dot,real_inner_self_eq_norm_sq,hv]
  norm_num

lemma norm_coordinate_inverse_of_dot_self {v : NormalFrame.Vec} (hv : v ⬝ᵥ v = 1) :
    ‖spaceCoordinates.symm v‖ = 1 := by
  have he : ‖spaceCoordinates.symm v‖^2 = (1 : ℝ)^2 := by
    rw [← real_inner_self_eq_norm_sq,← spaceCoordinates_dot,
      ContinuousLinearEquiv.apply_symm_apply,hv,one_pow]
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp he

/-- Glue an interior normal to an exterior normal, retaining all positive
pairings needed on the later primitive boundaries. -/
theorem preferredNormal_collar {F a b : M → Space} {U V : Set M}
    (hU : IsOpen U) (hV : IsOpen V)
    (ha : ContMDiffOn planeModel spaceModel ∞ a U)
    (hb : ContMDiffOn planeModel spaceModel ∞ b V)
    (ha1 : ∀ p ∈ U, ‖a p‖ = 1) (hb1 : ∀ p ∈ V, ‖b p‖ = 1)
    (haN : ∀ p ∈ U, ∀ v : TangentSpace planeModel p,
      inner ℝ (surfaceDifferential F p v) (a p) = 0)
    (hbN : ∀ p ∈ V, ∀ v : TangentSpace planeModel p,
      inner ℝ (surfaceDifferential F p v) (b p) = 0)
    (hne : ∀ p ∈ U ∩ V, b p ≠ -a p)
    {chi : M → ℝ} (hchi : ContMDiff planeModel 𝓘(ℝ) ∞ chi)
    (hchiu : tsupport chi ⊆ U) (hchiv : tsupport (fun p => 1-chi p) ⊆ V)
    (hchi01 : ∀ p, chi p ∈ Icc (0 : ℝ) 1) :
    ∃ N : PreferredNormal F,
      (∀ p, chi p = 1 → N.vector p = a p) ∧
      (∀ p, chi p = 0 → N.vector p = b p) ∧
      (∀ p (w : Space), (p ∈ U → 0 < inner ℝ w (a p)) →
        (p ∈ V → 0 < inner ℝ w (b p)) → 0 < inner ℝ w (N.vector p)) := by
  let ac := spaceCoordinates ∘ a
  let bc := spaceCoordinates ∘ b
  have hac : ContMDiffOn planeModel 𝓘(ℝ,NormalFrame.Vec) ∞ ac U :=
    spaceCoordinates.contDiff.contMDiff.comp_contMDiffOn ha
  have hbc : ContMDiffOn planeModel 𝓘(ℝ,NormalFrame.Vec) ∞ bc V :=
    spaceCoordinates.contDiff.contMDiff.comp_contMDiffOn hb
  have hne' : ∀ p ∈ U ∩ V, bc p ≠ -ac p := by
    intro p hp hh
    apply hne p hp
    apply spaceCoordinates.injective
    simpa only [ac,bc,Function.comp_apply,map_neg] using hh
  obtain ⟨hsmooth,hunit,h1,h0,hperp,hpos⟩ := normal_collar_gluing hU hV hac hbc hchi hchiu hchiv
    hchi01 (fun p hp => coordinate_dot_self_of_unit (ha1 p hp))
    (fun p hp => coordinate_dot_self_of_unit (hb1 p hp)) hne'
  let n : M → Space := fun p => spaceCoordinates.symm (first (bc p) (ac p) (chi p))
  let hn : PreferredNormal F := {
    vector := n
    smooth := spaceCoordinates.symm.contDiff.contMDiff.comp hsmooth
    unit := fun p => norm_coordinate_inverse_of_dot_self (hunit p)
    normal := by
      intro p v
      change inner ℝ (surfaceDifferential F p v) (n p) = 0
      rw [← spaceCoordinates_dot]
      change spaceCoordinates (surfaceDifferential F p v) ⬝ᵥ first (bc p) (ac p) (chi p) = 0
      apply hperp
      · intro hp
        exact (spaceCoordinates_dot _ _).trans (haN p hp v)
      · intro hp
        exact (spaceCoordinates_dot _ _).trans (hbN p hp v)
  }
  refine ⟨hn,?_,?_,?_⟩
  · intro p hp
    change spaceCoordinates.symm (first (bc p) (ac p) (chi p)) = a p
    exact (congrArg spaceCoordinates.symm (h1 p hp)).trans
      (spaceCoordinates.symm_apply_apply (a p))
  · intro p hp
    change spaceCoordinates.symm (first (bc p) (ac p) (chi p)) = b p
    exact (congrArg spaceCoordinates.symm (h0 p hp)).trans
      (spaceCoordinates.symm_apply_apply (b p))
  · intro p w hwa hwb
    change inner ℝ w (n p) > 0
    rw [← spaceCoordinates_dot]
    change 0 < spaceCoordinates w ⬝ᵥ first (bc p) (ac p) (chi p)
    apply hpos
    · intro hp
      simpa only [ac,Function.comp_apply,spaceCoordinates_dot] using hwa hp
    · intro hp
      simpa only [bc,Function.comp_apply,spaceCoordinates_dot] using hwb hp

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseChartNormalField
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A normal vector in the nonlinear phase coordinates is normal to the
actual immersion on the corresponding atlas support. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phase_chart_normal_of_outer (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {p : M} (hp : p ∈ (chart (i : M)).source)
    (houter : A.outer i =ᶠ[𝓝 p] fun _ => (1 : ℝ))
    (hx : chart (i : M) p ∈ e.source) (n : NormalFrame.Vec)
    (hn : ∀ v : SmallModes.Base,
      SmallModes.coordDeriv v (A.phaseRealChartMap i e.symm F)
        (baseEquiv (e (chart (i : M) p))) ⬝ᵥ n = 0)
    (v : TangentSpace planeModel p) :
    inner ℝ (surfaceDifferential F p v) (spaceCoordinates.symm n) = 0 := by
  let x := chart (i : M) p
  let H : JetPolynomial.Base → JetPolynomial.Space :=
    (spaceCoordinates ∘ A.vectorChartRead i F) ∘ e.symm
  have hH : ContDiff ℝ ∞ H :=
    (spaceCoordinates.contDiff.comp (A.vectorChartRead_smooth i hF)).comp hi
  have hHnormal (u : JetPolynomial.Base) : fderiv ℝ H (e x) u ⬝ᵥ n = 0 := by
    have hh := hn (baseEquiv u)
    change fderiv ℝ (H ∘ baseEquiv.symm) (baseEquiv (e x)) (baseEquiv u) ⬝ᵥ n = 0 at hh
    rw [fderiv_comp _ (hH.differentiable (by simp) _) baseEquiv.symm.differentiableAt,
      baseEquiv.symm.fderiv,ContinuousLinearMap.comp_apply] at hh
    simpa only [baseEquiv.symm_apply_apply,ContinuousLinearEquiv.coe_coe] using hh
  have hrel : H ∘ e =ᶠ[𝓝 x] spaceCoordinates ∘ A.vectorChartRead i F := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    simp only [H,Function.comp_apply,e.left_inv hy]
  have hd := hrel.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp x (hH.differentiable (by simp) _) (he.differentiable (by simp) _)] at hd
  have hd' := fderiv_comp x spaceCoordinates.differentiableAt
    ((A.vectorChartRead_smooth i hF).differentiable (by simp) _)
  rw [spaceCoordinates.fderiv] at hd'
  have hnormal (u : JetPolynomial.Base) :
      spaceCoordinates (fderiv ℝ (A.vectorChartRead i F) x u) ⬝ᵥ n = 0 := by
    have hh := hHnormal (fderiv ℝ e x u)
    have hh' := congrArg (fun L : JetPolynomial.Base →L[ℝ] JetPolynomial.Space => L u) hd
    rw [hd'] at hh'
    change fderiv ℝ H (e x) (fderiv ℝ e x u) =
      spaceCoordinates (fderiv ℝ (A.vectorChartRead i F) x u) at hh'
    rw [← hh']
    exact hh
  rw [← spaceCoordinates_dot,spaceCoordinates.apply_symm_apply,
    A.vectorChartRead_differential_of_outer i hF hp houter]
  exact hnormal (surfaceDifferential (chart (i : M)) p v)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseNormalLift
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pull a local normal field in the phase coordinates back to the surface.
The result is smooth, unit length and normal on its actual chart domain. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem phaseNormalLift_properties (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {U : Set SmallModes.Base} {W : Set M} {n : SmallModes.Base → NormalFrame.Vec}
    (hn : ContDiffOn ℝ ∞ n U) (hnunit : ∀ x ∈ U, n x ⬝ᵥ n x = 1)
    (hnnormal : ∀ x ∈ U, ∀ v : SmallModes.Base,
      SmallModes.coordDeriv v (A.phaseRealChartMap i e.symm F) x ⬝ᵥ n x = 0)
    (hW : W ⊆ (chart (i : M)).source)
    (hWe : MapsTo (chart (i : M)) W e.source)
    (hWU : MapsTo (fun p => baseEquiv (e (chart (i : M) p))) W U)
    (houter : ∀ p ∈ W, A.outer i =ᶠ[𝓝 p] fun _ => (1 : ℝ)) :
    ContMDiffOn planeModel spaceModel ∞ (A.phaseNormalLift i e n) W ∧
      (∀ p ∈ W, ‖A.phaseNormalLift i e n p‖ = 1) ∧
      ∀ p ∈ W, ∀ v : TangentSpace planeModel p,
        inner ℝ (surfaceDifferential F p v) (A.phaseNormalLift i e n p) = 0 := by
  have hcoord : ContMDiffOn planeModel 𝓘(ℝ,SmallModes.Base) ∞
      (fun p => baseEquiv (e (chart (i : M) p))) W :=
    (baseEquiv.contDiff.comp he).contMDiff.comp_contMDiffOn ((chart_smooth (i : M)).mono hW)
  have hlift := spaceCoordinates.symm.contDiff.contMDiff.comp_contMDiffOn
    (hn.contMDiffOn.comp hcoord hWU)
  refine ⟨hlift,?_,?_⟩
  · intro p hp
    exact norm_coordinate_inverse_of_dot_self (hnunit _ (hWU hp))
  · intro p hp v
    exact A.phase_chart_normal_of_outer i hF e he hi (hW hp) (houter p hp) (hWe hp)
      (n (baseEquiv (e (chart (i : M) p)))) (hnnormal _ (hWU hp)) v

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseNormalNeighborhood
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local exact normal defines a genuine smooth unit normal on an
open surface neighborhood of the closed primitive disk. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma phaseNormalLift_coordinates (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (ν : SmallModes.Base → NormalFrame.Vec) (p : M) :
    spaceCoordinates (A.phaseNormalLift i e ν p) = ν (baseEquiv (e (chart (i : M) p))) :=
  spaceCoordinates.apply_symm_apply _

theorem phase_normal_neighborhood (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {U₀ : Set SmallModes.Base} (hU₀ : IsOpen U₀) {ν : SmallModes.Base → NormalFrame.Vec}
    (hν : ContDiffOn ℝ ∞ ν U₀) (hunit : ∀ x ∈ U₀, ν x ⬝ᵥ ν x = 1)
    (hnormal : ∀ x ∈ U₀, ∀ v : SmallModes.Base,
      SmallModes.coordDeriv v (A.phaseRealChartMap i e.symm F) x ⬝ᵥ ν x = 0)
    {K : Set M}
    (hKs : K ⊆ (chart (i : M)).source)
    (hKe : MapsTo (chart (i : M)) K e.source)
    (hKU : MapsTo (fun p => baseEquiv (e (chart (i : M) p))) K U₀)
    (hKw : ∀ p ∈ K, A.weight i p ≠ 0) :
    ∃ U : Set M, IsOpen U ∧ K ⊆ U ∧ U ⊆ (chart (i : M)).source ∧
      MapsTo (chart (i : M)) U e.source ∧
      MapsTo (fun p => baseEquiv (e (chart (i : M) p))) U U₀ ∧
      ContMDiffOn planeModel spaceModel ∞ (A.phaseNormalLift i e ν) U ∧
      (∀ p ∈ U, ‖A.phaseNormalLift i e ν p‖ = 1) ∧
      ∀ p ∈ U, ∀ v : TangentSpace planeModel p,
        inner ℝ (surfaceDifferential F p v) (A.phaseNormalLift i e ν p) = 0 := by
  let V := e.source ∩ (fun x => baseEquiv (e x)) ⁻¹' U₀
  have hV : IsOpen V := e.open_source.inter
    (hU₀.preimage (baseEquiv.continuous.comp he.continuous))
  let U := ((chart (i : M)).source ∩ (chart (i : M)) ⁻¹' V) ∩ {p | A.weight i p ≠ 0}
  have hU : IsOpen U := ((chart (i : M)).isOpen_inter_preimage hV).inter
    (isOpen_ne.preimage (A.weight_smooth i).continuous)
  have hKU' : K ⊆ U := fun p hp => ⟨⟨hKs hp,⟨hKe hp,hKU hp⟩⟩,hKw p hp⟩
  have hUs : U ⊆ (chart (i : M)).source := fun _ hp => hp.1.1
  have hUe : MapsTo (chart (i : M)) U e.source := fun _ hp => hp.1.2.1
  have hUU : MapsTo (fun p => baseEquiv (e (chart (i : M) p))) U U₀ := fun _ hp => hp.1.2.2
  obtain ⟨hs,hu,hn⟩ := A.phaseNormalLift_properties i hF e he hi hν hunit hnormal hUs hUe hUU
    (fun p hp => A.outer_eventually_one_of_weight_ne_zero i hp.2)
  exact ⟨U,hU,hKU',hUs,hUe,hUU,hs,hu,hn⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothCoverCutoff
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth two-set cutoff with closed supports inside the prescribed
open cover of the compact surface. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

theorem smooth_cover_cutoff {U V : Set M} (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) :
    ∃ χ : M → ℝ, ContMDiff planeModel 𝓘(ℝ) ∞ χ ∧
      tsupport χ ⊆ U ∧ tsupport (fun p => 1-χ p) ⊆ V ∧
      ∀ p, χ p ∈ Icc (0 : ℝ) 1 := by
  have hd : Disjoint Uᶜ Vᶜ := by
    apply disjoint_left.mpr
    intro p hpU hpV
    have hp : p ∈ U ∪ V := by rw [hcover]; trivial
    exact hp.elim hpU hpV
  obtain ⟨χ,hzero,hone,hrange⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    planeModel hU.isClosed_compl hV.isClosed_compl hd (n := (⊤ : ℕ∞))
  refine ⟨χ,χ.contMDiff,?_,?_,hrange⟩
  · intro p hp
    by_contra hnot
    have hz : (χ : M → ℝ) =ᶠ[𝓝 p] 0 := hzero.filter_mono (nhds_le_nhdsSet hnot)
    exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hp
  · intro p hp
    by_contra hnot
    have ho := hone.filter_mono (nhds_le_nhdsSet hnot)
    have hz : (fun q => 1-χ q) =ᶠ[𝓝 p] (0 : M → ℝ) := by
      filter_upwards [ho] with q hq
      simp only [hq,sub_self,Pi.zero_apply]
    exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hp

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CrossingNormalPath
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The preferred-normal adjustment at a crossing: a normalized straight path
stays away from both forbidden antipodes and ends with positive pairings. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

lemma nonzero_of_dot_pos {v m : Vec} (h : 0 < v ⬝ᵥ m) : v ≠ 0 := by
  intro hz
  rw [hz,zero_dotProduct] at h
  exact (lt_irrefl _ h)

lemma normalize_dot_pos {v m : Vec} (h : 0 < v ⬝ᵥ m) : 0 < normalize v ⬝ᵥ m := by
  have hv := nonzero_of_dot_pos h
  have hnorm : 0 < Real.sqrt (v ⬝ᵥ v) := Real.sqrt_pos.mpr (dot_self_pos hv)
  simpa only [normalize,smul_dotProduct,smul_eq_mul] using mul_pos (inv_pos.mpr hnorm) h

end ClosedSurfaceR4.VelocityFrame

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PreferredNormalAvoidanceGlue
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Collar gluing retains full-curve antipode avoidance. Only the transition
region requires positive pairings; the exact endpoint fields cover the rest. -/
noncomputable section
open Set Manifold
open scoped ContDiff
namespace ClosedSurfaceR4
open VelocityFrame NormalFrame
variable {M κ : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma ne_neg_normalize_of_pairing_pos {w n : Vec} (hp : 0 < w ⬝ᵥ n) :
    n ≠ -normalize w := by
  have hw : w ≠ 0 := nonzero_of_dot_pos hp
  have hs : 0 < normalize w ⬝ᵥ w := normalize_dot_pos (dot_self_pos hw)
  intro he
  rw [he,dotProduct_neg,dotProduct_comm w (normalize w)] at hp
  linarith

theorem preferredNormal_collar_avoidance {F a b : M → Space} {U V : Set M}
    (hU : IsOpen U) (hV : IsOpen V)
    (ha : ContMDiffOn planeModel spaceModel ∞ a U)
    (hb : ContMDiffOn planeModel spaceModel ∞ b V)
    (ha1 : ∀ p ∈ U, ‖a p‖ = 1) (hb1 : ∀ p ∈ V, ‖b p‖ = 1)
    (haN : ∀ p ∈ U, ∀ v : TangentSpace planeModel p,
      inner ℝ (surfaceDifferential F p v) (a p) = 0)
    (hbN : ∀ p ∈ V, ∀ v : TangentSpace planeModel p,
      inner ℝ (surfaceDifferential F p v) (b p) = 0)
    (hne : ∀ p ∈ U ∩ V, b p ≠ -a p)
    {χ : M → ℝ} (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ)
    (hχU : tsupport χ ⊆ U) (hχV : tsupport (fun p => 1-χ p) ⊆ V)
    (hχ01 : ∀ p, χ p ∈ Icc (0 : ℝ) 1)
    (C : κ → Set M) (B : κ → M → Vec)
    (haAvoid : ∀ k p, p ∈ C k → p ∈ U → spaceCoordinates (a p) ≠ -normalize (B k p))
    (hbAvoid : ∀ k p, p ∈ C k → p ∈ V → spaceCoordinates (b p) ≠ -normalize (B k p))
    (hpositive : ∀ k p, p ∈ C k → 0 < χ p → χ p < 1 →
      0 < inner ℝ (spaceCoordinates.symm (B k p)) (a p) ∧
      0 < inner ℝ (spaceCoordinates.symm (B k p)) (b p)) :
    ∃ N : PreferredNormal F,
      (∀ p, χ p = 1 → N.vector p = a p) ∧
      (∀ p, χ p = 0 → N.vector p = b p) ∧
      ∀ k p, p ∈ C k → spaceCoordinates (N.vector p) ≠ -normalize (B k p) := by
  obtain ⟨N,hNa,hNb,hNp⟩ := preferredNormal_collar hU hV ha hb ha1 hb1 haN hbN hne
    hχ hχU hχV hχ01
  refine ⟨N,hNa,hNb,?_⟩
  intro k p hp
  by_cases h0 : χ p = 0
  · rw [hNb p h0]
    apply hbAvoid k p hp
    apply hχV
    apply subset_tsupport
    change 1-χ p ≠ 0
    simp only [h0,sub_zero,ne_eq,one_ne_zero,not_false_eq_true]
  by_cases h1 : χ p = 1
  · rw [hNa p h1]
    exact haAvoid k p hp (hχU (subset_tsupport χ (by change χ p ≠ 0; rw [h1]; exact one_ne_zero)))
  have hpos := hpositive k p hp (lt_of_le_of_ne (hχ01 p).1 (Ne.symm h0))
    (lt_of_le_of_ne (hχ01 p).2 h1)
  have hglobal := hNp p (spaceCoordinates.symm (B k p)) (fun _ => hpos.1) (fun _ => hpos.2)
  apply ne_neg_normalize_of_pairing_pos
  simpa only [← spaceCoordinates_dot,spaceCoordinates.apply_symm_apply] using hglobal

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PreferredNormalFromCover
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global preferred normal is constructed from the two local fields;
its smooth cutoff is obtained from the open cover, not assumed. -/
noncomputable section
open Set Manifold
open scoped ContDiff
namespace ClosedSurfaceR4
open VelocityFrame NormalFrame
variable {M κ : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M]

theorem preferredNormal_from_cover {F a b : M → Space} {U V : Set M}
    (hU : IsOpen U) (hV : IsOpen V)
    (ha : ContMDiffOn planeModel spaceModel ∞ a U)
    (hb : ContMDiffOn planeModel spaceModel ∞ b V)
    (ha1 : ∀ p ∈ U, ‖a p‖ = 1) (hb1 : ∀ p ∈ V, ‖b p‖ = 1)
    (haN : ∀ p ∈ U, ∀ v : TangentSpace planeModel p,
      inner ℝ (surfaceDifferential F p v) (a p) = 0)
    (hbN : ∀ p ∈ V, ∀ v : TangentSpace planeModel p,
      inner ℝ (surfaceDifferential F p v) (b p) = 0)
    (hne : ∀ p ∈ U ∩ V, b p ≠ -a p)
    (hcover : U ∪ V = univ)
    (C : κ → Set M) (B : κ → M → Vec)
    (haAvoid : ∀ k p, p ∈ C k → p ∈ U → spaceCoordinates (a p) ≠ -normalize (B k p))
    (hbAvoid : ∀ k p, p ∈ C k → p ∈ V → spaceCoordinates (b p) ≠ -normalize (B k p))
    (hpositive : ∀ k p, p ∈ C k → p ∈ U ∩ V →
      0 < inner ℝ (spaceCoordinates.symm (B k p)) (a p) ∧
      0 < inner ℝ (spaceCoordinates.symm (B k p)) (b p)) :
    ∃ N : PreferredNormal F,
      (∀ p ∈ U \ V, N.vector p = a p) ∧
      (∀ p ∈ V \ U, N.vector p = b p) ∧
      ∀ k p, p ∈ C k → spaceCoordinates (N.vector p) ≠ -normalize (B k p) := by
  obtain ⟨χ,hχ,hχU,hχV,hχ01⟩ := smooth_cover_cutoff hU hV hcover
  obtain ⟨N,hNa,hNb,havoid⟩ := preferredNormal_collar_avoidance hU hV ha hb ha1 hb1 haN hbN hne
    hχ hχU hχV hχ01 C B haAvoid hbAvoid (by
      intro k p hp h0 h1
      apply hpositive k p hp
      constructor
      · exact hχU (subset_tsupport χ (by change χ p ≠ 0; exact h0.ne'))
      · apply hχV
        apply subset_tsupport
        change 1-χ p ≠ 0
        linarith)
  refine ⟨N,?_,?_,havoid⟩
  · intro p hp
    apply hNa
    have hz : 1-χ p = 0 := image_eq_zero_of_notMem_tsupport (f := fun q : M => (1:ℝ)-χ q) (fun h => hp.2 (hχV h))
    linarith
  · intro p hp
    exact hNb p (image_eq_zero_of_notMem_tsupport (fun h => hp.2 (hχU h)))

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_NormalBoundaryCollar
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Strict normal conditions on the disk boundary determine an open collar
that works simultaneously for every later curve. -/
noncomputable section
open Set Manifold
open scoped ContDiff
namespace ClosedSurfaceR4
variable {M κ : Type*} [TopologicalSpace M] [Fintype κ]

lemma normal_boundary_collar {D U V : Set M} (hD : IsOpen D) (hU : IsOpen U) (hV : IsOpen V)
    (hDU : closure D ⊆ U) (hDV : Dᶜ ⊆ V)
    {a b : M → Space} (ha : ContinuousOn a U) (hb : ContinuousOn b V)
    (hne : ∀ p ∈ frontier D, b p ≠ -a p)
    (C : κ → Set M) (hC : ∀ k, IsClosed (C k)) (B : κ → M → Space)
    (hB : ∀ k, ContinuousOn (B k) (U ∩ V))
    (hpositive : ∀ k p, p ∈ C k → p ∈ frontier D →
      0 < inner ℝ (B k p) (a p) ∧ 0 < inner ℝ (B k p) (b p)) :
    ∃ W : Set M, IsOpen W ∧ frontier D ⊆ W ∧ W ⊆ U ∩ V ∧
      (∀ p ∈ W, b p ≠ -a p) ∧
      ∀ k p, p ∈ C k → p ∈ W →
        0 < inner ℝ (B k p) (a p) ∧ 0 < inner ℝ (B k p) (b p) := by
  classical
  have hfUV : frontier D ⊆ U ∩ V := by
    intro p hp
    refine ⟨hDU (frontier_subset_closure hp),hDV ?_⟩
    change p ∉ D
    simpa only [hD.interior_eq] using hp.2
  let Ω := U ∩ V
  have hΩ : IsOpen Ω := hU.inter hV
  let O := Ω ∩ (fun p => b p-(-a p)) ⁻¹' ({0} : Set Space)ᶜ
  have hO : IsOpen O := ((hb.mono inter_subset_right).sub
    (ha.mono inter_subset_left).neg).isOpen_inter_preimage hΩ isClosed_singleton.isOpen_compl
  let P : κ → Set M := fun k => Ω ∩
    (fun p => (inner ℝ (B k p) (a p),inner ℝ (B k p) (b p))) ⁻¹' (Ioi 0 ×ˢ Ioi 0)
  have hP (k : κ) : IsOpen (P k) :=
    (((hB k).inner (ha.mono inter_subset_left)).prodMk
      ((hB k).inner (hb.mono inter_subset_right))).isOpen_inter_preimage hΩ
      (isOpen_Ioi.prod isOpen_Ioi)
  let W := O ∩ ⋂ k : κ, (C k)ᶜ ∪ P k
  refine ⟨W,hO.inter (isOpen_iInter_of_finite (fun k => (hC k).isOpen_compl.union (hP k))),?_,?_,?_,?_⟩
  · intro p hp
    refine ⟨⟨hfUV hp,sub_ne_zero.mpr (hne p hp)⟩,mem_iInter.mpr ?_⟩
    intro k
    by_cases hpk : p ∈ C k
    · exact Or.inr ⟨hfUV hp,hpositive k p hpk hp⟩
    · exact Or.inl hpk
  · exact fun _ hp => hp.1.1
  · intro p hp
    exact sub_ne_zero.mp hp.1.2
  · intro k p hpC hpW
    exact (Or.resolve_left (mem_iInter.mp hpW.2 k) (not_not.mpr hpC)).2

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_PreferredNormalDiskGluing
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the global normal from interior/exterior fields and strict
conditions on the disk boundary. The transition collar is derived. -/
noncomputable section
open Set Manifold
open scoped ContDiff
namespace ClosedSurfaceR4
open VelocityFrame NormalFrame
variable {M κ : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M] [Fintype κ]

theorem preferredNormal_disk_gluing_within {F a b : M → Space} {D U V : Set M}
    (O : Set M) (hO : IsOpen O) (hfO : frontier D ⊆ O)
    (hD : IsOpen D) (hU : IsOpen U) (hV : IsOpen V)
    (hDU : closure D ⊆ U) (hDV : Dᶜ ⊆ V)
    (ha : ContMDiffOn planeModel spaceModel ∞ a U)
    (hb : ContMDiffOn planeModel spaceModel ∞ b V)
    (ha1 : ∀ p ∈ U, ‖a p‖ = 1) (hb1 : ∀ p ∈ V, ‖b p‖ = 1)
    (haN : ∀ p ∈ U, ∀ v : TangentSpace planeModel p,
      inner ℝ (surfaceDifferential F p v) (a p) = 0)
    (hbN : ∀ p ∈ V, ∀ v : TangentSpace planeModel p,
      inner ℝ (surfaceDifferential F p v) (b p) = 0)
    (hne : ∀ p ∈ frontier D, b p ≠ -a p)
    (C : κ → Set M) (hC : ∀ k, IsClosed (C k)) (B : κ → M → Vec)
    (hB : ∀ k, ContinuousOn (B k) (U ∩ V))
    (haAvoid : ∀ k p, p ∈ C k → p ∈ D → spaceCoordinates (a p) ≠ -normalize (B k p))
    (hbAvoid : ∀ k p, p ∈ C k → p ∉ closure D → spaceCoordinates (b p) ≠ -normalize (B k p))
    (hpositive : ∀ k p, p ∈ C k → p ∈ frontier D →
      0 < inner ℝ (spaceCoordinates.symm (B k p)) (a p) ∧
      0 < inner ℝ (spaceCoordinates.symm (B k p)) (b p)) :
    ∃ W : Set M, IsOpen W ∧ frontier D ⊆ W ∧ W ⊆ O ∧ ∃ N : PreferredNormal F,
      (∀ p ∈ D \ W, N.vector p = a p) ∧
      (∀ p ∈ (closure D)ᶜ \ W, N.vector p = b p) ∧
      ∀ k p, p ∈ C k → spaceCoordinates (N.vector p) ≠ -normalize (B k p) := by
  obtain ⟨W₀,hW₀,hfW₀,hW₀UV,hneW₀,hposW₀⟩ := normal_boundary_collar hD hU hV hDU hDV
    ha.continuousOn hb.continuousOn hne C hC (fun k p => spaceCoordinates.symm (B k p))
    (fun k => spaceCoordinates.symm.continuous.comp_continuousOn (hB k)) hpositive
  let W := W₀ ∩ O
  have hW : IsOpen W := hW₀.inter hO
  have hfW : frontier D ⊆ W := fun _ hp => ⟨hfW₀ hp,hfO hp⟩
  have hWUV : W ⊆ U ∩ V := fun _ hp => hW₀UV hp.1
  have hneW : ∀ p ∈ W, b p ≠ -a p := fun p hp => hneW₀ p hp.1
  have hposW : ∀ k p, p ∈ C k → p ∈ W →
      0 < inner ℝ (spaceCoordinates.symm (B k p)) (a p) ∧
      0 < inner ℝ (spaceCoordinates.symm (B k p)) (b p) :=
    fun k p hpC hpW => hposW₀ k p hpC hpW.1
  let U' := D ∪ W
  let V' := (closure D)ᶜ ∪ W
  have hU' : IsOpen U' := hD.union hW
  have hV' : IsOpen V' := isClosed_closure.isOpen_compl.union hW
  have hUU : U' ⊆ U := by
    intro p hp
    rcases hp with hp | hp
    · exact hDU (subset_closure hp)
    · exact (hWUV hp).1
  have hVV : V' ⊆ V := by
    intro p hp
    rcases hp with hp | hp
    · exact hDV (fun h => hp (subset_closure h))
    · exact (hWUV hp).2
  have hcover : U' ∪ V' = univ := by
    apply eq_univ_of_forall
    intro p
    by_cases hp : p ∈ D
    · exact Or.inl (Or.inl hp)
    by_cases hpc : p ∈ closure D
    · have hf : p ∈ frontier D := by
        rw [hD.frontier_eq]
        exact ⟨hpc,hp⟩
      exact Or.inl (Or.inr (hfW hf))
    · exact Or.inr (Or.inl hpc)
  have hUV' : U' ∩ V' ⊆ W := by
    intro p hp
    rcases hp.1 with hpD | hpW
    · rcases hp.2 with hpcl | hpW
      · exact False.elim (hpcl (subset_closure hpD))
      · exact hpW
    · exact hpW
  have havoidW (k : κ) (p : M) (hpC : p ∈ C k) (hpW : p ∈ W) :
      spaceCoordinates (a p) ≠ -normalize (B k p) ∧
      spaceCoordinates (b p) ≠ -normalize (B k p) := by
    have hh := hposW k p hpC hpW
    have hid (t : Space) : B k p ⬝ᵥ spaceCoordinates t = inner ℝ (spaceCoordinates.symm (B k p)) t := by
      rw [← spaceCoordinates_dot,ContinuousLinearEquiv.apply_symm_apply]
    exact ⟨ne_neg_normalize_of_pairing_pos (by rw [hid]; exact hh.1),
      ne_neg_normalize_of_pairing_pos (by rw [hid]; exact hh.2)⟩
  obtain ⟨N,hNa,hNb,havoid⟩ := preferredNormal_from_cover hU' hV' (ha.mono hUU) (hb.mono hVV)
    (fun p hp => ha1 p (hUU hp)) (fun p hp => hb1 p (hVV hp))
    (fun p hp => haN p (hUU hp)) (fun p hp => hbN p (hVV hp))
    (fun p hp => hneW p (hUV' hp)) hcover C B
    (by
      intro k p hpC hpU
      rcases hpU with hpD | hpW
      · exact haAvoid k p hpC hpD
      · exact (havoidW k p hpC hpW).1)
    (by
      intro k p hpC hpV
      rcases hpV with hpcl | hpW
      · exact hbAvoid k p hpC hpcl
      · exact (havoidW k p hpC hpW).2)
    (fun k p hpC hpUV => hposW k p hpC (hUV' hpUV))
  refine ⟨W,hW,hfW,inter_subset_right,N,?_,?_,havoid⟩
  · intro p hp
    exact hNa p ⟨Or.inl hp.1,by
      intro h
      rcases h with hcl | hW
      · exact hcl (subset_closure hp.1)
      · exact hp.2 hW⟩
  · intro p hp
    exact hNb p ⟨Or.inl hp.1,by
      intro h
      rcases h with hD | hW
      · exact hp.1 (subset_closure hD)
      · exact hp.2 hW⟩


end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseDiskNormalGluing
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Glue the constructed exact phase normal to the actual exterior
projection, producing the global preferred normal required by a primitive step. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates NormalFrame VelocityFrame
variable {M κ : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] [Fintype κ]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem phase_disk_normal_gluing_within (i : A.centers) {F n : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hI : ∀ p, Function.Injective (surfaceDifferential F p))
    (hn : ContMDiff planeModel spaceModel ∞ n)
    (houter : ∀ j p, p ∈ tsupport (A.weight j) → A.outer j =ᶠ[𝓝 p] (fun _ => 1))
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    (O : Set M) (hO : IsOpen O)
    {D : Set M} (hD : IsOpen D) (hfO : frontier D ⊆ O)
    {U₀ : Set SmallModes.Base} (hU₀ : IsOpen U₀) {ν : SmallModes.Base → Vec}
    (hν : ContDiffOn ℝ ∞ ν U₀) (hunit : ∀ x ∈ U₀, ν x ⬝ᵥ ν x = 1)
    (hnormal : ∀ x ∈ U₀, ∀ v : SmallModes.Base,
      SmallModes.coordDeriv v (A.phaseRealChartMap i e.symm F) x ⬝ᵥ ν x = 0)
    (hDs : closure D ⊆ (chart (i : M)).source)
    (hDe : MapsTo (chart (i : M)) (closure D) e.source)
    (hDU : MapsTo (fun p => baseEquiv (e (chart (i : M) p))) (closure D) U₀)
    (hDw : ∀ p ∈ closure D, A.weight i p ≠ 0)
    (hproj : ∀ p ∉ D, A.projectedNormalField F n p ≠ 0)
    (hanti : ∀ p ∈ frontier D, spaceCoordinates (A.unitProjectedNormalField F n p) ≠
      -ν (baseEquiv (e (chart (i : M) p))))
    (C : κ → Set M) (hC : ∀ k, IsClosed (C k)) (B : κ → M → Vec)
    (hB : ∀ k, Continuous (B k))
    (hin : ∀ k p, p ∈ C k → p ∈ D →
      ν (baseEquiv (e (chart (i : M) p))) ≠ -normalize (B k p))
    (hout : ∀ k p, p ∈ C k → p ∉ closure D →
      spaceCoordinates (A.unitProjectedNormalField F n p) ≠ -normalize (B k p))
    (hpair : ∀ k p, p ∈ C k → p ∈ frontier D →
      0 < B k p ⬝ᵥ ν (baseEquiv (e (chart (i : M) p))) ∧
      0 < B k p ⬝ᵥ spaceCoordinates (A.unitProjectedNormalField F n p)) :
    ∃ W : Set M, IsOpen W ∧ frontier D ⊆ W ∧ W ⊆ O ∧ ∃ N : PreferredNormal F,
      (∀ p ∈ D \ W, N.vector p = A.phaseNormalLift i e ν p) ∧
      (∀ p ∈ (closure D)ᶜ \ W, N.vector p = A.unitProjectedNormalField F n p) ∧
      ∀ k p, p ∈ C k → spaceCoordinates (N.vector p) ≠ -normalize (B k p) := by
  obtain ⟨U,hU,hDU',_,_,_,ha,haunit,hanormal⟩ :=
    A.phase_normal_neighborhood i hF e he hi hU₀ hν hunit hnormal hDs hDe hDU hDw
  let V := {p | A.projectedNormalField F n p ≠ 0}
  have hgram := fun (j : A.centers) (x : SmallModes.Base) (hx : x ∈ tsupport (A.planeWeight j)) =>
    A.planeWeight_gram_of_immersion hF hI houter j hx
  have hV : IsOpen V := isOpen_ne.preimage (A.projectedNormalField_smooth hF hn hgram).continuous
  have hDV : Dᶜ ⊆ V := hproj
  obtain ⟨hb,hbunit,hbnormal⟩ := A.unitProjectedNormalField_properties hF hn hgram
    (show ∀ p ∈ V, A.projectedNormalField F n p ≠ 0 from fun _ hp => hp)
  apply preferredNormal_disk_gluing_within O hO hfO hD hU hV hDU' hDV ha hb haunit hbunit hanormal hbnormal
    ?_ C hC B (fun k => (hB k).continuousOn) ?_ hout ?_
  · intro p hp heq
    apply hanti p hp
    have h := congrArg spaceCoordinates heq
    simpa only [map_neg,A.phaseNormalLift_coordinates] using h
  · intro k p hp hpd
    rw [A.phaseNormalLift_coordinates]
    exact hin k p hp hpd
  · intro k p hp hpf
    have hh := hpair k p hp hpf
    constructor
    · rw [← spaceCoordinates_dot,spaceCoordinates.apply_symm_apply,A.phaseNormalLift_coordinates]
      exact hh.1
    · rw [← spaceCoordinates_dot,spaceCoordinates.apply_symm_apply]
      exact hh.2


end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ExteriorClosureJets
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth comparison maps agreeing on an open exterior have equal jets
at its boundary. This retains the disk boundary in exterior C2 estimates. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma planeRead_eventuallyEq_at_source {F G : M → Space} {p : M}
    (hFG : F =ᶠ[𝓝 p] G) (i : A.centers) (hp : p ∈ (chart (i : M)).source) :
    (spaceCoordinates ∘ A.vectorPlaneRead i F) =ᶠ[
      𝓝 (planeCoordinateIsometry (chart (i : M) p))]
        (spaceCoordinates ∘ A.vectorPlaneRead i G) := by
  have ht : Tendsto (fun x : SmallModes.Base => (chart (i : M)).symm (planeCoordinateIsometry.symm x))
      (𝓝 (planeCoordinateIsometry (chart (i : M) p))) (𝓝 p) := by
    have hc : Tendsto (chart (i : M)).symm (𝓝 (chart (i : M) p)) (𝓝 p) := by
      simpa only [(chart (i : M)).left_inv hp] using
        ((chart (i : M)).continuousAt_symm ((chart (i : M)).map_source hp)).tendsto
    have hi : Tendsto planeCoordinateIsometry.symm
        (𝓝 (planeCoordinateIsometry (chart (i : M) p))) (𝓝 (chart (i : M) p)) := by
      simpa only [LinearIsometryEquiv.symm_apply_apply] using
        (planeCoordinateIsometry.symm.continuousAt (x := planeCoordinateIsometry (chart (i : M) p))).tendsto
    exact hc.comp hi
  filter_upwards [hFG.comp_tendsto ht] with x hx
  change spaceCoordinates (localize (i : M) (A.outer i) F (planeCoordinateIsometry.symm x)) =
    spaceCoordinates (localize (i : M) (A.outer i) G (planeCoordinateIsometry.symm x))
  unfold localize
  by_cases hxT : planeCoordinateIsometry.symm x ∈ (chart (i : M)).target
  · simp only [indicator_of_mem hxT]
    change F ((chart (i : M)).symm (planeCoordinateIsometry.symm x)) =
      G ((chart (i : M)).symm (planeCoordinateIsometry.symm x)) at hx
    rw [hx]
  · simp only [indicator_of_notMem hxT]

lemma planeRead_jets_eq_on_exterior_closure {F G : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hG : ContMDiff planeModel spaceModel ∞ G)
    {O : Set M} (hext : ∀ p ∈ O, F =ᶠ[𝓝 p] G)
    (i : A.centers) (m : ℕ) :
    ∀ p ∈ closure O, p ∈ (chart (i : M)).source →
      iteratedFDeriv ℝ m (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p)) =
      iteratedFDeriv ℝ m (spaceCoordinates ∘ A.vectorPlaneRead i G)
        (planeCoordinateIsometry (chart (i : M) p)) := by
  let U := (chart (i : M)).source
  have hU : IsOpen U := (chart (i : M)).open_source
  let a := fun p => iteratedFDeriv ℝ m (spaceCoordinates ∘ A.vectorPlaneRead i F)
    (planeCoordinateIsometry (chart (i : M) p))
  let b := fun p => iteratedFDeriv ℝ m (spaceCoordinates ∘ A.vectorPlaneRead i G)
    (planeCoordinateIsometry (chart (i : M) p))
  have hca : ContinuousOn a U :=
    ((spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF)).continuous_iteratedFDeriv
      (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp_continuousOn (planeCoordinateIsometry.continuous.comp_continuousOn (chart (i : M)).continuousOn)
  have hcb : ContinuousOn b U :=
    ((spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hG)).continuous_iteratedFDeriv
      (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp_continuousOn (planeCoordinateIsometry.continuous.comp_continuousOn (chart (i : M)).continuousOn)
  have he : EqOn a b (O ∩ U) := by
    intro p hp
    exact ((A.planeRead_eventuallyEq_at_source (hext p hp.1) i hp.2).iteratedFDeriv ℝ m).eq_of_nhds
  have hclosed := he.of_subset_closure (hca.mono inter_subset_right) (hcb.mono inter_subset_right)
    (fun p hp => ⟨subset_closure hp.1,hp.2⟩) hU.closure_inter
  exact fun p hp hpU => hclosed ⟨hp,hpU⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ExteriorClosureBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Extend the actual exterior C2 estimate through the boundary by continuity
of every coordinate jet. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem exterior_read_C2_bound_closure (j : A.centers) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ F G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ F → ContMDiff planeModel spaceModel ∞ G →
      ContMDiff planeModel spaceModel ∞ V → ContMDiff planeModel spaceModel ∞ W →
      ∀ b c : ℝ, 0 ≤ b → 0 ≤ c →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 c (W-V) →
      ∀ O : Set M, (∀ q ∈ O, V =ᶠ[𝓝 q] G) →
      ∀ p ∈ closure O, p ∈ tsupport (A.weight j) →
      ∀ m ≤ 2,
      ‖iteratedFDeriv ℝ m (spaceCoordinates ∘ A.vectorPlaneRead j (W-F))
        (planeCoordinateIsometry (chart (j : M) p))‖ ≤ D*(b+c) := by
  obtain ⟨D,hD,hd⟩ := A.vectorPlaneRead_bound (V := Space) j 2
  refine ⟨‖spaceCoordinates.toContinuousLinearMap‖*D,
    mul_nonneg (norm_nonneg _) hD,?_⟩
  intro F G V W hF hG hV hW b c hb hc hGF hWV O hext p hpO hp m hm
  let H := (G-F)+(W-V)
  have hH : ContMDiff planeModel spaceModel ∞ H := (hG.sub hF).add (hW.sub hV)
  have hbound : A.WeightedBound 1 2 (b+c) H := by
    intro i
    change WeightedEstimates.WeightedBound univ 1 2 (b+c)
      (localize (i : M) (A.weight i) ((G-F)+(W-V)))
    rw [localize_add]
    exact WeightedEstimates.WeightedBound.add uniqueDiffOn_univ zero_le_one
      (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) (hG.sub hF)).contDiffOn
      (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) (hW.sub hV)).contDiffOn
      (hGF i) (hWV i)
  have hread := hd H 1 (b+c) zero_lt_one le_rfl (add_nonneg hb hc) hH hbound
  have hlinear := hread.linear uniqueDiffOn_univ zero_le_one
    (A.vectorPlaneRead_smooth j hH).contDiffOn spaceCoordinates.toContinuousLinearMap
  change WeightedEstimates.WeightedBound univ 1 2 _
    (spaceCoordinates ∘ A.vectorPlaneRead j H) at hlinear
  have he' : ∀ q ∈ O, W-F =ᶠ[𝓝 q] H := by
    intro q hq
    filter_upwards [hext q hq] with x hx
    dsimp [H]
    rw [hx]
    abel
  have hjet := A.planeRead_jets_eq_on_exterior_closure (hW.sub hF) hH he' j m
    p hpO (A.weight_support j hp)
  change iteratedFDeriv ℝ m (spaceCoordinates ∘ A.vectorPlaneRead j (W-F))
    (planeCoordinateIsometry (chart (j : M) p)) = _ at hjet
  rw [hjet]
  simpa only [one_pow,one_mul,iteratedFDerivWithin_univ,mul_assoc] using
    hlinear m hm (planeCoordinateIsometry (chart (j : M) p)) (mem_univ _)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ExteriorClosureNormal
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The retained slow baseline and C2 correction control the actual
normalized exterior normal, uniformly over every atlas chart. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial RealModes SmallModes NormalFrame WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem exterior_projected_normal_close_closure {F n : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (hn : ContMDiff planeModel spaceModel ∞ n)
    (hunit : ∀ p, ‖n p‖ = 1)
    (hN : ∀ p v, inner ℝ (surfaceDifferential F p v) (n p) = 0)
    (hD : ∀ i p, p ∈ tsupport (A.weight i) →
      gramDet (coordDeriv dx (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p)))
      (coordDeriv dy (spaceCoordinates ∘ A.vectorPlaneRead i F)
        (planeCoordinateIsometry (chart (i : M) p))) ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ContMDiff planeModel spaceModel ∞ W → ∀ b c : ℝ, 0 ≤ b → 0 ≤ c → b+c < ρ →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 c (W-V) →
      ∀ O : Set M, (∀ q ∈ O, V =ᶠ[𝓝 q] G) →
      ∀ p ∈ closure O,
      A.projectedNormalField W n p ≠ 0 ∧ ‖A.unitProjectedNormalField W n p-n p‖ < ε := by
  classical
  obtain ⟨δ,hδ,hnear⟩ := A.compact_atlas_projection_stability hF hn hunit hN hD hε
  choose D hD0 hbound using fun i => A.exterior_read_C2_bound_closure i
  obtain ⟨ρ,hρ,_,hle⟩ := finite_positive_threshold (fun i => δ/(D i+1))
    (fun i => div_pos hδ (by have := hD0 i; positivity))
  refine ⟨ρ,hρ,?_⟩
  intro G V W hG hV hW b c hb hc hbc hGF hWV O hext p hpO
  apply hnear W p
  intro i hi v hv
  have hp := subset_tsupport (A.weight i) hi
  have hd := hbound i F G V W hF hG hV hW b c hb hc hGF hWV O hext p hpO hp 1 (by omega)
  rw [norm_iteratedFDeriv_one] at hd
  have hs : D i*(b+c) < δ := by
    have ht := (lt_div_iff₀ (by have := hD0 i; positivity : 0 < D i+1)).mp
      (hbc.trans_le (hle i))
    nlinarith
  have hnV : ‖v‖ ≤ 1 := by
    rcases hv with rfl | hv
    · simp [dx]
    · have hv' : v = dy := by simpa only [mem_singleton_iff] using hv
      subst v
      simp [dy]
  have hre : spaceCoordinates ∘ A.vectorPlaneRead i (W-F) =
      (spaceCoordinates ∘ A.vectorPlaneRead i W)-(spaceCoordinates ∘ A.vectorPlaneRead i F) := by
    rw [A.vectorPlaneRead_sub]
    funext y
    exact map_sub spaceCoordinates _ _
  rw [hre,fderiv_sub
    (spaceCoordinates.differentiableAt.comp _ ((A.vectorPlaneRead_smooth i hW).differentiable (by simp) _))
    (spaceCoordinates.differentiableAt.comp _ ((A.vectorPlaneRead_smooth i hF).differentiable (by simp) _))] at hd
  change ‖((fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i W) _)-
    (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) _)) v‖ < δ
  exact ((ContinuousLinearMap.le_opNorm _ _).trans
    ((mul_le_mul_of_nonneg_left hnV (norm_nonneg _)).trans (by simpa only [mul_one] using hd))).trans_lt hs

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CrossingSafeNormalGluing
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Glue the constructed exact phase normal to the actual exterior
projection, producing the global preferred normal required by a primitive step. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates NormalFrame VelocityFrame
variable {M κ : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] [Fintype κ]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem crossing_safe_phase_normal_gluing (i : A.centers) {F n : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hI : ∀ p, Function.Injective (surfaceDifferential F p))
    (hn : ContMDiff planeModel spaceModel ∞ n)
    (houter : ∀ j p, p ∈ tsupport (A.weight j) → A.outer j =ᶠ[𝓝 p] (fun _ => 1))
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {D : Set M} (hD : IsOpen D)
    (E : Set M) (hE : E.Finite) (hEf : Disjoint E (frontier D))
    {U₀ : Set SmallModes.Base} (hU₀ : IsOpen U₀) {ν : SmallModes.Base → Vec}
    (hν : ContDiffOn ℝ ∞ ν U₀) (hunit : ∀ x ∈ U₀, ν x ⬝ᵥ ν x = 1)
    (hnormal : ∀ x ∈ U₀, ∀ v : SmallModes.Base,
      SmallModes.coordDeriv v (A.phaseRealChartMap i e.symm F) x ⬝ᵥ ν x = 0)
    (hDs : closure D ⊆ (chart (i : M)).source)
    (hDe : MapsTo (chart (i : M)) (closure D) e.source)
    (hDU : MapsTo (fun p => baseEquiv (e (chart (i : M) p))) (closure D) U₀)
    (hDw : ∀ p ∈ closure D, A.weight i p ≠ 0)
    (hproj : ∀ p ∉ D, A.projectedNormalField F n p ≠ 0)
    (hanti : ∀ p ∈ frontier D, spaceCoordinates (A.unitProjectedNormalField F n p) ≠
      -ν (baseEquiv (e (chart (i : M) p))))
    (C : κ → Set M) (hC : ∀ k, IsClosed (C k)) (B : κ → M → Vec)
    (hB : ∀ k, Continuous (B k))
    (hin : ∀ k p, p ∈ C k → p ∈ D →
      ν (baseEquiv (e (chart (i : M) p))) ≠ -normalize (B k p))
    (hout : ∀ k p, p ∈ C k → p ∉ closure D →
      spaceCoordinates (A.unitProjectedNormalField F n p) ≠ -normalize (B k p))
    (hpair : ∀ k p, p ∈ C k → p ∈ frontier D →
      0 < B k p ⬝ᵥ ν (baseEquiv (e (chart (i : M) p))) ∧
      0 < B k p ⬝ᵥ spaceCoordinates (A.unitProjectedNormalField F n p)) :
    ∃ N : PreferredNormal F,
      (∀ k p, p ∈ C k → spaceCoordinates (N.vector p) ≠ -normalize (B k p)) ∧
      ∀ p ∈ E, (p ∈ D → N.vector p = A.phaseNormalLift i e ν p) ∧
        (p ∉ D → N.vector p = A.unitProjectedNormalField F n p) := by
  have hf : frontier D ⊆ Eᶜ := fun p hp he => Set.disjoint_left.mp hEf he hp
  obtain ⟨W,hW,_,hWE,N,hNa,hNb,havoid⟩ := A.phase_disk_normal_gluing_within i hF hI
    hn houter e he hi Eᶜ hE.isClosed.isOpen_compl hD hf hU₀ hν hunit hnormal
    hDs hDe hDU hDw hproj hanti C hC B hB hin hout hpair
  refine ⟨N,havoid,?_⟩
  intro p hp
  have hpW : p ∉ W := fun hw => hWE hw hp
  refine ⟨fun hpD => hNa p ⟨hpD,hpW⟩,?_⟩
  intro hpD
  have hpc : p ∉ closure D := by
    intro hpc
    have hpf : p ∈ frontier D := by rw [hD.frontier_eq]; exact ⟨hpc,hpD⟩
    exact Set.disjoint_left.mp hEf hp hpf
  exact hNb p ⟨hpc,hpW⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SurfaceCurveNormalGluing
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global normal step for actual surface curves. A single smallness
threshold handles every exterior curve and the whole exterior normal field. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceJetCoordinates RealModes SmallModes NormalFrame VelocityFrame
variable {M κ : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] [Fintype κ]
namespace SmoothingAtlas
variable (A B : SmoothingAtlas M)

theorem finite_curve_disk_normal_oai
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
    (E : Set M) (hE : E.Finite) (hEf : Disjoint E (frontier D)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G V W : M → Space,
      ContMDiff planeModel spaceModel ∞ G → ContMDiff planeModel spaceModel ∞ V →
      ∀ h : SmoothMetric M, IsSmoothIsometricImmersion M h W →
      ∀ b d : ℝ, 0 ≤ b → 0 ≤ d → b+d < ρ →
      A.WeightedBound 1 2 b (G-F) → A.WeightedBound 1 2 d (W-V) →
      (∀ p ∉ closure D, V =ᶠ[𝓝 p] G) →
      ∀ U₀ : Set SmallModes.Base, IsOpen U₀ → ∀ ν : SmallModes.Base → Vec,
      ContDiffOn ℝ ∞ ν U₀ →
      (∀ x ∈ U₀, ν x ⬝ᵥ ν x = 1) →
      (∀ x ∈ U₀, ∀ v : SmallModes.Base,
        SmallModes.coordDeriv v (A.phaseRealChartMap i e.symm W) x ⬝ᵥ ν x = 0) →
      MapsTo (fun p => baseEquiv (e (chart (i : M) p))) (closure D) U₀ →
      (∀ p ∈ frontier D, spaceCoordinates (A.unitProjectedNormalField W n.vector p) ≠
        -ν (baseEquiv (e (chart (i : M) p)))) →
      (∀ k p, p ∈ (curves k).carrier → p ∈ D →
        (curves k).second W p ≠ 0 ∧
        ν (baseEquiv (e (chart (i : M) p))) ≠ -normalize ((curves k).second W p)) →
      (∀ k p, p ∈ (curves k).carrier → p ∈ frontier D →
        0 < (curves k).second W p ⬝ᵥ ν (baseEquiv (e (chart (i : M) p))) ∧
        0 < (curves k).second W p ⬝ᵥ spaceCoordinates (A.unitProjectedNormalField W n.vector p)) →
      ∃ N : PreferredNormal W,
        (∀ k p, p ∈ (curves k).carrier → (curves k).second W p ≠ 0 ∧
          spaceCoordinates (N.vector p) ≠ -normalize ((curves k).second W p)) ∧
        ∀ p ∈ E, (p ∈ D → N.vector p = A.phaseNormalLift i e ν p) ∧
          (p ∉ D → N.vector p = A.unitProjectedNormalField W n.vector p) := by
  classical
  choose r hr hpres using fun k => (curves k).exterior_preservation A hF n houter
    (fun p hp => (hold k p hp).1) (fun p hp => (hold k p hp).2)
  obtain ⟨s,hs,_,hsr⟩ := finite_positive_threshold r hr
  obtain ⟨t,ht,hproj⟩ := A.exterior_projected_normal_close_closure hF.1 n.smooth n.unit n.normal
    (fun j p hp => A.planeRead_gram_of_immersion hF.1
      (IsSmoothIsometricImmersion.mfderiv_injective hF) houter j hp) zero_lt_one
  refine ⟨min s t,lt_min hs ht,?_⟩
  intro G V W hG hV h hW b d hb hd hbd hGF hWV hext U₀ hU₀ ν hν hunit hnormal hDU hanti hin hpair
  have hclosure (p : M) (hp : p ∉ D) : p ∈ closure (closure D)ᶜ := by
    rwa [closure_compl,hDr]
  have hcurve (k : κ) (p : M) (hp : p ∈ (curves k).carrier) (hpD : p ∉ D) :=
    hpres k G V W hG hV hW.1 b d hb hd
      ((hbd.trans_le (min_le_left _ _)).trans_le (hsr k)) hGF hWV (closure D)ᶜ
      hext p ⟨hp,hclosure p hpD⟩
  have hpn (p : M) (hpD : p ∉ D) : A.projectedNormalField W n.vector p ≠ 0 :=
    (hproj G V W hG hV hW.1 b d hb hd (hbd.trans_le (min_le_right _ _)) hGF hWV
      (closure D)ᶜ hext p (hclosure p hpD)).1
  obtain ⟨N,havoid,hmatch⟩ := A.crossing_safe_phase_normal_gluing i hW.1
    (IsSmoothIsometricImmersion.mfderiv_injective hW) n.smooth houter e he hi hD E hE hEf
    hU₀ hν hunit hnormal hDs hDe hDU hDw hpn hanti
    (fun k => (curves k).carrier) (fun k => (curves k).compact.isClosed)
    (fun k => (curves k).second W) (fun k => ((curves k).second_smooth hW).continuous)
    (fun k p hp hpD => (hin k p hp hpD).2)
    (fun k p hp hpD => (hcurve k p hp (fun hpd => hpD (subset_closure hpd))).2.2) hpair
  refine ⟨N,?_,hmatch⟩
  intro k p hp
  refine ⟨?_,havoid k p hp⟩
  by_cases hpD : p ∈ D
  · exact (hin k p hp hpD).1
  · exact (hcurve k p hp hpD).2.1

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_curve_disk_normal_oai.{u_1, u_2} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_curve_disk_normal_oai.{u_1, u_2}
