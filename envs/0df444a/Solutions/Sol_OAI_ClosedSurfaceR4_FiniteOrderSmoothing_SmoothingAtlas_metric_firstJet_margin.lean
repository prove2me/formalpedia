-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.metric_firstJet_margin
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:31:18.240221+00:00
-- url     : https://prove2.me/submissions/033e5a7c-0cd8-42a3-a498-76890acdebda

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
import Definitions.Def_OAIQ249SI012

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
local instance coordinateFiberSpace_r84b943_1 : NormedSpace ℝ TensorFiber := inferInstance
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
local instance chartReadSectionNormed_r84b943_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance chartReadSectionSpace_r84b943_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
local instance planeReadSectionSpace_r84b943_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasFiniteCancellation
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite global metric-linear corrections assembled from local phase solvers. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance atlasSolveFiberNormed_r84b943_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasSolveFiberSpace_r84b943_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance atlasSolveDualAdd_r84b943_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasSolveDualSmul_r84b943_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance atlasSolveSectionNormed_r84b943_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasSolveSectionSpace_r84b943_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma jetChartMap_plane (i : A.centers) (F : M → Space) :
    A.jetChartMap i F ∘ planeCoordinateIsometry.symm = spaceCoordinates ∘ A.vectorPlaneRead i F := rfl

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
local instance metricReferenceSectionNormed_r84b943_1 (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricReferenceSectionSpace_r84b943_1 (p : M) :
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
local instance metricReadExactDualSmul_r84b943_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReadExactFiberNormed
local instance metricReadExactSectionNormed_r84b943_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricReadExactSectionSpace_r84b943_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasMetricLocalModel
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local coordinate models of the complete perturbed global metric. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricLocalDualAdd
local instance metricLocalFiberNormed_r84b943_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance metricLocalFiberSpace_r84b943_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance metricLocalDualSmul_r84b943_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance metricLocalSectionNormed_r84b943_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricLocalSectionSpace_r84b943_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma metric_read_on_support (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {x : Base}
    (hx : x ∈ (A.chartWeightCompact i : Set Base)) :
    RealModes.realMetricTensor (A.jetChartMap i F ∘ planeCoordinateIsometry.symm)
        (planeCoordinateIsometry x) = A.tensorChartRead i (inducedTensor F) x := by
  obtain ⟨p,hp,rfl⟩ := hx
  have hread := A.tensorChartRead_on_weight i (inducedTensor F) hp
  rw [A.metric_component_on_weight i hF hp,fiberToThree_fromThree] at hread
  exact hread.symm

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_MetricJetMargins
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact metric positivity controls the first jets of all sufficiently
accurate approximate isometries. -/
noncomputable section
open Set
open scoped Topology BigOperators Matrix
namespace ClosedSurfaceR4.RealModes
open SmallModes

lemma norm_le_one_add_dot_self (X : RVec 4) : ‖X‖ ≤ 1+X ⬝ᵥ X := by
  have hsum : 0 ≤ X ⬝ᵥ X := Finset.sum_nonneg (fun j _ => mul_self_nonneg (X j))
  apply (pi_norm_le_iff_of_nonneg (by linarith : 0 ≤ 1+X ⬝ᵥ X)).mpr
  intro i
  have hi : X i*X i ≤ X ⬝ᵥ X :=
    Finset.single_le_sum (fun j _ => mul_self_nonneg (X j)) (Finset.mem_univ i)
  rw [Real.norm_eq_abs]
  nlinarith [sq_nonneg (|X i|-1/2),sq_abs (X i)]

lemma firstJetPair_norm_le_metric (F : RField 4) (p : Base) :
    ‖firstJetPair F p‖ ≤ 1+‖realMetricTensor F p‖ := by
  apply (max_le_iff).mpr
  constructor
  · have h := (le_abs_self (realMetricTensor F p 0)).trans
      (norm_le_pi_norm (realMetricTensor F p) (0 : Fin 3))
    exact (norm_le_one_add_dot_self _).trans (by
      change 1+realMetricTensor F p 0 ≤ _
      linarith)
  · have h := (le_abs_self (realMetricTensor F p 2)).trans
      (norm_le_pi_norm (realMetricTensor F p) (2 : Fin 3))
    exact (norm_le_one_add_dot_self _).trans (by
      change 1+realMetricTensor F p 2 ≤ _
      linarith)

lemma gramDet_firstJetPair (F : RField 4) (p : Base) :
    NormalFrame.gramDet (firstJetPair F p).1 (firstJetPair F p).2 =
      realMetricTensor F p 0*realMetricTensor F p 2-(realMetricTensor F p 1)^2 := rfl

/-- Only the compact set of prescribed positive metrics is fixed. The
approximate immersion and all its higher derivatives remain arbitrary. -/
theorem compact_metric_firstJet_margin {T : Set PhaseMean.Tensor} (hT : IsCompact T)
    (hpos : ∀ H ∈ T, 0 < H 0*H 2-(H 1)^2) :
    ∃ ε R c : ℝ, 0 < ε ∧ 0 < R ∧ 0 < c ∧
      ∀ (F : RField 4) (p : Base) (H : PhaseMean.Tensor), H ∈ T →
      ‖realMetricTensor F p-H‖ < ε →
      ‖firstJetPair F p‖ ≤ R ∧ c ≤ NormalFrame.gramDet
        (firstJetPair F p).1 (firstJetPair F p).2 := by
  let det : PhaseMean.Tensor → ℝ := fun H => H 0*H 2-(H 1)^2
  have hd : Continuous det := by unfold det; fun_prop
  by_cases hne : T.Nonempty
  · obtain ⟨H₀,hH₀,hmin⟩ := hT.exists_isMinOn hne hd.continuousOn
    let c := det H₀/2
    have hc : 0 < c := half_pos (hpos H₀ hH₀)
    have hs : T ⊆ {H | c < det H} := by
      intro H hH
      exact (half_lt_self (hpos H₀ hH₀)).trans_le (hmin hH)
    obtain ⟨ε,hε,hthick⟩ := hT.exists_thickening_subset_open
      (isOpen_lt continuous_const hd) hs
    obtain ⟨B,hB⟩ := hT.exists_bound_of_continuousOn continuousOn_id
    let R := |B|+2
    have hR : 0 < R := by dsimp [R] <;> positivity
    refine ⟨min ε 1,R,c,lt_min hε zero_lt_one,hR,hc,?_⟩
    intro F p H hH hclose
    have hclose1 : ‖realMetricTensor F p-H‖ ≤ 1 :=
      (hclose.trans_le (min_le_right _ _)).le
    have hmetric : ‖realMetricTensor F p‖ ≤ |B|+1 := by
      calc
        ‖realMetricTensor F p‖ = ‖(realMetricTensor F p-H)+H‖ := by congr 1; abel
        _ ≤ ‖realMetricTensor F p-H‖+‖H‖ := norm_add_le _ _
        _ ≤ 1+B := add_le_add hclose1 (hB H hH)
        _ ≤ |B|+1 := by linarith [le_abs_self B]
    refine ⟨(firstJetPair_norm_le_metric F p).trans (by dsimp [R] <;> linarith),?_⟩
    rw [gramDet_firstJetPair]
    exact (hthick (Metric.mem_thickening_iff.mpr
      ⟨H,hH,by simpa only [dist_eq_norm] using hclose.trans_le (min_le_left _ _)⟩)).le
  · refine ⟨1,1,1,zero_lt_one,zero_lt_one,zero_lt_one,?_⟩
    intro F p H hH _
    exact False.elim (hne ⟨H,hH⟩)

end ClosedSurfaceR4.RealModes

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
local instance metricJetsFiberNormed_r84b943_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance metricJetsFiberSpace_r84b943_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance metricJetsDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
namespace SmoothingAtlas
local instance metricJetsFiberNormed_r84b943_2 : NormedAddCommGroup TensorFiber := inferInstance
local instance metricJetsFiberSpace_r84b943_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance metricJetsDualSmul_r84b943_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance metricJetsSectionNormed_r84b943_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricJetsSectionSpace_r84b943_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma modeSupport_subset_coordinateDomain (i : A.centers) :
    (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ coordinateDomain (i : M) := by
  rintro x ⟨y,⟨p,hp,rfl⟩,rfl⟩
  have hs : p ∈ (coordinateChart (i : M)).source := by
    simpa only [coordinateChart_source,chart_source] using A.weight_support i hp
  rw [← coordinateChart_target]
  exact (coordinateChart (i : M)).map_source hs

lemma metricPlaneRead_on_support {V : M → Space}
    (hV : ContMDiff planeModel spaceModel ∞ V) (i : A.centers) {x : SmallModes.Base}
    (hx : x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    realMetricTensor (spaceCoordinates ∘ A.vectorPlaneRead i V) x =
      A.tensorPlaneRead i (inducedTensor V) x := by
  obtain ⟨y,hy,rfl⟩ := hx
  rw [← A.jetChartMap_plane]
  simpa only [tensorPlaneRead,Function.comp_apply,LinearIsometryEquiv.symm_apply_apply] using
    A.metric_read_on_support i hV hy

/-- The constants depend on the prescribed metric and fixed atlas, not on
any derivatives of the approximate immersion. -/
theorem metric_firstJet_margin_oai (g : SmoothMetric M) :
    ∃ ε R c : ℝ, 0 < ε ∧ 0 < R ∧ 0 < c ∧
      ∀ V : M → Space, ContMDiff planeModel spaceModel ∞ V →
      ∀ b : ℝ, 0 ≤ b → b < ε →
      A.TensorWeightedBound 1 0 b (inducedTensor V-g.inner) →
      ∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
      ‖firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i V) x‖ ≤ R ∧
        c ≤ NormalFrame.gramDet
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i V) x).1
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i V) x).2 := by
  let T : Set PhaseMean.Tensor := ⋃ i : A.centers,
    A.tensorPlaneRead i g.inner '' (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)
  have hT : IsCompact T := isCompact_iUnion (fun i =>
    (modeSupport (A.chartWeightCompact i)).isCompact.image (A.tensorPlaneRead_smooth i g.contMDiff).continuous)
  have hpos : ∀ H ∈ T, 0 < H 0*H 2-(H 1)^2 := by
    intro H hH
    obtain ⟨i,hi⟩ := mem_iUnion.mp hH
    obtain ⟨x,hx,rfl⟩ := hi
    rw [A.tensorPlaneRead_metric g i hx]
    exact (coordinateMetric_positive g (i : M) (A.modeSupport_subset_coordinateDomain i hx)).2
  obtain ⟨ε,R,c,hε,hR,hc,hmargin⟩ := compact_metric_firstJet_margin hT hpos
  choose D hD hread using fun i : A.centers => A.tensorPlaneRead_bound i 0
  have heps (i : A.centers) : 0 < ε/(1+D i) := div_pos hε (by linarith [hD i])
  obtain ⟨ρ,hρ,_,hρall⟩ := finite_positive_threshold (fun i => ε/(1+D i)) heps
  refine ⟨ρ,R,c,hρ,hR,hc,?_⟩
  intro V hV b hb hbρ hclose i x hx
  apply hmargin (spaceCoordinates ∘ A.vectorPlaneRead i V) x (A.tensorPlaneRead i g.inner x)
    (mem_iUnion.mpr ⟨i,mem_image_of_mem _ hx⟩)
  have hlocal := hread i (inducedTensor V-g.inner) 1 b zero_lt_one le_rfl hb
    ((A.inducedTensor_smooth hV).sub_section g.contMDiff) hclose
  have hh := hlocal.norm_le (mem_univ x)
  rw [A.tensorPlaneRead_sub] at hh
  rw [A.metricPlaneRead_on_support hV i hx]
  have hb' := (lt_div_iff₀ (by linarith [hD i] : 0 < 1+D i)).mp
    (hbρ.trans_le (hρall i))
  exact hh.trans_lt (by nlinarith)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.metric_firstJet_margin_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.metric_firstJet_margin_oai.{u_1}
