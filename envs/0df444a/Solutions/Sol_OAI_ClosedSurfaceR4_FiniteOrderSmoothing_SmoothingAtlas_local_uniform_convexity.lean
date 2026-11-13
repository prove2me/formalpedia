-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.local_uniform_convexity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:31:16.445108+00:00
-- url     : https://prove2.me/submissions/9198b00b-21bb-4846-ad02-e242d884aa4b

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ConvexQuadraticPhase
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
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

lemma metricConnectionAt_contDiffAt {J : MetricFirstJet} (hJ : metricJetDet J ≠ 0) :
    ContDiffAt ℝ ∞ metricConnectionAt J := by
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;>
    simp only [metricConnectionAt, Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
    unfold metricJetDet at * <;> fun_prop (disch := exact hJ)

theorem compact_metricConnection_bound {K : Set MetricFirstJet} (hK : IsCompact K)
    (hdet : ∀ J ∈ K, metricJetDet J ≠ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ J ∈ K, ∀ i, ‖metricConnectionAt J i‖ ≤ B := by
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn
    (fun J hJ => (metricConnectionAt_contDiffAt (hdet J hJ)).continuousAt.continuousWithinAt)
  refine ⟨max 0 B, le_max_left _ _, fun J hJ i => ?_⟩
  exact (norm_le_pi_norm _ i).trans ((hB J hJ).trans (le_max_right _ _))

private lemma abs_quadratic_combination {a b c B x y : ℝ} (hB : 0 ≤ B)
    (ha : |a| ≤ B) (hb : |b| ≤ B) (hc : |c| ≤ B) :
    |x^2*a + (x*y+y*x)*b + y^2*c| ≤ 2*B*(x^2+y^2) := by
  have hm : x*y+y*x = 2*x*y := by ring
  rw [hm]
  have h1 : |x^2*a| ≤ x^2*B := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg x)]
    exact mul_le_mul_of_nonneg_left ha (sq_nonneg x)
  have h2 : |2*x*y*b| ≤ 2 * |x| * |y| * B := by
    simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  have h3 : |y^2*c| ≤ y^2*B := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg y)]
    exact mul_le_mul_of_nonneg_left hc (sq_nonneg y)
  have hxy : 2 * |x| * |y| ≤ x^2+y^2 := by
    nlinarith [sq_nonneg (|x|-|y|), sq_abs x, sq_abs y]
  have hmB := mul_le_mul_of_nonneg_right hxy hB
  have htri := (abs_add_le (x^2*a+2*x*y*b) (y^2*c)).trans
    (add_le_add (abs_add_le (x^2*a) (2*x*y*b)) le_rfl)
  nlinarith

lemma connectionContract_diagonal_bound {Gamma : Fin 3 → Base} {B : ℝ}
    (hB : 0 ≤ B) (hGamma : ∀ i, ‖Gamma i‖ ≤ B) (v : Base) :
    |(connectionContract Gamma v v).1| ≤ 2*B*(v.1^2+v.2^2) ∧
      |(connectionContract Gamma v v).2| ≤ 2*B*(v.1^2+v.2^2) := by
  have h1 (i : Fin 3) : |(Gamma i).1| ≤ B := by
    exact (norm_fst_le (Gamma i)).trans (hGamma i)
  have h2 (i : Fin 3) : |(Gamma i).2| ≤ B := by
    exact (norm_snd_le (Gamma i)).trans (hGamma i)
  constructor
  · simpa only [connectionContract, Prod.fst_add, Prod.smul_fst, smul_eq_mul, pow_two] using
      (abs_quadratic_combination (x := v.1) (y := v.2) hB (h1 0) (h1 1) (h1 2))
  · simpa only [connectionContract, Prod.snd_add, Prod.smul_snd, smul_eq_mul, pow_two] using
      (abs_quadratic_combination (x := v.1) (y := v.2) hB (h2 0) (h2 1) (h2 2))

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_TensorFiberCoordinates
attribute [-instance] _root_.instVAddIntReal_solutions
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
local instance coordinateFiberSpace_r836e2e_1 : NormedSpace ℝ TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateDualSmul
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coordinateFiberGroup
lemma fiberToThree_apply (B : TensorFiber) (k : Fin 3) :
    fiberToThree B k = B (planeCoordinates.symm (firstDirection k))
      (planeCoordinates.symm (secondDirection k)) := rfl

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
local instance chartReadSectionNormed_r836e2e_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance chartReadSectionSpace_r836e2e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
local instance planeReadSectionSpace_r836e2e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceDualSmul
local instance metricReferenceSectionNormed_r836e2e_1 (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricReferenceSectionSpace_r836e2e_1 (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma metric_inner_smooth (g : SmoothMetric M) :
    ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (g.inner p)) := g.contMDiff

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReferenceFiberSpace
local instance metricReferenceSectionNormed_r836e2e_2 (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricReferenceSectionSpace_r836e2e_2 (p : M) :
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

lemma tensorPlaneRead_metric_smooth (g : SmoothMetric M) (i : A.centers) :
    ContDiff ℝ ∞ (A.tensorPlaneRead i g.inner) :=
  A.tensorPlaneRead_smooth i (metric_inner_smooth g)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_MetricReadBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact positive metric range and global first-order bounds for atlas readings. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReadBoundsFiberNormed
local instance metricReadBoundsFiberSpace_r836e2e_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance metricReadBoundsDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReadBoundsFiberNormed
local instance metricReadBoundsFiberSpace_r836e2e_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance metricReadBoundsDualSmul_r836e2e_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance metricReadBoundsSectionNormed_r836e2e_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricReadBoundsSectionSpace_r836e2e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma metricReadSupport_domain (i : A.centers) :
    (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ coordinateDomain (i : M) := by
  rintro x ⟨y,⟨p,hp,rfl⟩,rfl⟩
  have hs : p ∈ (coordinateChart (i : M)).source := by
    simpa only [coordinateChart_source,chart_source] using A.weight_support i hp
  rw [← coordinateChart_target]
  exact (coordinateChart (i : M)).map_source hs

theorem metric_plane_read_bounds (g : SmoothMetric M) :
    ∃ T : Set PhaseMean.Tensor, ∃ B : ℝ, IsCompact T ∧
      (∀ H ∈ T, 0 < H 0) ∧ (∀ H ∈ T, 0 < H 0*H 2-(H 1)^2) ∧ 1 ≤ B ∧
      (∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        A.tensorPlaneRead i g.inner x ∈ T) ∧
      (∀ i x, ‖A.tensorPlaneRead i g.inner x‖ ≤ B) ∧
      (∀ i x y, ‖A.tensorPlaneRead i g.inner y-A.tensorPlaneRead i g.inner x‖ ≤ B*‖y-x‖) := by
  classical
  let T : Set PhaseMean.Tensor := ⋃ i : A.centers,
    A.tensorPlaneRead i g.inner '' (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)
  have hT : IsCompact T := isCompact_iUnion (fun i =>
    (modeSupport (A.chartWeightCompact i)).isCompact.image (A.tensorPlaneRead_metric_smooth g i).continuous)
  have hpos (H : PhaseMean.Tensor) (hH : H ∈ T) :
      0 < H 0 ∧ 0 < H 0*H 2-(H 1)^2 := by
    obtain ⟨i,x,hx,rfl⟩ := mem_iUnion.mp hH
    rw [A.tensorPlaneRead_metric g i hx]
    exact coordinateMetric_positive g (i : M) (A.metricReadSupport_domain i hx)
  obtain ⟨C,hC,hbound⟩ := A.exists_bundle_bound A.tensorTriv A.tensorTriv_domain 1 g.contMDiff
  choose D hD hd using fun i : A.centers => A.tensorPlaneRead_bound i 1
  let B : ℝ := 1+∑ i : A.centers, D i*C
  have hB : 1 ≤ B := by
    have hh := Finset.sum_nonneg (s := Finset.univ) (fun i _ => mul_nonneg (hD i) hC)
    change 1 ≤ 1+∑ i : A.centers, D i*C
    linarith
  have hb (i : A.centers) : WeightedEstimates.WeightedBound univ 1 1 B (A.tensorPlaneRead i g.inner) := by
    apply (hd i g.inner 1 C zero_lt_one le_rfl hC g.contMDiff hbound).mono_const
    have hh := Finset.single_le_sum (s := Finset.univ)
      (fun i _ => mul_nonneg (hD i) hC) (Finset.mem_univ i)
    change D i*C ≤ 1+∑ i : A.centers, D i*C
    linarith
  refine ⟨T,B,hT,fun H hH => (hpos H hH).1,fun H hH => (hpos H hH).2,hB,
    fun i x hx => mem_iUnion.mpr ⟨i,mem_image_of_mem _ hx⟩,
    fun i x => (hb i).norm_le (mem_univ x),?_⟩
  intro i x y
  apply Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) _ _
    (convex_univ : Convex ℝ (univ : Set SmallModes.Base)) (mem_univ x) (mem_univ y)
  · intro a _
    exact (A.tensorPlaneRead_metric_smooth g i).differentiable (by simp) a
  · intro a _
    have hh := (hb i).deriv_le zero_lt_one (le_refl 1) (mem_univ a)
    simpa only [iteratedFDerivWithin_univ,one_pow,div_one,norm_iteratedFDeriv_one] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactPositiveTensorBound
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A compact family of positive surface tensors has one quadratic lower
bound in the fixed coordinate norm. -/
noncomputable section
open Set Metric
namespace ClosedSurfaceR4.PhaseMean
open SmallModes

lemma evaluate_smul_both (H : Tensor) (c : ℝ) (v : Base) :
    evaluate H (c • v) (c • v) = c^2*evaluate H v v := by
  simp only [evaluate,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  ring

theorem compact_positive_tensor_lower_bound {T : Set Tensor} (hT : IsCompact T)
    (hpos : ∀ H ∈ T, ∀ v : Base, v ≠ 0 → 0 < evaluate H v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ H ∈ T, ∀ v : Base, c*‖v‖^2 ≤ evaluate H v v := by
  let K : Set (Tensor × Base) := T ×ˢ sphere 0 1
  have hK : IsCompact K := hT.prod (isCompact_sphere 0 1)
  have hf : Continuous (fun z : Tensor × Base => evaluate z.1 z.2 z.2) := by
    unfold evaluate
    fun_prop
  have hp : ∀ z ∈ K, 0 < evaluate z.1 z.2 z.2 := by
    rintro ⟨H,v⟩ ⟨hH,hv⟩
    apply hpos H hH v
    intro hz
    have hn : ‖v‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using hv
    rw [hz,norm_zero] at hn
    exact zero_ne_one hn
  obtain ⟨c,hc,hb⟩ := hK.exists_forall_le' hf.continuousOn hp
  refine ⟨c,hc,?_⟩
  intro H hH v
  by_cases hv : v = 0
  · simp [hv,evaluate]
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let u := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by
    simp only [u,norm_smul,Real.norm_eq_abs,abs_inv,abs_norm]
    exact inv_mul_cancel₀ hn.ne'
  have hh := hb (H,u) ⟨hH,by simpa only [mem_sphere,dist_zero_right] using hu⟩
  calc
    c*‖v‖^2 ≤ evaluate H u u*‖v‖^2 := mul_le_mul_of_nonneg_right hh (sq_nonneg _)
    _ = evaluate H v v := by
      rw [evaluate_smul_both]
      field_simp

end ClosedSurfaceR4.PhaseMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactPositiveMetricJets
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The closed family of first metric jets with a fixed positive lower
bound is compact. It therefore fixes the connection bound before any
finite-point modification or choice of disk centers. -/
noncomputable section
open Set Metric
open scoped Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes PhaseMean

lemma positiveMetricJetRegion_compact (c B : ℝ) :
    IsCompact (positiveMetricJetRegion c B) := by
  have hclosed : IsClosed {j : MetricFirstJet | ∀ v : Base, c*‖v‖^2 ≤ evaluate j.1 v v} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro v
    apply isClosed_le continuous_const
    unfold evaluate
    fun_prop
  have heq : positiveMetricJetRegion c B =
      closedBall (0 : MetricFirstJet) B ∩ {j | ∀ v : Base, c*‖v‖^2 ≤ evaluate j.1 v v} := by
    ext j
    simp only [positiveMetricJetRegion,mem_ofPred_eq,mem_inter_iff,mem_closedBall,dist_zero_right]
  rw [heq]
  exact (isCompact_closedBall _ _).inter_right hclosed

lemma positiveMetricJetRegion_det {c B : ℝ} (hc : 0 < c)
    {j : MetricFirstJet} (hj : j ∈ positiveMetricJetRegion c B) : metricJetDet j ≠ 0 := by
  have hp : ∀ v : Base, v ≠ 0 → 0 < evaluate j.1 v v := by
    intro v hv
    exact (mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hv))).trans_le (hj.2 v)
  exact ((tensor_positive_iff j.1).mp hp).2.ne'

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasMetricJetFamily
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform compact first-jet families of actual atlas metric readings.
The constants depend on a fixed lower metric bound and C1 budget. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes PhaseMean PhaseGeometry JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma tensorPlaneRead_metric_lower (g h : SmoothMetric M) (c : ℝ)
    (hlower : ∀ p v, c*g.inner p v v ≤ h.inner p v v)
    (i : A.centers) {x : SmallModes.Base}
    (hx : x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    (v : SmallModes.Base) :
    c*evaluate (A.tensorPlaneRead i g.inner x) v v ≤
      evaluate (A.tensorPlaneRead i h.inner x) v v := by
  rw [A.tensorPlaneRead_metric g i hx,A.tensorPlaneRead_metric h i hx,
    coordinateMetric_evaluate,coordinateMetric_evaluate]
  exact hlower (coordinateInverse (i : M) x)
    (mfderiv 𝓘(ℝ,SmallModes.Base) planeModel (coordinateInverse (i : M)) x v)

theorem compact_metric_jet_family (g : SmoothMetric M) {c C : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) :
    ∃ J : Set MetricFirstJet, IsCompact J ∧
      (∀ j ∈ J, metricJetDet j ≠ 0) ∧
      ∀ h : SmoothMetric M, A.TensorWeightedBound 1 1 C h.inner →
        (∀ p v, c*g.inner p v v ≤ h.inner p v v) →
        ∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
          (A.tensorPlaneRead i h.inner x,fderiv ℝ (A.tensorPlaneRead i h.inner) x) ∈ J := by
  classical
  obtain ⟨T,B,hT,hpos,hdet,_,hmem,_,_⟩ := A.metric_plane_read_bounds g
  obtain ⟨d,hd,hdlower⟩ := compact_positive_tensor_lower_bound hT (by
    intro H hH
    exact (tensor_positive_iff H).mpr ⟨hpos H hH,hdet H hH⟩)
  choose E hE hread using fun i : A.centers => A.tensorPlaneRead_bound i 1
  let R : ℝ := (∑ i, E i)*C
  let J := positiveMetricJetRegion (c*d) R
  refine ⟨J,positiveMetricJetRegion_compact _ _,
    fun j hj => positiveMetricJetRegion_det (mul_pos hc hd) hj,?_⟩
  intro h hbound hlower i x hx
  have hb := hread i h.inner 1 C zero_lt_one le_rfl hC h.contMDiff hbound
  have hEi : E i ≤ ∑ k, E k :=
    Finset.single_le_sum (fun k _ => hE k) (Finset.mem_univ i)
  have hv : ‖A.tensorPlaneRead i h.inner x‖ ≤ R :=
    (hb.norm_le (mem_univ x)).trans (mul_le_mul_of_nonneg_right hEi hC)
  have hderiv : ‖fderiv ℝ (A.tensorPlaneRead i h.inner) x‖ ≤ R := by
    have hb' := hb.deriv_le zero_lt_one (le_refl 1) (mem_univ x)
    simp only [iteratedFDerivWithin_univ,one_pow,div_one,norm_iteratedFDeriv_one] at hb'
    exact hb'.trans (mul_le_mul_of_nonneg_right hEi hC)
  refine ⟨max_le hv hderiv,?_⟩
  intro v
  calc
    (c*d)*‖v‖^2 = c*(d*‖v‖^2) := by ring
    _ ≤ c*evaluate (A.tensorPlaneRead i g.inner x) v v :=
      mul_le_mul_of_nonneg_left (hdlower _ (hmem i x hx) v) hc.le
    _ ≤ evaluate (A.tensorPlaneRead i h.inner x) v v :=
      A.tensorPlaneRead_metric_lower g h c hlower i hx v

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasMetricReadGerms
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A metric atlas reading agrees as a germ with the actual coordinate
metric when the outer cutoff is locally one. This also identifies its
first derivative, as required by the connection estimates. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReadGermFiberSpace
local instance metricReadGermDualAdd : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReadGermFiberSpace
local instance metricReadGermDualSmul_r836e2e_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricReadGermFiberNormed
local instance metricReadGermSectionNormed_r836e2e_1 (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricReadGermSectionSpace_r836e2e_1 (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorPlaneRead_metric_outer_one (g : SmoothMetric M) (i : A.centers)
    {p : M} (hp : p ∈ (chart (i : M)).source) (ho : A.outer i p = 1) :
    A.tensorPlaneRead i g.inner (coordinateChart (i : M) p) =
      coordinateMetric g (i : M) (coordinateChart (i : M) p) := by
  change A.tensorChartRead i g.inner
    (planeCoordinateIsometry.symm (planeCoordinateIsometry (chart (i : M) p))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  have hread : A.tensorChartRead i g.inner (chart (i : M) p) =
      fiberToThree (A.bundleComponent A.tensorTriv i g.inner p) := by
    change fiberToThree (localize (i : M) (A.outer i)
      (A.bundleComponent A.tensorTriv i g.inner) (chart (i : M) p)) = _
    rw [localize_chart _ _ _ hp,ho]
    simp only [one_pow,one_smul]
  rw [hread]
  ext k
  rw [fiberToThree_apply,A.tensorComponent_metric g i hp]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  fin_cases k <;> simp [evaluate,firstDirection,secondDirection,SmallModes.dx,SmallModes.dy]

lemma tensorPlaneRead_metric_germ (g : SmoothMetric M) (i : A.centers)
    {p : M} (hp : p ∈ (chart (i : M)).source)
    (ho : A.outer i =ᶠ[𝓝 p] (fun _ => (1 : ℝ))) :
    A.tensorPlaneRead i g.inner =ᶠ[𝓝 (coordinateChart (i : M) p)] coordinateMetric g (i : M) := by
  let e := coordinateChart (i : M)
  have hps : p ∈ e.source := by simpa only [e,coordinateChart_source,chart_source] using hp
  have hpt := e.map_source hps
  have ht : Tendsto e.symm (𝓝 (e p)) (𝓝 p) := by
    have hc := (e.continuousOn_symm _ hpt).continuousAt (e.open_target.mem_nhds hpt)
    simpa only [e.left_inv hps] using hc.tendsto
  filter_upwards [e.open_target.mem_nhds hpt,ho.comp_tendsto ht] with y hy hoy
  have hq : e.symm y ∈ (chart (i : M)).source := by
    simpa only [e,coordinateChart_source,chart_source] using e.map_target hy
  have he := A.tensorPlaneRead_metric_outer_one g i hq hoy
  change A.tensorPlaneRead i g.inner (e (e.symm y)) = coordinateMetric g (i : M) (e (e.symm y)) at he
  simpa only [e.right_inv hy] using he

lemma tensorPlaneRead_metric_firstJet (g : SmoothMetric M) (i : A.centers)
    {p : M} (hp : p ∈ (chart (i : M)).source)
    (ho : A.outer i =ᶠ[𝓝 p] (fun _ => (1 : ℝ))) :
    (A.tensorPlaneRead i g.inner (coordinateChart (i : M) p),
      fderiv ℝ (A.tensorPlaneRead i g.inner) (coordinateChart (i : M) p)) =
    (coordinateMetric g (i : M) (coordinateChart (i : M) p),
      fderiv ℝ (coordinateMetric g (i : M)) (coordinateChart (i : M) p)) := by
  have he := A.tensorPlaneRead_metric_germ g i hp ho
  exact Prod.ext he.eq_of_nhds he.fderiv_eq

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CenteredConvexPhase
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convex phases centered at the actual coordinate center of a circular
patch. The connection is evaluated at the original point, so translation
of the phase does not silently translate the metric. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

lemma centeredConvexPhase_hasFDerivAt (ell : Base) (L : ℝ) (c p : Base) :
    HasFDerivAt (centeredConvexPhase ell L c) (phaseLinear (ell+L • (p-c))) p := by
  have ht : HasFDerivAt (fun x : Base => x-c) (ContinuousLinearMap.id ℝ Base) p :=
    (hasFDerivAt_id p).sub_const c
  simpa only [centeredConvexPhase,Function.comp_def,ContinuousLinearMap.comp_id] using!
    (convexQuadraticPhase_hasFDerivAt ell L (p-c)).comp p ht

lemma centeredConvexPhase_coordDeriv (ell : Base) (L : ℝ) (c p v : Base) :
    coordDeriv v (centeredConvexPhase ell L c) p = phaseLinear (ell+L • (p-c)) v :=
  congrArg (fun f : Base →L[ℝ] ℝ => f v)
    (centeredConvexPhase_hasFDerivAt ell L c p).fderiv

lemma centeredConvexPhase_phaseDerivative (ell : Base) (L : ℝ) (c p : Base) :
    phaseDerivative (centeredConvexPhase ell L c) p = ell+L • (p-c) := by
  unfold phaseDerivative
  rw [(centeredConvexPhase_hasFDerivAt ell L c p).fderiv]
  ext <;> simp [phaseLinear_apply,dx,dy]

lemma centeredConvexPhase_second (ell : Base) (L : ℝ) (c p v w : Base) :
    coordDeriv v (coordDeriv w (centeredConvexPhase ell L c)) p =
      L*(v.1*w.1+v.2*w.2) := by
  have he : coordDeriv w (centeredConvexPhase ell L c) =
      fun p => phaseLinear ell w+L*phaseLinear w (p-c) := by
    funext q
    rw [centeredConvexPhase_coordDeriv]
    simp only [phaseLinear_apply,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,
      smul_eq_mul]
    ring
  have ht : HasFDerivAt (fun x : Base => x-c) (ContinuousLinearMap.id ℝ Base) p :=
    (hasFDerivAt_id p).sub_const c
  have hd : HasFDerivAt (fun x : Base => phaseLinear w (x-c)) (phaseLinear w) p := by
    simpa only [Function.comp_def,ContinuousLinearMap.comp_id] using!
      ((phaseLinear w).hasFDerivAt (x := p-c)).comp p ht
  have hh := (hasFDerivAt_const (phaseLinear ell w) p).add (hd.const_mul L)
  rw [he]
  change (fderiv ℝ ((fun _ : Base => phaseLinear ell w)+
    fun x => L*phaseLinear w (x-c)) p) v = _
  rw [hh.fderiv]
  simp only [smul_apply,smul_eq_mul,zero_add,phaseLinear_apply]
  ring

lemma centeredConvexPhase_hessian (h : Base → PhaseMean.Tensor) (ell : Base) (L : ℝ)
    (c p v w : Base) :
    coordinateMetricHessian h (centeredConvexPhase ell L c) p v w =
      L*(v.1*w.1+v.2*w.2)-phaseLinear (ell+L • (p-c))
        (connectionContract (metricConnectionAt (h p,fderiv ℝ h p)) v w) := by
  rw [coordinateMetricHessian,centeredConvexPhase_second,centeredConvexPhase_phaseDerivative]

theorem centeredConvexPhase_hessian_lower {h : Base → PhaseMean.Tensor}
    {ell c p : Base} {L B K r : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hK : ‖ell‖ ≤ K) (hp : ‖p-c‖ ≤ r)
    (hGamma : ∀ i, ‖metricConnectionAt (h p,fderiv ℝ h p) i‖ ≤ B) (v : Base) :
    (L-4*B*(K+L*r))*(v.1^2+v.2^2) ≤
      coordinateMetricHessian h (centeredConvexPhase ell L c) p v v := by
  have hg1 : |ell.1+L*(p-c).1| ≤ K+L*r := by
    calc
      _ ≤ |ell.1|+|L*(p-c).1| := abs_add_le _ _
      _ ≤ K+L*r := by
        rw [abs_mul,abs_of_nonneg hL]
        exact add_le_add ((norm_fst_le ell).trans hK)
          (mul_le_mul_of_nonneg_left ((norm_fst_le (p-c)).trans hp) hL)
  have hg2 : |ell.2+L*(p-c).2| ≤ K+L*r := by
    calc
      _ ≤ |ell.2|+|L*(p-c).2| := abs_add_le _ _
      _ ≤ K+L*r := by
        rw [abs_mul,abs_of_nonneg hL]
        exact add_le_add ((norm_snd_le ell).trans hK)
          (mul_le_mul_of_nonneg_left ((norm_snd_le (p-c)).trans hp) hL)
  obtain ⟨hc1,hc2⟩ := connectionContract_diagonal_bound hB hGamma v
  let C := connectionContract (metricConnectionAt (h p,fderiv ℝ h p)) v v
  have hdot : |phaseLinear (ell+L • (p-c)) C| ≤
      4*B*(K+L*r)*(v.1^2+v.2^2) := by
    have hk : 0 ≤ K+L*r := (abs_nonneg _).trans hg1
    calc
      _ ≤ |ell.1+L*(p-c).1| * |C.1|+|ell.2+L*(p-c).2| * |C.2| := by
        simpa only [phaseLinear_apply,Prod.fst_add,Prod.snd_add,Prod.smul_fst,
          Prod.smul_snd,smul_eq_mul,abs_mul] using
          abs_add_le ((ell.1+L*(p-c).1)*C.1) ((ell.2+L*(p-c).2)*C.2)
      _ ≤ (K+L*r)*(2*B*(v.1^2+v.2^2))+
          (K+L*r)*(2*B*(v.1^2+v.2^2)) :=
        add_le_add (mul_le_mul hg1 hc1 (abs_nonneg _) hk)
          (mul_le_mul hg2 hc2 (abs_nonneg _) hk)
      _ = _ := by ring
  rw [centeredConvexPhase_hessian]
  have hh := (le_abs_self (phaseLinear (ell+L • (p-c)) C)).trans hdot
  dsimp only [C] at hh
  nlinarith

/-- The metric-jet compact set fixes the same Hessian constants at every
center; the first metric jet is always taken at the actual point. -/
theorem compact_uniform_centered_convex_phases {J : Set MetricFirstJet}
    (hJ : IsCompact J) (hdet : ∀ j ∈ J, metricJetDet j ≠ 0)
    {K : ℝ} (hK : 0 ≤ K) :
    ∃ L r : ℝ, 0 < L ∧ 0 < r ∧
      ∀ (h : Base → PhaseMean.Tensor) (ell c p : Base), ‖ell‖ ≤ K → ‖p-c‖ ≤ r →
        (h p,fderiv ℝ h p) ∈ J → ∀ v : Base,
        (L/2)*(v.1^2+v.2^2) ≤
          coordinateMetricHessian h (centeredConvexPhase ell L c) p v v := by
  obtain ⟨B,hB,hbound⟩ := compact_metricConnection_bound hJ hdet
  let L := 16*(B+1)*(K+1)
  let r := (16*(B+1))⁻¹
  have hBp : 0 < 16*(B+1) := by positivity
  have hL : 0 < L := by dsimp [L] <;> positivity
  have hr : 0 < r := inv_pos.mpr hBp
  have hLr : L*r = K+1 := by
    dsimp [L,r]
    field_simp [hBp.ne']
  have hsmall : 4*B*(K+L*r) ≤ L/2 := by
    rw [hLr]
    dsimp [L]
    nlinarith
  refine ⟨L,r,hL,hr,fun h ell c p hell hp hj v => ?_⟩
  have hb := centeredConvexPhase_hessian_lower hL.le hB hell hp (hbound _ hj) v
  nlinarith [mul_le_mul_of_nonneg_right hsmall (add_nonneg (sq_nonneg v.1) (sq_nonneg v.2))]

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CrossAtlasTensorTransition
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual tensor transitions between independent smoothing atlases. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
open PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossTransitionDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossTransitionFiberSpace
local instance crossTransitionDualSmul_r836e2e_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A B : SmoothingAtlas M)

variable [CompactSpace M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossTransitionFiberNormed
local instance crossTransitionSectionNormed_r836e2e_1 (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance crossTransitionSectionSpace_r836e2e_1 (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma cross_pairSupport_compact (i : A.centers) (j : B.centers) :
    IsCompact (A.cross_pairSupport B i j) :=
  ((isClosed_tsupport (A.weight i)).inter (isClosed_tsupport (B.outer j))).isCompact.image_of_continuousOn
    ((chart (i : M)).continuousOn.mono (fun _ hx => A.weight_support i hx.1))

omit [CompactSpace M] in
lemma cross_pairSupport_transition (i : A.centers) (j : B.centers) :
    A.cross_pairSupport B i j ⊆ (transition (i : M) (j : M)).source := by
  rintro x ⟨p,⟨hp,hq⟩,rfl⟩
  have hp' := A.weight_support i hp
  refine ⟨(chart (i : M)).map_source hp',?_⟩
  change (chart (i : M)).symm (chart (i : M) p) ∈ (chart (j : M)).source
  rw [(chart (i : M)).left_inv hp']
  exact B.outer_support j hq

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CrossAtlasTensorBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted tensor bounds persist when the finite correction atlas changes. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base Expression)
open JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossTensorBoundDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossTensorBoundDualSmul
variable (A B : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossTensorBoundFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossTensorBoundFiberSpace
local instance crossTensorBoundSectionNormed_r836e2e_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance crossTensorBoundSectionSpace_r836e2e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma cross_tensor_localize_restore_bound (i : B.centers) (j : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (h : Base → TensorFiber) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ h →
      WeightedEstimates.WeightedBound univ s m C h →
      WeightedEstimates.WeightedBound univ s m (D*C)
        (B.bundleLocalize B.tensorTriv i (A.bundleRestore A.tensorTriv j h)) := by
  let L : Base → TensorFiber →L[ℝ] TensorFiber := fun x =>
    (A.tensorTriv j).coordChangeL ℝ (B.tensorTriv i) ((chart (i : M)).symm x)
  have hL : ContDiffOn ℝ ∞ L (transition (i : M) (j : M)).source := by
    apply ContMDiffOn.contDiffOn
    apply (contMDiffOn_coordChangeL (A.tensorTriv j) (B.tensorTriv i)).comp
      ((chart_symm_smooth (i : M)).mono (fun _ hx => hx.1))
    intro x hx
    have hj : (chart (i : M)).symm x ∈ (chart (j : M)).source := hx.2
    exact ⟨A.tensorTriv_domain j hj,B.tensorTriv_domain i ((chart (i : M)).map_target hx.1)⟩
  have heq (h : Base → TensorFiber) :
      B.bundleLocalize B.tensorTriv i (A.bundleRestore A.tensorTriv j h) =
        fun x => localize (i : M) (B.weight i) (A.outer j) x •
          L x (h (transition (i : M) (j : M) x)) := by
    funext x
    by_cases hi : x ∈ (chart (i : M)).target
    · by_cases hj : (chart (i : M)).symm x ∈ (chart (j : M)).source
      · have hbi := B.tensorTriv_domain i ((chart (i : M)).map_target hi)
        have hbj := A.tensorTriv_domain j hj
        simp only [bundleLocalize,bundleComponent,localize,indicator_of_mem hi,
          bundleRestore,map_smul]
        rw [(B.tensorTriv i).continuousLinearMapAt_apply_of_mem ℝ hbi,
          (A.tensorTriv j).symmL_apply (R := ℝ) hbj,
          ← (A.tensorTriv j).coordChangeL_apply (R := ℝ) (B.tensorTriv i) ⟨hbj,hbi⟩,smul_smul]
        rfl
      · have hz : A.outer j ((chart (i : M)).symm x) = 0 :=
          image_eq_zero_of_notMem_tsupport (fun hh => hj (A.outer_support j hh))
        simp only [bundleLocalize,bundleComponent,localize,indicator_of_mem hi,
          bundleRestore,hz,zero_smul,map_zero,smul_zero]
    · simp only [bundleLocalize,localize,indicator_of_notMem hi,zero_smul]
  obtain ⟨D,hD,hd⟩ := compact_localized_clm_composition_bound
    (transition (i : M) (j : M)).open_source (B.cross_pairSupport_compact A i j)
    (B.cross_pairSupport_transition A i j)
    (localize_smooth (i : M) (B.weight_smooth i) (B.weight_support i) (A.outer_smooth j))
    (localize_tsupport_inter (i : M) (B.weight_support i) (A.outer j))
    hL (transition_smooth (i : M) (j : M)) m
  refine ⟨D,hD,?_⟩
  intro h s C hs hs1 hC hh hb
  rw [heq]
  exact hd h s C hs hs1 hC hh hb

theorem tensorWeightedBound_change_atlas (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (u : ∀ p : M, CovariantTwoTensor p) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun p => TotalSpace.mk' TensorFiber p (u p)) →
      A.TensorWeightedBound s m C u → B.TensorWeightedBound s m (D*C) u := by
  classical
  choose D hD hd using fun (i : B.centers) (j : A.centers) =>
    A.cross_tensor_localize_restore_bound B i j m
  refine ⟨∑ i : B.centers,∑ j : A.centers,D i j,
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hD i j)),?_⟩
  intro u s C hs hs1 hC hu hb i
  have hsum := WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ hs.le
    (Finset.univ : Finset A.centers) (fun j => D i j*C)
    (fun j => B.bundleLocalize B.tensorTriv i
      (A.bundleRestore A.tensorTriv j (A.bundleLocalize A.tensorTriv j u)))
    (fun j _ => (B.bundleLocalize_smooth B.tensorTriv B.tensorTriv_domain i
      (A.bundleRestore_smooth A.tensorTriv A.tensorTriv_domain j
        (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain j hu))).contDiffOn)
    (fun j _ => hd i j _ s C hs hs1 hC
      (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain j hu) (hb j))
  have he : B.bundleLocalize B.tensorTriv i u = fun x => ∑ j : A.centers,
      B.bundleLocalize B.tensorTriv i
        (A.bundleRestore A.tensorTriv j (A.bundleLocalize A.tensorTriv j u)) x := by
    have hu' : u = (fun p => ∑ j : A.centers,
        A.bundleRestore A.tensorTriv j (A.bundleLocalize A.tensorTriv j u) p) :=
      (funext (A.bundle_sum_restore_localize A.tensorTriv A.tensorTriv_domain u)).symm
    conv_lhs => rw [hu']
    exact B.bundleLocalize_sum B.tensorTriv Finset.univ i _
  change WeightedEstimates.WeightedBound univ s m _ (B.bundleLocalize B.tensorTriv i u)
  rw [he]
  apply hsum.mono_const
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ hC
  exact Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun j _ => hD k j)) (Finset.mem_univ i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

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
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_UniformAtlasConvexPhases
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform strictly convex phases for the actual intermediate metrics.
The phase constants precede every choice of metric in the bounded family. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes PhaseMean PhaseGeometry JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem uniform_atlas_convex_phases (g : SmoothMetric M) {c C K : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1)) :
    ∃ L r : ℝ, 0 < L ∧ 0 < r ∧
      ∀ h : SmoothMetric M, A.TensorWeightedBound 1 1 C h.inner →
        (∀ p v, c*g.inner p v v ≤ h.inner p v v) →
        ∀ (i : A.centers) (p : M), p ∈ tsupport (A.weight i) →
          ‖coordinateChart (i : M) p-coordinateChart (i : M) (i : M)‖ ≤ r →
          ∀ ell : SmallModes.Base, ‖ell‖ ≤ K → ∀ v : SmallModes.Base,
            (L/2)*(v.1^2+v.2^2) ≤ coordinateMetricHessian (coordinateMetric h (i : M))
              (centeredConvexPhase ell L (coordinateChart (i : M) (i : M)))
              (coordinateChart (i : M) p) v v := by
  obtain ⟨J,hJ,hdet,hmem⟩ := A.compact_metric_jet_family g hc hC
  obtain ⟨L,r,hL,hr,hess⟩ := compact_uniform_centered_convex_phases hJ hdet hK
  refine ⟨L,r,hL,hr,?_⟩
  intro h hb hlower i p hp hsmall ell hell v
  have hx : coordinateChart (i : M) p ∈
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) := by
    exact ⟨chart (i : M) p,⟨p,hp,rfl⟩,rfl⟩
  have hj := hmem h hb hlower i _ hx
  rw [A.tensorPlaneRead_metric_firstJet h i (A.weight_support i hp) (houter i p hp)] at hj
  exact hess (coordinateMetric h (i : M)) ell _ _ hell hsmall hj v

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalUniformConvexity
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local phase convexity chosen from a fixed background norm, before the
finite circular atlas is selected. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes PhaseMean PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem local_uniform_convexity_oai (g : SmoothMetric M) {c C K : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (hK : 0 ≤ K) (p : M) :
    ∃ (L : ℝ) (U : Set M), 0 < L ∧ IsOpen U ∧ p ∈ U ∧
      U ⊆ (coordinateChart p).source ∧
      ∀ h : SmoothMetric M, A.TensorWeightedBound 1 1 C h.inner →
        (∀ q v, c*g.inner q v v ≤ h.inner q v v) →
        ∀ q ∈ U, ∀ ell : Base, ‖ell‖ ≤ K → ∀ v : Base,
          (L/2)*(v.1^2+v.2^2) ≤ coordinateMetricHessian (coordinateMetric h p)
            (centeredConvexPhase ell L (coordinateChart p p)) (coordinateChart p q) v v := by
  obtain ⟨B,i,hip,hpos,_hsupport,_hnon,houter⟩ :=
    exists_smoothingAtlas_prescribed_patch p (isCompact_singleton : IsCompact ({p} : Set M))
      (mem_singleton p) (chart p).open_source
      (singleton_subset_iff.mpr (by rw [chart_source]; exact mem_chart_source Plane p))
      (Subset.refl _)
  obtain ⟨D,hD,hchange⟩ := A.tensorWeightedBound_change_atlas B 1
  obtain ⟨L,r,hL,hr,hconvex⟩ := B.uniform_atlas_convex_phases g hc
    (mul_nonneg hD hC) hK houter
  let U : Set M := {q | 0 < B.weight i q} ∩
    ((coordinateChart p).source ∩ (coordinateChart p) ⁻¹' Metric.ball (coordinateChart p p) r)
  have hU : IsOpen U :=
    (isOpen_lt continuous_const (B.weight_smooth i).continuous).inter
      ((coordinateChart p).isOpen_inter_preimage Metric.isOpen_ball)
  have hp : p ∈ U := by
    refine ⟨hpos p (mem_singleton p),?_,?_⟩
    · rw [coordinateChart_source]; exact mem_chart_source Plane p
    · exact Metric.mem_ball_self hr
  refine ⟨L,U,hL,hU,hp,fun q hq => hq.2.1,?_⟩
  intro h hb hlower q hq ell hell v
  have hb' := hchange h.inner 1 C zero_lt_one le_rfl hC h.contMDiff hb
  have hqi : q ∈ tsupport (B.weight i) := subset_tsupport _ hq.1.ne'
  have hsmall : ‖coordinateChart (i : M) q-coordinateChart (i : M) (i : M)‖ ≤ r := by
    rw [hip]
    have hs : coordinateChart p q ∈ Metric.ball (coordinateChart p p) r := hq.2.2
    exact (by simpa only [Metric.mem_ball,dist_eq_norm] using hs :
      ‖coordinateChart p q-coordinateChart p p‖ < r).le
  have hh := hconvex h hb' hlower i q hqi hsmall ell hell v
  simpa only [hip] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.local_uniform_convexity_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.local_uniform_convexity_oai.{u_1}
