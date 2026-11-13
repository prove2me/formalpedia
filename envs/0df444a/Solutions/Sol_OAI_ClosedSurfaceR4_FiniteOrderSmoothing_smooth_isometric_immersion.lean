-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:03:42.313216+00:00
-- url     : https://prove2.me/submissions/b404f0d8-9254-4b46-9c29-dfd2c56ff0d0

import Mathlib
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Hom.Ring
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Algebra.Ring.Subring.Order
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.AddTorsor.Coord
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Convex.AmpleSet
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fin.SuccPredOrder
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.AffineSpace.Matrix
import Mathlib.LinearAlgebra.Basis.Flag
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.Filter.Ring
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Choose
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.EMetricSpace.Paracompact
import Mathlib.Topology.Germ
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Path
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.ShrinkingLemma
import Mathlib.Topology.Subpath
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UnitInterval
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI010
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_nonempty
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_isometric_immersion_of_spherical_immersion
import Theorems.Thm_OAI_ClosedSurfaceR4_PublishedInputs_whitneySurfaceInput

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ChartModel
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingConvolution
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual smoothing operators from the finite-moment kernels. They are
linear on locally integrable inputs, smooth their outputs, and fix constants. -/
noncomputable section
open scoped ContDiff Convolution

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory ContinuousLinearMap
open JetPolynomial (Base)

lemma kernel_smooth (r : ℕ) : ContDiff ℝ ∞ (kernel r) :=
  (Classical.choose_spec (exists_smoothing_kernel r)).1

lemma kernel_compact (r : ℕ) : HasCompactSupport (kernel r) :=
  (Classical.choose_spec (exists_smoothing_kernel r)).2.1

lemma kernel_mass (r : ℕ) : (∫ x, kernel r x) = 1 :=
  (Classical.choose_spec (exists_smoothing_kernel r)).2.2.1

lemma mass_dilate (K : Base → ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ x, dilate K s x) = ∫ x, K x := by
  simpa only [monomial, degree, Finset.sum_const_zero, pow_zero,
    Finset.prod_const_one, one_mul] using moment_dilate K (fun _ => 0) hs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma smooth_smooth (r : ℕ) {s : ℝ} (hs : 0 < s) {f : Base → E}
    (hf : LocallyIntegrable f volume) : ContDiff ℝ ∞ (smooth r s f) :=
  (compact_dilate (kernel_compact r) hs.ne').contDiff_convolution_left (lsmul ℝ ℝ)
    (smooth_dilate (kernel_smooth r) s) hf

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingNormBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scale-independent zeroth-order bounds for the constructed smoothing
operator, including the signed finite-moment kernels. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory
open JetPolynomial (Base)

lemma norm_dilate (K : Base → ℝ) (s : ℝ) (x : Base) :
    ‖dilate K s x‖ = dilate (fun y => ‖K y‖) s x := by
  simp only [dilate, norm_mul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (sq_nonneg s)]

lemma norm_mass_dilate (K : Base → ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ x, ‖dilate K s x‖) = ∫ x, ‖K x‖ := by
  simp_rw [norm_dilate]
  exact mass_dilate (fun x => ‖K x‖) hs

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingAtlas
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite chart data with inner and outer cutoffs for smoothing on a closed
surface. All chart and cutoff data are chosen independently of the input. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

variable [IsManifold planeModel ∞ M]

variable [T2Space M] [CompactSpace M]

/-- A compact smooth surface admits fixed finite smoothing chart data. -/
theorem exists_smoothingAtlas : Nonempty (SmoothingAtlas M) := by
  classical
  obtain ⟨t, ψ, hψ, hsupp, _, _, hsum⟩ :=
    PhaseGeometry.exists_finite_smooth_square_partition (E := Plane)
      (fun p : M => (chart p).source) (fun p => (chart p).open_source)
      (fun p => by rw [chart_source]; exact mem_chart_source Plane p)
  have hout : ∀ i : t, ∃ χ : M → ℝ,
      ContMDiff planeModel 𝓘(ℝ) ∞ χ ∧
      tsupport χ ⊆ (chart (i : M)).source ∧
      ∀ x ∈ tsupport (ψ i), χ x = 1 := by
    intro i
    have hc : IsCompact (tsupport (ψ i)) := (isClosed_tsupport _).isCompact
    obtain ⟨O, hO, hKO, hOc⟩ := hc.exists_isOpen_closure_subset
      ((chart (i : M)).open_source.mem_nhdsSet.mpr (hsupp i))
    obtain ⟨χ, hχ, _, hχs, hχone⟩ :=
      exists_contMDiff_support_eq_eq_one_iff (I := planeModel) (n := (⊤ : ℕ∞))
        hO (isClosed_tsupport (ψ i)) hKO
    refine ⟨χ, hχ, ?_, fun x hx => (hχone x).mp hx⟩
    change closure (Function.support χ) ⊆ _
    rw [hχs]
    exact hOc
  choose χ hχ hχs hχone using hout
  exact ⟨⟨t, ψ, χ, hψ, hsupp, hχ, hχs, hχone, hsum⟩⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldSmoothing
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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

omit [IsManifold planeModel ∞ M] in
lemma restore_sub (p : M) (χ : M → ℝ) (h k : Base → V) :
    restore p χ (h - k) = restore p χ h - restore p χ k := by
  funext x
  by_cases hx : x ∈ (chart p).source <;>
    simp [restore, hx, smul_sub]

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingTransition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate transitions that transport each localized smoothing error. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

variable [CompactSpace M]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [CompactSpace M] in
/-- Writing a restored component in another chart is multiplication by a
fixed smooth weight followed by the fixed transition. -/
lemma localize_restore (i j : A.centers) (h : Base → V) :
    localize (i : M) (A.weight i) (restore (j : M) (A.outer j) h) =
      fun x => A.pairWeight i j x • h (transition (i : M) (j : M) x) := by
  funext x
  by_cases hi : x ∈ (chart (i : M)).target
  · by_cases hj : (chart (i : M)).symm x ∈ (chart (j : M)).source
    · simp only [localize, restore, pairWeight, indicator_of_mem hi, indicator_of_mem hj]
      rw [smul_smul]
      rfl
    · have hz : A.outer j ((chart (i : M)).symm x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hp => hj (A.outer_support j hp))
      simp only [localize, restore, pairWeight, indicator_of_mem hi, indicator_of_notMem hj,
        hz, smul_zero, zero_smul]
  · simp only [localize, pairWeight, indicator_of_notMem hi, zero_smul]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasWeightedBounds
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_SphericalLift
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The spherical lift of an ordinary surface immersion

Inverse stereographic projection lifts a smooth immersion into three-space
to a smooth spherical immersion in four-space, as in Section 8.1 of paper 094-01.
-/

noncomputable section

namespace ClosedSurfaceR4.SphericalStart

open Set Manifold
open scoped ContDiff Topology InnerProductSpace

lemma lift_smooth (v : Space) : ContDiff ℝ ∞ (lift v) :=
  contDiff_stereoInvFunAux.comp (ℝ ∙ v)ᗮ.subtypeL.contDiff

lemma lift_norm {v : Space} (hv : ‖v‖ = 1) (w : Hyperplane v) :
    ‖lift v w‖ = 1 := by
  exact mem_sphere_zero_iff_norm.mp (stereoInvFunAux_mem hv w.property)

lemma lift_inner_lt_one {v : Space} (hv : ‖v‖ = 1) (w : Hyperplane v) :
    inner ℝ v (lift v w) < 1 := by
  apply (inner_lt_one_iff_real_of_norm_eq_one hv (lift_norm hv w)).mpr
  exact (Subtype.coe_ne_coe.mpr (stereoInvFun_ne_north_pole hv w)).symm

/-- Its differential is injective everywhere because stereographic projection
is a smooth left inverse on its image. -/
theorem lift_fderiv_injective {v : Space} (hv : ‖v‖ = 1) (w : Hyperplane v) :
    Function.Injective (fderiv ℝ (lift v) w) := by
  let U : Set Space := {x | inner ℝ v x ≠ 1}
  have hU : IsOpen U := isOpen_ne_fun (innerSL ℝ v).continuous continuous_const
  have hw : lift v w ∈ U := ne_of_lt (lift_inner_lt_one hv w)
  have hd : DifferentiableAt ℝ (stereoToFun v) (lift v w) := by
    exact ((contDiffOn_stereoToFun (v := v) (n := (1 : ℕ∞ω))).contDiffAt
      (hU.mem_nhds hw)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hl := (lift_smooth v).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) w
  have he : stereoToFun v ∘ lift v = id := by
    funext z
    exact stereo_right_inv hv z
  have hchain : (fderiv ℝ (stereoToFun v) (lift v w)).comp
      (fderiv ℝ (lift v) w) = ContinuousLinearMap.id ℝ (Hyperplane v) := by
    rw [← fderiv_comp w hd hl, he, fderiv_id]
  intro a b hab
  have hab' := congrArg (fderiv ℝ (stereoToFun v) (lift v w)) hab
  change ((fderiv ℝ (stereoToFun v) (lift v w)).comp
    (fderiv ℝ (lift v) w)) a = ((fderiv ℝ (stereoToFun v) (lift v w)).comp
    (fderiv ℝ (lift v) w)) b at hab'
  simpa only [hchain, ContinuousLinearMap.id_apply] using hab'

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ M]

omit [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ M] in
/-- A smooth ordinary immersion into the three-dimensional hyperplane gives
an ambient smooth immersion with image in the unit three-sphere. -/
theorem spherical_immersion_of_hyperplane_immersion {v : Space} (hv : ‖v‖ = 1)
    {F : M → Hyperplane v}
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, Hyperplane v) ∞ F)
    (hI : ∀ p, Function.Injective
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, Hyperplane v) F p)) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, Space) ∞ (lift v ∘ F) ∧
      (∀ p, ‖lift v (F p)‖ = 1) ∧
      ∀ p, Function.Injective
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, Space) (lift v ∘ F) p) := by
  have hl := (lift_smooth v).contMDiff
  refine ⟨hl.comp hF, fun p => lift_norm hv (F p), ?_⟩
  intro p
  rw [mfderiv_comp p (hl.mdifferentiable (by simp)).mdifferentiableAt
    (hF.mdifferentiable (by simp)).mdifferentiableAt, mfderiv_eq_fderiv]
  exact (lift_fderiv_injective hv (F p)).comp (hI p)

omit [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ M] in
/-- The ordinary smooth three-space immersion supplied at the starting step
can be placed in the unit three-sphere. -/
theorem spherical_immersion_of_three_space_immersion {v : Space} (hv : ‖v‖ = 1)
    {F : M → ThreeSpace}
    (hF : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ThreeSpace) ∞ F)
    (hI : ∀ p, Function.Injective
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ThreeSpace) F p)) :
    ∃ G : M → Space,
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, Space) ∞ G ∧
      (∀ p, ‖G p‖ = 1) ∧
      ∀ p, Function.Injective
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, Space) G p) := by
  have hv0 : v ≠ 0 := by
    intro he
    rw [he, norm_zero] at hv
    norm_num at hv
  let e := threeSpaceToHyperplane hv0
  have he : ContDiff ℝ ∞ e := e.toContinuousLinearEquiv.contDiff
  have hi : ∀ p, Function.Injective
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, Hyperplane v) (e ∘ F) p) := by
    intro p
    rw [mfderiv_comp p (he.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
      (hF.mdifferentiable (by simp)).mdifferentiableAt, mfderiv_eq_fderiv]
    let D : EuclideanSpace ℝ (Fin 2) →L[ℝ] ThreeSpace :=
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ThreeSpace) F p
    change Function.Injective ((fderiv ℝ e (F p)).comp D)
    have hde : fderiv ℝ e (F p) = e.toContinuousLinearEquiv.toContinuousLinearMap :=
      e.toContinuousLinearEquiv.hasFDerivAt.fderiv
    rw [hde]
    exact e.injective.comp (hI p)
  exact ⟨lift v ∘ (e ∘ F),
    spherical_immersion_of_hyperplane_immersion hv (he.contMDiff.comp hF) hi⟩

end ClosedSurfaceR4.SphericalStart

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SphericalMetricPhaseData
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A smooth three-space immersion supplies the actual starting phase geometry. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Matrix

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes RealModes

private lemma inner_spaceCoordinates_symm (X Y : RVec 4) :
    inner ℝ (spaceCoordinates.symm X) (spaceCoordinates.symm Y) = X ⬝ᵥ Y := by
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using
    (spaceCoordinates_dot (spaceCoordinates.symm X) (spaceCoordinates.symm Y)).symm

private lemma fderiv_realDot_apply {F G : RField 4} {x : Base}
    (hF : DifferentiableAt ℝ F x) (hG : DifferentiableAt ℝ G x) (v : Base) :
    fderiv ℝ (fun y => F y ⬝ᵥ G y) x v =
      F x ⬝ᵥ (fderiv ℝ G x v)+(fderiv ℝ F x v) ⬝ᵥ G x := by
  have hF' := spaceCoordinates.symm.hasFDerivAt.comp x hF.hasFDerivAt
  have hG' := spaceCoordinates.symm.hasFDerivAt.comp x hG.hasFDerivAt
  have hd := fderiv_inner_apply ℝ hF'.differentiableAt hG'.differentiableAt v
  have he : (fun y => inner ℝ (spaceCoordinates.symm (F y)) (spaceCoordinates.symm (G y))) =
      (fun y => F y ⬝ᵥ G y) := funext fun y => inner_spaceCoordinates_symm (F y) (G y)
  simp only [Function.comp_apply] at hd
  rw [he,hF'.fderiv,hG'.fderiv] at hd
  change fderiv ℝ (fun y => F y ⬝ᵥ G y) x v =
    inner ℝ (spaceCoordinates.symm (F x)) (spaceCoordinates.symm (fderiv ℝ G x v))+
      inner ℝ (spaceCoordinates.symm (fderiv ℝ F x v)) (spaceCoordinates.symm (G x)) at hd
  simpa only [inner_spaceCoordinates_symm] using hd

private lemma sphere_real_radial_first {F : RField 4} {x : Base}
    (hF : DifferentiableAt ℝ F x) (hunit : ∀ y, F y ⬝ᵥ F y = 1) (v : Base) :
    F x ⬝ᵥ coordDeriv v F x = 0 := by
  have he : (fun y => F y ⬝ᵥ F y) = (fun _ => (1 : ℝ)) := funext hunit
  have hd := congrArg (fun L : Base →L[ℝ] ℝ => L v)
    (congrArg (fun f : Base → ℝ => fderiv ℝ f x) he)
  rw [fderiv_realDot_apply hF hF] at hd
  simp only [fderiv_const_apply,zero_apply] at hd
  rw [dotProduct_comm (fderiv ℝ F x v) (F x)] at hd
  change F x ⬝ᵥ fderiv ℝ F x v = 0
  linarith

private lemma sphere_real_radial_second {F : RField 4} {U : Set Base}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hunit : ∀ y, F y ⬝ᵥ F y = 1) {x : Base} (hx : x ∈ U) (v w : Base) :
    F x ⬝ᵥ coordDeriv v (coordDeriv w F) x =
      -(coordDeriv v F x ⬝ᵥ coordDeriv w F x) := by
  have hFx := (hF x hx).contDiffAt (hU.mem_nhds hx)
  have he : (fun y => F y ⬝ᵥ coordDeriv w F y) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact sphere_real_radial_first
      (((hF y hy).contDiffAt (hU.mem_nhds hy)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hunit w
  have hd := congrArg (fun L : Base →L[ℝ] ℝ => L v) he.fderiv_eq
  rw [fderiv_realDot_apply (hFx.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    ((contDiffAt_coordDeriv hFx w).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))] at hd
  simp only [fderiv_const_apply,zero_apply] at hd
  change F x ⬝ᵥ fderiv ℝ (coordDeriv w F) x v =
    -(fderiv ℝ F x v ⬝ᵥ coordDeriv w F x)
  change F x ⬝ᵥ fderiv ℝ (coordDeriv w F) x v+
    fderiv ℝ F x v ⬝ᵥ coordDeriv w F x = 0 at hd
  linarith

/-- The inward radial pairing of the coordinate second form is the induced
metric, even though the coordinate representative is only smooth on its chart. -/
lemma sphere_realSecondForm_inward {F : RField 4} {U : Set Base}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hunit : ∀ y, F y ⬝ᵥ F y = 1) {x : Base} (hx : x ∈ U) (v w : Base) :
    realSecondForm F v w x ⬝ᵥ (-F x) =
      coordDeriv v F x ⬝ᵥ coordDeriv w F x := by
  have hFx := ((hF x hx).contDiffAt (hU.mem_nhds hx)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hX : coordDeriv dx F x ⬝ᵥ (-F x) = 0 := by
    rw [dotProduct_neg,dotProduct_comm,sphere_real_radial_first hFx hunit,neg_zero]
  have hY : coordDeriv dy F x ⬝ᵥ (-F x) = 0 := by
    rw [dotProduct_neg,dotProduct_comm,sphere_real_radial_first hFx hunit,neg_zero]
  unfold realSecondForm realNormalPart
  simp only [sub_dotProduct,smul_dotProduct,smul_eq_mul,hX,hY,mul_zero,sub_zero]
  rw [dotProduct_neg,dotProduct_comm,sphere_real_radial_second hU hF hunit hx,neg_neg]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

/-- A spherical immersion has nonzero second fundamental form in every
coordinate chart, with the first coordinate direction as an explicit witness. -/
theorem spherical_coordinate_second_nonzero {G : M → Space}
    (hG : ContMDiff planeModel spaceModel ∞ G) (hunit : ∀ p, ‖G p‖ = 1)
    (hI : ∀ p, Function.Injective (mfderiv planeModel spaceModel G p)) (p : M) :
    ∃ v w : Base, realSecondForm (coordinateMap G p) v w (coordinateCenter p) ≠ 0 := by
  have hcoords : ∀ x, coordinateMap G p x ⬝ᵥ coordinateMap G p x = 1 := by
    intro x
    dsimp only [coordinateMap,Function.comp_apply]
    rw [spaceCoordinates_dot,real_inner_self_eq_norm_sq,hunit]
    norm_num
  have hdir : coordDeriv dx (coordinateMap G p) (coordinateCenter p) ≠ 0 := by
    intro hz
    change fderiv ℝ (coordinateMap G p) (coordinateCenter p) dx = 0 at hz
    have hi := coordinateMap_immersion_center hG p (hI p)
    have he : dx = (0 : Base) := hi (by simpa only [map_zero] using hz)
    simp [dx] at he
  have hnorm : 0 < coordDeriv dx (coordinateMap G p) (coordinateCenter p) ⬝ᵥ
      coordDeriv dx (coordinateMap G p) (coordinateCenter p) := by
    have hn : 0 ≤ coordDeriv dx (coordinateMap G p) (coordinateCenter p) ⬝ᵥ
        coordDeriv dx (coordinateMap G p) (coordinateCenter p) :=
      Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    exact hn.lt_of_ne' ((dotProduct_self_eq_zero).not.mpr hdir)
  refine ⟨dx,dx,?_⟩
  intro hz
  have hh := sphere_realSecondForm_inward (coordinateDomain_open p)
    (coordinateMap_smoothOn hG p) hcoords (coordinateCenter_mem p) dx dx
  rw [hz,zero_dotProduct] at hh
  linarith

variable [T2Space M] [CompactSpace M]

/-- A given smooth immersion into three-space yields a spherical immersion
and all the concrete phase geometry for any smooth target metric. -/
theorem metricPhaseData_of_three_space_immersion
    (g : SmoothMetric M) {F : M → SphericalStart.ThreeSpace}
    (hF : ContMDiff planeModel 𝓘(ℝ,SphericalStart.ThreeSpace) ∞ F)
    (hI : ∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ,SphericalStart.ThreeSpace) F p)) :
    ∃ G : M → Space, ContMDiff planeModel spaceModel ∞ G ∧
      (∀ p, ‖G p‖ = 1) ∧
      (∀ p, Function.Injective (mfderiv planeModel spaceModel G p)) ∧
      Nonempty (MetricGoodPhaseData g G) := by
  let v : Space := EuclideanSpace.single 0 1
  have hv : ‖v‖ = 1 := by simp [v]
  obtain ⟨G,hG,hu,hi⟩ := SphericalStart.spherical_immersion_of_three_space_immersion hv hF hI
  exact ⟨G,hG,hu,hi,MetricGoodPhaseData.nonempty g hG hi
    (spherical_coordinate_second_nonzero hG hu hi)⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingC1Approximation
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform approximation of C1 coordinate maps by the existing smooth kernel. -/
noncomputable section
open scoped ContDiff Convolution Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open MeasureTheory Set Filter ContinuousLinearMap
open JetPolynomial (Base)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma fderiv_smooth_C1 (r : ℕ) {s : ℝ} (hs : 0 < s) {f : Base → E}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (x : Base) :
    fderiv ℝ (smooth r s f) x = smooth r s (fderiv ℝ f) x := by
  let L : ℝ →L[ℝ] E →L[ℝ] E := lsmul ℝ ℝ
  have hk : LocallyIntegrable (dilate (kernel r) s) volume :=
    (((smooth_dilate (kernel_smooth r) s).continuous).integrable_of_hasCompactSupport
      (compact_dilate (kernel_compact r) hs.ne')).locallyIntegrable
  have h := hfc.hasFDerivAt_convolution_right L hk hf x
  have heq : ((dilate (kernel r) s) ⋆[L.precompR Base, volume] fderiv ℝ f) x =
      smooth r s (fderiv ℝ f) x := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun y => by ext v; rfl)
  exact h.fderiv.trans heq

/-- Uniform continuity suffices for uniform convergence of the signed
finite-moment kernel. Positivity of the kernel is not required. -/
theorem smooth_uniform_approximation (r : ℕ) {f : Base → E}
    (hf : UniformContinuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 0 < s → s < η →
      ∀ x : Base, ‖smooth r s f x-f x‖ ≤ ε := by
  let C : ℝ := ∫ y, ‖kernel r y‖
  have hC : 0 ≤ C := integral_nonneg (fun _ => norm_nonneg _)
  have ha : 0 < ε/(C+1) := div_pos hε (by linarith)
  obtain ⟨δ,hδ,hδf⟩ := Metric.uniformContinuous_iff.mp hf (ε/(C+1)) ha
  obtain ⟨R,hR,hRK⟩ := (kernel_compact r).isCompact.isBounded.exists_pos_norm_le
  refine ⟨δ/(R+1),div_pos hδ (by linarith),?_⟩
  intro s hs hsη x
  let k := dilate (kernel r) s
  have hk : HasCompactSupport k := compact_dilate (kernel_compact r) hs.ne'
  have hkc : Continuous k := (smooth_dilate (kernel_smooth r) s).continuous
  have hki : Integrable k volume := hkc.integrable_of_hasCompactSupport hk
  have hloc : LocallyIntegrable f volume := hf.continuous.locallyIntegrable
  have hif := hk.convolutionExists_left (lsmul ℝ ℝ) hkc hloc x
  have hif' : Integrable (fun y => k y • f (x-y)) volume := hif
  have heq : smooth r s f x-f x = ∫ y, k y • (f (x-y)-f x) := by
    symm
    simp_rw [smul_sub]
    rw [integral_sub hif' (hki.smul_const (f x)),integral_smul_const]
    change smooth r s f x-(∫ y, dilate (kernel r) s y) • f x = _
    rw [mass_dilate _ hs,kernel_mass,one_smul]
  have hbound (y : Base) : ‖k y • (f (x-y)-f x)‖ ≤ ‖k y‖*(ε/(C+1)) := by
    by_cases hy : k y = 0
    · simp [hy]
    have hyn : kernel r (s⁻¹ • y) ≠ 0 := (mul_ne_zero_iff.mp hy).2
    have hyR := hRK (s⁻¹ • y) (subset_tsupport _ hyn)
    have hn : ‖y‖ ≤ R*s := by
      rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hs] at hyR
      have hh : ‖y‖/s ≤ R := by simpa only [div_eq_mul_inv,mul_comm] using hyR
      exact (div_le_iff₀ hs).mp hh
    have hsR : R*s < δ := by
      have hh := (lt_div_iff₀ (show 0 < R+1 by linarith)).mp hsη
      nlinarith
    have hd : dist (x-y) x < δ := by
      simpa only [dist_eq_norm,sub_sub_cancel_left,norm_neg] using hn.trans_lt hsR
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (le_of_lt (by
      simpa only [dist_eq_norm] using hδf hd)) (norm_nonneg _)
  rw [heq]
  calc
    ‖∫ y, k y • (f (x-y)-f x)‖ ≤ ∫ y, ‖k y‖*(ε/(C+1)) :=
      norm_integral_le_of_norm_le (hki.norm.mul_const _) (Eventually.of_forall hbound)
    _ = C*(ε/(C+1)) := by rw [integral_mul_const,norm_mass_dilate _ hs]
    _ ≤ ε := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (show 0 < C+1 by linarith)).mpr
      nlinarith

/-- Compactly supported C1 maps have smooth approximants converging uniformly
both as maps and in their first derivatives. -/
theorem smooth_C1_approximation (r : ℕ) {f : Base → E}
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 0 < s → s < η →
      ContDiff ℝ ∞ (smooth r s f) ∧
      ∀ x, ‖smooth r s f x-f x‖ ≤ ε ∧
        ‖fderiv ℝ (smooth r s f) x-fderiv ℝ f x‖ ≤ ε := by
  have hu := hfc.uniformContinuous_of_continuous hf.continuous
  have hd : UniformContinuous (fderiv ℝ f) :=
    (hfc.fderiv ℝ).uniformContinuous_of_continuous (hf.continuous_fderiv one_ne_zero)
  obtain ⟨η₁,hη₁,h₁⟩ := smooth_uniform_approximation r hu hε
  obtain ⟨η₂,hη₂,h₂⟩ := smooth_uniform_approximation r hd hε
  refine ⟨min η₁ η₂,lt_min hη₁ hη₂,?_⟩
  intro s hs hsη
  refine ⟨smooth_smooth r hs hf.continuous.locallyIntegrable,?_⟩
  intro x
  refine ⟨h₁ s hs (hsη.trans_le (min_le_left _ _)) x,?_⟩
  rw [fderiv_smooth_C1 r hs hf hfc]
  exact h₂ s hs (hsη.trans_le (min_le_right _ _)) x

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_C1LocalizedComposition
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First-derivative bounds for localization of C1 inputs. -/
noncomputable section
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Filter WeightedEstimates
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma localizedComposition_C1 {O : Set Base} (hO : IsOpen O)
    {χ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ O)
    {T : Base → Base} (hT : ContDiffOn ℝ ∞ T O)
    {f : Base → V} (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (fun x => χ x • f (T x)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · have ht : ContDiffAt ℝ 1 T x :=
      (hT.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hO.mem_nhds (hs hx))
    exact (hχ.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt.smul (hf.contDiffAt.comp x ht)
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp only [Pi.zero_apply] at hy
    rw [hy,zero_smul]

/-- Localization by a fixed chart change is bounded in C1 even when the
input is only C1. This applies to smoothing errors of a Whitney immersion. -/
theorem compact_localized_C1_bound {O K : Set Base}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {χ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχK : tsupport χ ⊆ K)
    {T : Base → Base} (hT : ContDiffOn ℝ ∞ T O) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : Base → V) (C : ℝ), 0 ≤ C →
      ContDiff ℝ 1 f → (∀ x, ‖f x‖ ≤ C ∧ ‖fderiv ℝ f x‖ ≤ C) →
      ∀ x, ‖χ x • f (T x)‖ ≤ D*C ∧
        ‖fderiv ℝ (fun y => χ y • f (T y)) x‖ ≤ D*C := by
  obtain ⟨A,hA,hAb⟩ := compact_coefficient_bound hO.uniqueDiffOn hK hKO hχ.contDiffOn 1
  obtain ⟨B,hB,hBb⟩ := compact_coefficient_bound hO.uniqueDiffOn hK hKO hT 1
  refine ⟨A+A*B,by positivity,?_⟩
  intro f C hC hf hb x
  by_cases hx : x ∈ tsupport χ
  · have hxO := hKO (hχK hx)
    have hAx : ‖χ x‖ ≤ A := by
      simpa only [norm_iteratedFDerivWithin_zero] using hAb 0 (by omega) x (hχK hx)
    have hA' : ‖fderiv ℝ χ x‖ ≤ A := by
      have hh := hAb 1 le_rfl x (hχK hx)
      rw [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn
        ((hχ.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt) hxO] at hh
      simpa only [norm_iteratedFDeriv_one] using hh
    have ht := (hT.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≤ ∞)).contDiffAt (hO.mem_nhds hxO)
    have hB' : ‖fderiv ℝ T x‖ ≤ B := by
      have hh := hBb 1 le_rfl x (hχK hx)
      rw [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn ht hxO] at hh
      simpa only [norm_iteratedFDeriv_one] using hh
    refine ⟨?_,?_⟩
    · calc
        ‖χ x • f (T x)‖ = ‖χ x‖*‖f (T x)‖ := norm_smul _ _
        _ ≤ A*C := mul_le_mul hAx (hb _).1 (norm_nonneg _) (by linarith)
        _ ≤ (A+A*B)*C := by nlinarith [mul_nonneg (mul_nonneg (by linarith : 0 ≤ A) (by linarith : 0 ≤ B)) hC]
    · have htc := (hf.differentiable one_ne_zero (T x)).comp x
        (ht.differentiableAt one_ne_zero)
      rw [fderiv_fun_smul (f := fun y => f (T y)) (hχ.differentiable (by simp) x) htc]
      change ‖χ x • fderiv ℝ (f ∘ T) x + (fderiv ℝ χ x).smulRight (f (T x))‖ ≤ _
      rw [fderiv_comp x (hf.differentiable one_ne_zero (T x)) (ht.differentiableAt one_ne_zero)]
      calc
        _ ≤ ‖χ x • ((fderiv ℝ f (T x)).comp (fderiv ℝ T x))‖+
            ‖(fderiv ℝ χ x).smulRight (f (T x))‖ := norm_add_le _ _
        _ ≤ ‖χ x‖*(‖fderiv ℝ f (T x)‖*‖fderiv ℝ T x‖)+‖fderiv ℝ χ x‖*‖f (T x)‖ := by
          rw [norm_smul,ContinuousLinearMap.norm_smulRight_apply]
          exact add_le_add (mul_le_mul_of_nonneg_left
            (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)) le_rfl
        _ ≤ A*(C*B)+A*C := by gcongr; exact (hb _).2; exact (hb _).1
        _ = (A+A*B)*C := by ring
  · have hz := notMem_tsupport_iff_eventuallyEq.mp hx
    have heq : (fun y => χ y • f (T y)) =ᶠ[𝓝 x] (fun _ => (0 : V)) := by
      filter_upwards [hz] with y hy
      simp only [Pi.zero_apply] at hy
      rw [hy,zero_smul]
    have hval : χ x • f (T x) = 0 := heq.self_of_nhds
    have hd : fderiv ℝ (fun y => χ y • f (T y)) x = 0 := by
      rw [heq.fderiv_eq]
      exact fderiv_const_apply (0 : V)
    rw [hval,hd,norm_zero,norm_zero]
    constructor <;> positivity

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_C1ManifoldSmoothing
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothing C1 maps on the fixed finite surface atlas. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma localize_C1 (p : M) {ψ : M → ℝ} (hψ : ContMDiff planeModel 𝓘(ℝ) ∞ ψ)
    (hsupp : tsupport ψ ⊆ (chart p).source) {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ, V) 1 f) : ContDiff ℝ 1 (localize p ψ f) := by
  have hchart := (chart_symm_smooth p).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top : (1 : ℕ∞ω) ≤ ∞)
  have hlocal : ContDiffOn ℝ 1
      (fun x => (ψ ((chart p).symm x)) ^ 2 • f ((chart p).symm x)) (chart p).target :=
    ((((hψ.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp_contMDiffOn hchart).pow 2).smul
      (hf.comp_contMDiffOn hchart)).contDiffOn
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport (localize p ψ f)
  · obtain ⟨y,hy,hxy⟩ := localize_tsupport p hsupp f hx
    have hxT : x ∈ (chart p).target := hxy ▸ (chart p).map_source (hsupp hy)
    apply (hlocal.contDiffAt ((chart p).open_target.mem_nhds hxT)).congr_of_eventuallyEq
    filter_upwards [(chart p).open_target.mem_nhds hxT] with z hz
    exact indicator_of_mem hz _
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hx)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- The already defined first-order finite smoother is smooth even when its
input map has only one derivative. -/
lemma smooth_C1_input {s : ℝ} (hs : 0 < s) {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ, V) 1 f) :
    ContMDiff planeModel 𝓘(ℝ, V) ∞ (A.smooth 1 s f) := by
  have heq : A.smooth 1 s f = fun x => ∑ i : A.centers,
      restore (i : M) (A.outer i) (finiteSmooth 1 s (localize (i : M) (A.weight i) f)) x := by
    funext x
    simp only [smooth,Finset.sum_apply]
  rw [heq]
  apply ContMDiff.sum
  intro i _
  apply restore_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
  have hi := localize_C1 (i : M) (A.weight_smooth i) (A.weight_support i) hf
  simpa only [finiteSmooth,Finset.sum_range_one,residual] using
    (FiniteOrderSmoothing.smooth_smooth 0 hs hi.continuous.locallyIntegrable)

theorem restoration_C1_bound :
    ∃ D : ℝ, 0 < D ∧ ∀ (h : A.centers → Base → V) (C : ℝ), 0 ≤ C →
      (∀ i, ContDiff ℝ 1 (h i)) →
      (∀ i x, ‖h i x‖ ≤ C ∧ ‖fderiv ℝ (h i) x‖ ≤ C) →
      A.C1Bound (D*C) (∑ i : A.centers, restore (i : M) (A.outer i) (h i)) := by
  classical
  choose D hD hb using fun i j : A.centers => compact_localized_C1_bound (V := V)
    (transition (i : M) (j : M)).open_source (A.pairSupport_compact i j)
    (A.pairSupport_transition i j) (A.pairWeight_smooth i j) (A.pairWeight_support i j)
    (transition_smooth (i : M) (j : M))
  let S := ∑ i : A.centers, ∑ j : A.centers, D i j
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hD i j))
  refine ⟨1+S,by linarith,?_⟩
  intro h C hC hh hnorm i x
  let H : A.centers → Base → V := fun j =>
    localize (i : M) (A.weight i) (restore (j : M) (A.outer j) (h j))
  have hH (j : A.centers) : ContDiff ℝ 1 (H j) := by
    dsimp [H]
    rw [A.localize_restore]
    exact localizedComposition_C1 (transition (i : M) (j : M)).open_source
      (A.pairWeight_smooth i j) ((A.pairWeight_support i j).trans (A.pairSupport_transition i j))
      (transition_smooth (i : M) (j : M)) (hh j)
  have hHb (j : A.centers) : ‖H j x‖ ≤ D i j*C ∧ ‖fderiv ℝ (H j) x‖ ≤ D i j*C := by
    dsimp [H]
    rw [A.localize_restore]
    exact hb i j (h j) C hC (hh j) (hnorm j) x
  have hsum : (∑ j : A.centers, D i j)*C ≤ (1+S)*C := by
    apply mul_le_mul_of_nonneg_right _ hC
    have ht : (∑ j : A.centers, D i j) ≤ S :=
      Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun j _ => hD k j)) (Finset.mem_univ i)
    linarith
  change ‖localize (i : M) (A.weight i) (∑ j : A.centers, restore (j : M) (A.outer j) (h j)) x‖ ≤ _ ∧ _
  rw [localize_sum]
  constructor
  · exact ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => (hHb j).1))).trans
      (by simpa only [Finset.sum_mul] using hsum)
  · rw [fderiv_fun_sum (fun j _ => (hH j).differentiable one_ne_zero x)]
    exact ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => (hHb j).2))).trans
      (by simpa only [Finset.sum_mul] using hsum)

variable [CompleteSpace V]

/-- The fixed atlas smoother converges in C1 for C1 input maps. -/
theorem smooth_C1_approximation {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ,V) 1 f) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ s : ℝ, 0 < s → s < η →
      ContMDiff planeModel 𝓘(ℝ,V) ∞ (A.smooth 1 s f) ∧
      A.C1Bound ε (A.smooth 1 s f-f) := by
  classical
  obtain ⟨D,hD,hrestore⟩ := A.restoration_C1_bound (V := V)
  let l : A.centers → Base → V := fun i => localize (i : M) (A.weight i) f
  have hl (i : A.centers) : ContDiff ℝ 1 (l i) :=
    localize_C1 (i : M) (A.weight_smooth i) (A.weight_support i) hf
  have hlc (i : A.centers) : HasCompactSupport (l i) :=
    localize_compact (i : M) (A.weight_support i) f
  choose η hη hb using fun i : A.centers =>
    FiniteOrderSmoothing.smooth_C1_approximation 0 (hl i) (hlc i) (div_pos hε hD)
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ i : A.centers, s < η i :=
    Filter.eventually_all.mpr (fun i => gt_mem_nhds (hη i))
  obtain ⟨r,hr,hrb⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨r,hr,?_⟩
  intro s hs hsr
  have hsi (i : A.centers) : s < η i :=
    hrb (by simpa only [Real.dist_eq,sub_zero,abs_of_pos hs] using hsr) i
  let e : A.centers → Base → V := fun i => FiniteOrderSmoothing.smooth 0 s (l i)-l i
  have he (i : A.centers) : ContDiff ℝ 1 (e i) :=
    ((hb i s hs (hsi i)).1.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).sub (hl i)
  have heb (i : A.centers) (x : Base) :
      ‖e i x‖ ≤ ε/D ∧ ‖fderiv ℝ (e i) x‖ ≤ ε/D := by
    have hh := (hb i s hs (hsi i)).2 x
    refine ⟨hh.1,?_⟩
    change ‖fderiv ℝ (FiniteOrderSmoothing.smooth 0 s (l i)-l i) x‖ ≤ _
    rw [fderiv_sub ((hb i s hs (hsi i)).1.differentiable (by simp) x)
      ((hl i).differentiable one_ne_zero x)]
    exact hh.2
  have hsum := hrestore e (ε/D) (div_nonneg hε.le hD.le) he heb
  have heq : (∑ i : A.centers, restore (i : M) (A.outer i) (e i)) = A.smooth 1 s f-f := by
    simp only [e,restore_sub,Finset.sum_sub_distrib]
    change (∑ i : A.centers, restore (i : M) (A.outer i)
      (FiniteOrderSmoothing.smooth 0 s (l i))) -
      (∑ i : A.centers, restore (i : M) (A.outer i)
        (localize (i : M) (A.weight i) f)) = _
    rw [A.sum_restore_localize]
    congr 1
    simp only [l,smooth,finiteSmooth,Finset.sum_range_one,residual]
  refine ⟨A.smooth_C1_input hs hf,?_⟩
  rw [heq] at hsum
  simpa only [mul_div_cancel₀ _ hD.ne'] using hsum

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_C1ImmersionJets
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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

lemma continuous_weightedJet {w : Base → ℝ} {l : Base → V}
    (hw : ContDiff ℝ 1 w) (hl : ContDiff ℝ 1 l) : Continuous (weightedJet w l) := by
  exact (hw.continuous.smul (hl.continuous_fderiv one_ne_zero)).sub
    ((ContinuousLinearMap.smulRightL ℝ Base V).continuous₂.comp
      ((hw.continuous_fderiv one_ne_zero).prodMk hl.continuous))

lemma weightedJet_eq_smul {w : Base → ℝ} {l h : Base → V} {x : Base}
    (hw : DifferentiableAt ℝ w x) (hh : DifferentiableAt ℝ h x)
    (he : l =ᶠ[𝓝 x] fun y => w y • h y) :
    weightedJet w l x = (w x)^2 • fderiv ℝ h x := by
  unfold weightedJet
  rw [he.fderiv_eq, fderiv_fun_smul hw hh, he.self_of_nhds]
  ext v
  simp only [sub_apply,smul_apply,add_apply,ContinuousLinearMap.smulRight_apply]
  simp only [smul_add,smul_smul,pow_two,mul_comm (w x) ((fderiv ℝ w x) v)]
  abel

lemma weightedJet_sub {w : Base → ℝ} {f g : Base → V} {x : Base}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    weightedJet w (g-f) x = weightedJet w g x-weightedJet w f x := by
  unfold weightedJet
  rw [fderiv_sub hg hf]
  ext v
  simp only [sub_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,Pi.sub_apply,smul_sub]
  abel

lemma norm_weightedJet_le {w : Base → ℝ} {l : Base → V} {x : Base} {C : ℝ}
    (hl : ‖l x‖ ≤ C) (hd : ‖fderiv ℝ l x‖ ≤ C) :
    ‖weightedJet w l x‖ ≤ (‖w x‖+‖fderiv ℝ w x‖)*C := by
  calc
    _ ≤ ‖w x • fderiv ℝ l x‖+‖(fderiv ℝ w x).smulRight (l x)‖ := norm_sub_le _ _
    _ = ‖w x‖*‖fderiv ℝ l x‖+‖fderiv ℝ w x‖*‖l x‖ := by
      rw [norm_smul,ContinuousLinearMap.norm_smulRight_apply]
    _ ≤ ‖w x‖*C+‖fderiv ℝ w x‖*C := by gcongr
    _ = _ := by ring

theorem compact_injective_stability {K : Set (Base →L[ℝ] V)}
    (hK : IsCompact K) (hI : ∀ L ∈ K, Function.Injective L) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ L ∈ K, ∀ H : Base →L[ℝ] V,
      ‖H-L‖ < ε → Function.Injective H := by
  obtain ⟨ε,hε,he⟩ := hK.exists_thickening_subset_open
    ContinuousLinearMap.isOpen_injective hI
  exact ⟨ε,hε,fun L hL H hH => he
    (Metric.mem_thickening_iff.mpr ⟨L,hL,by simpa only [dist_eq_norm] using hH⟩)⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

lemma localizedWeight_smooth (p : M) {ψ : M → ℝ}
    (hψ : ContMDiff planeModel 𝓘(ℝ) ∞ ψ) (hs : tsupport ψ ⊆ (chart p).source) :
    ContDiff ℝ ∞ (localizedWeight p ψ) := localize_smooth p hψ hs contMDiff_const

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

lemma localized_weightedJet {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ,V) 1 f) (p : M) {ψ : M → ℝ}
    (hψ : ContMDiff planeModel 𝓘(ℝ) ∞ ψ) (hs : tsupport ψ ⊆ (chart p).source)
    {x : Base} (hx : x ∈ (chart p).target) :
    weightedJet (localizedWeight p ψ) (localize p ψ f) x =
      (ψ ((chart p).symm x))^4 •
        ((mfderiv planeModel 𝓘(ℝ,V) f ((chart p).symm x)).comp
          (mfderiv 𝓘(ℝ,Base) planeModel (chart p).symm x)) := by
  have hh : DifferentiableAt ℝ (f ∘ (chart p).symm) x :=
    ((hf.mdifferentiable one_ne_zero).mdifferentiableAt.comp x
      ((chart_mdifferentiable p).mdifferentiableAt_symm hx)).differentiableAt
  have he : localize p ψ f =ᶠ[𝓝 x]
      fun y => localizedWeight p ψ y • (f ∘ (chart p).symm) y := by
    filter_upwards [(chart p).open_target.mem_nhds hx] with y hy
    simp only [localizedWeight,localize,indicator_of_mem hy,smul_eq_mul,mul_one,
      Function.comp_apply]
  rw [weightedJet_eq_smul ((localizedWeight_smooth p hψ hs).differentiable (by simp) x) hh he,
    fderiv_comp_chart_symm hf p hx]
  have hw : localizedWeight p ψ x = (ψ ((chart p).symm x))^2 := by
    simp only [localizedWeight,localize,indicator_of_mem hx,smul_eq_mul,mul_one]
  rw [hw,← pow_mul]
  norm_num
  rfl

/-- The weighted jet loses no immersion information wherever its weight is
nonzero; the chart differential is an isomorphism there. -/
lemma localized_weightedJet_injective_iff {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ,V) 1 f) (p : M) {ψ : M → ℝ}
    (hψ : ContMDiff planeModel 𝓘(ℝ) ∞ ψ) (hs : tsupport ψ ⊆ (chart p).source)
    {x : Base} (hx : x ∈ (chart p).target) (hw : ψ ((chart p).symm x) ≠ 0) :
    Function.Injective (weightedJet (localizedWeight p ψ) (localize p ψ f) x) ↔
      Function.Injective (mfderiv planeModel 𝓘(ℝ,V) f ((chart p).symm x)) := by
  rw [localized_weightedJet hf p hψ hs hx]
  constructor
  · intro hi
    have hcomp : Function.Injective
        ((mfderiv planeModel 𝓘(ℝ,V) f ((chart p).symm x)).comp
          (mfderiv 𝓘(ℝ,Base) planeModel (chart p).symm x)) := by
      intro v u h
      apply hi
      change (ψ ((chart p).symm x))^4 •
          ((mfderiv planeModel 𝓘(ℝ,V) f ((chart p).symm x)).comp
            (mfderiv 𝓘(ℝ,Base) planeModel (chart p).symm x)) v = _
      exact congrArg ((ψ ((chart p).symm x))^4 • ·) h
    change Function.Injective
      ((mfderiv planeModel 𝓘(ℝ,V) f ((chart p).symm x)) ∘
        (mfderiv 𝓘(ℝ,Base) planeModel (chart p).symm x)) at hcomp
    exact hcomp.of_comp_right ((chart_mdifferentiable p).symm.mfderiv_surjective hx)
  · intro hi
    exact (smul_right_injective V (pow_ne_zero 4 hw)).comp
      (hi.comp ((chart_mdifferentiable p).symm.mfderiv_injective hx))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_C1ImmersionApproximation
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothing a compact C1 immersion while keeping its differential injective. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma coreThreshold_pos : 0 < A.coreThreshold := by unfold coreThreshold; positivity

omit [CompactSpace M] in
lemma weightCore_nonzero (i : A.centers) {p : M} (hp : p ∈ A.weightCore i) :
    A.weight i p ≠ 0 := by
  intro hz
  have h := A.coreThreshold_pos
  change A.coreThreshold ≤ (A.weight i p)^2 at hp
  rw [hz,zero_pow (by decide : 2 ≠ 0)] at hp
  exact (not_lt_of_ge hp) h

omit [CompactSpace M] in
lemma weightCore_source (i : A.centers) : A.weightCore i ⊆ (chart (i : M)).source :=
  fun _ hp => A.weight_support i (subset_tsupport _ (A.weightCore_nonzero i hp))

lemma weightCore_compact (i : A.centers) : IsCompact (A.weightCore i) :=
  (isClosed_le continuous_const ((A.weight_smooth i).continuous.pow 2)).isCompact

lemma coordinateCore_compact (i : A.centers) : IsCompact (A.coordinateCore i) :=
  (A.weightCore_compact i).image_of_continuousOn
    ((chart (i : M)).continuousOn.mono (A.weightCore_source i))

omit [CompactSpace M] in
lemma mem_some_weightCore (p : M) : ∃ i : A.centers, p ∈ A.weightCore i := by
  classical
  by_contra hn
  have hi (i : A.centers) : (A.weight i p)^2 ≤ A.coreThreshold :=
    le_of_lt (lt_of_not_ge (fun h => hn ⟨i,h⟩))
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset A.centers)) (fun i _ => hi i)
  rw [A.partition p] at hs
  have hcount : (∑ _i : A.centers, A.coreThreshold) =
      (Fintype.card A.centers : ℝ) / ((Fintype.card A.centers : ℝ)+1) := by
    simp [coreThreshold,div_eq_mul_inv]
  rw [hcount] at hs
  have hlt : (Fintype.card A.centers : ℝ) / ((Fintype.card A.centers : ℝ)+1) < 1 :=
    (div_lt_one (by positivity)).mpr (by linarith)
  exact (not_lt_of_ge hs) hlt

omit [CompactSpace M] in
lemma coordinateCore_target (i : A.centers) : A.coordinateCore i ⊆ (chart (i : M)).target := by
  rintro _ ⟨p,hp,rfl⟩
  exact (chart (i : M)).map_source (A.weightCore_source i hp)

omit [CompactSpace M] in
lemma coordinateCore_weight_nonzero (i : A.centers) {x : Base}
    (hx : x ∈ A.coordinateCore i) : A.weight i ((chart (i : M)).symm x) ≠ 0 := by
  obtain ⟨p,hp,rfl⟩ := hx
  rw [(chart (i : M)).left_inv (A.weightCore_source i hp)]
  exact A.weightCore_nonzero i hp

/-- Every C1 immersion has a positive tolerance in the finite localized C1
norm within which all C1 maps remain immersions. -/
theorem immersion_C1_tolerance {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ,V) 1 f)
    (hI : ∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ,V) f p)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : M → V, ContMDiff planeModel 𝓘(ℝ,V) 1 g →
      A.C1Bound ε (g-f) → ∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ,V) g p) := by
  classical
  let w : A.centers → Base → ℝ := fun i => localizedWeight (i : M) (A.weight i)
  let l : A.centers → (M → V) → Base → V := fun i h => localize (i : M) (A.weight i) h
  have hw (i : A.centers) : ContDiff ℝ 1 (w i) :=
    (localizedWeight_smooth (i : M) (A.weight_smooth i) (A.weight_support i)).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hl (i : A.centers) : ContDiff ℝ 1 (l i f) :=
    localize_C1 (i : M) (A.weight_smooth i) (A.weight_support i) hf
  have hdata (i : A.centers) : ∃ r D : ℝ, 0 < r ∧ 0 < D ∧
      (∀ x ∈ A.coordinateCore i, ‖w i x‖+‖fderiv ℝ (w i) x‖ ≤ D) ∧
      ∀ x ∈ A.coordinateCore i, ∀ H : Base →L[ℝ] V,
        ‖H-weightedJet (w i) (l i f) x‖ < r → Function.Injective H := by
    obtain ⟨r,hr,hrb⟩ := compact_injective_stability
      ((A.coordinateCore_compact i).image (continuous_weightedJet (hw i) (hl i)))
      (by
        rintro _ ⟨x,hx,rfl⟩
        exact (localized_weightedJet_injective_iff hf (i : M) (A.weight_smooth i)
          (A.weight_support i) (A.coordinateCore_target i hx)
          (A.coordinateCore_weight_nonzero i hx)).mpr (hI _))
    obtain ⟨C,hC⟩ := (A.coordinateCore_compact i).exists_bound_of_continuousOn
      (((hw i).continuous.norm.add ((hw i).continuous_fderiv one_ne_zero).norm).continuousOn)
    refine ⟨r,1+|C|,hr,by positivity,?_,?_⟩
    · intro x hx
      exact (le_abs_self _).trans ((hC x hx).trans (by linarith [le_abs_self C]))
    · intro x hx H hH
      exact hrb _ (mem_image_of_mem _ hx) H hH
  choose r D hr hD hDb hrb using hdata
  have hev : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ i : A.centers, ε < r i / D i :=
    Filter.eventually_all.mpr (fun i => gt_mem_nhds (div_pos (hr i) (hD i)))
  obtain ⟨η,hη,hηb⟩ := Metric.eventually_nhds_iff.mp hev
  let ε := η/2
  have hε : 0 < ε := half_pos hη
  have hεi (i : A.centers) : ε < r i / D i :=
    hηb (by simpa only [Real.dist_eq,sub_zero,abs_of_pos hε] using half_lt_self hη) i
  refine ⟨ε,hε,?_⟩
  intro g hg hb p
  obtain ⟨i,hi⟩ := A.mem_some_weightCore p
  let x := chart (i : M) p
  have hx : x ∈ A.coordinateCore i := mem_image_of_mem _ hi
  have hgl : ContDiff ℝ 1 (l i g) :=
    localize_C1 (i : M) (A.weight_smooth i) (A.weight_support i) hg
  have hclose : ‖weightedJet (w i) (l i g) x-weightedJet (w i) (l i f) x‖ < r i := by
    have he : weightedJet (w i) (localize (i : M) (A.weight i) (g-f)) x =
        weightedJet (w i) (l i g) x-weightedJet (w i) (l i f) x := by
      have hlsub : localize (i : M) (A.weight i) (g-f) = l i g-l i f := by
        funext y
        by_cases hy : y ∈ (chart (i : M)).target
        · simp only [l,localize,indicator_of_mem hy,Pi.sub_apply,smul_sub]
        · simp only [l,localize,indicator_of_notMem hy,Pi.sub_apply,sub_self]
      rw [hlsub]
      exact weightedJet_sub ((hl i).differentiable one_ne_zero x)
        (hgl.differentiable one_ne_zero x)
    rw [← he]
    calc
      _ ≤ (‖w i x‖+‖fderiv ℝ (w i) x‖)*ε := norm_weightedJet_le (hb i x).1 (hb i x).2
      _ ≤ D i*ε := mul_le_mul_of_nonneg_right (hDb i x hx) hε.le
      _ < r i := by simpa only [mul_comm] using (lt_div_iff₀ (hD i)).mp (hεi i)
  have hgi := (localized_weightedJet_injective_iff hg (i : M) (A.weight_smooth i)
    (A.weight_support i) (A.coordinateCore_target i hx)
    (A.coordinateCore_weight_nonzero i hx)).mp (hrb i x hx _ hclose)
  change Function.Injective (mfderiv planeModel 𝓘(ℝ,V) g
    ((chart (i : M)).symm (chart (i : M) p))) at hgi
  rw [(chart (i : M)).left_inv (A.weightCore_source i hi)] at hgi
  exact hgi

variable [CompleteSpace V]

include A in
/-- The C1 immersion input is promoted to a smooth immersion by the actual
finite-atlas convolution smoother. -/
theorem smooth_immersion_of_C1 {f : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ,V) 1 f)
    (hI : ∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ,V) f p)) :
    ∃ g : M → V, ContMDiff planeModel 𝓘(ℝ,V) ∞ g ∧
      ∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ,V) g p) := by
  obtain ⟨ε,hε,hstable⟩ := immersion_C1_tolerance A hf hI
  obtain ⟨η,hη,happrox⟩ := A.smooth_C1_approximation hf hε
  obtain ⟨hs,hb⟩ := happrox (η/2) (half_pos hη) (half_lt_self hη)
  exact ⟨A.smooth 1 (η/2) f,hs,hstable _ (hs.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) hb⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Whitney_WhitneyStartingGeometry
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Starting geometry from the precise published C1 surface-immersion input.
The upgrade to a smooth immersion is proved by finite-atlas convolution. -/
noncomputable section
open Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [CompactSpace M] [ChartedSpace Plane M] [IsManifold planeModel ∞ M]

/-- Whitney (1944), Theorem 8 supplies only the C1 immersion. Its smoothing
is carried out here without adding a further published-input hypothesis. -/
theorem smooth_three_space_immersion_of_whitney
    (hW : PublishedInputs.WhitneySurfaceInput M) :
    ∃ f : M → PublishedInputs.ThreeSpace,
      ContMDiff planeModel 𝓘(ℝ,PublishedInputs.ThreeSpace) ∞ f ∧
      ∀ p, Function.Injective (mfderiv planeModel 𝓘(ℝ,PublishedInputs.ThreeSpace) f p) := by
  obtain ⟨f,hf,hI⟩ := hW
  obtain ⟨A⟩ := exists_smoothingAtlas (M := M)
  exact A.smooth_immersion_of_C1 hf hI

/-- The cited Whitney input yields a smooth spherical immersion together
with the actual finite phase data used by the metric correction. -/
theorem metricPhaseData_of_whitney (g : SmoothMetric M)
    (hW : PublishedInputs.WhitneySurfaceInput M) :
    ∃ G : M → Space, ContMDiff planeModel spaceModel ∞ G ∧
      (∀ p, ‖G p‖ = 1) ∧
      (∀ p, Function.Injective (mfderiv planeModel spaceModel G p)) ∧
      Nonempty (MetricGoodPhaseData g G) := by
  obtain ⟨f,hf,hI⟩ := smooth_three_space_immersion_of_whitney hW
  exact metricPhaseData_of_three_space_immersion g hf hI

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ConditionalMain
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth isometric immersions constructed from spherical immersions,
and from the compact surface case of Whitney (1944), Theorem 8, p.274. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] [SecondCountableTopology M]

local instance mainFiberNormed_rfba04e_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance mainFiberSpace_rfba04e_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance mainDualAdd_rfba04e_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance mainDualSmul_rfba04e_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance mainSectionNormed_rfba04e_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance mainSectionSpace_rfba04e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- Main theorem of paper 094-01. The sole published hypothesis is Whitney
(1944), Theorem 8, p.274, specialized to a closed smooth surface. -/
theorem smooth_isometric_immersion_conditional (g : SmoothMetric M)
    (hW : PublishedInputs.WhitneySurfaceInput M) :
    ∃ F : M → Space, IsSmoothIsometricImmersion M g F := by
  obtain ⟨I,hI,hunit,hImm,_⟩ := metricPhaseData_of_whitney g hW
  exact isometric_immersion_of_spherical_immersion g hI hunit hImm

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Main
open scoped SENot

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every compact smooth Riemannian surface, including nonorientable and
disconnected surfaces, admits a smooth isometric immersion into Euclidean
four-space. -/
noncomputable section
open Manifold
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] [SecondCountableTopology M]

theorem smooth_isometric_immersion_oai (g : SmoothMetric M) :
    ∃ F : M → Space, IsSmoothIsometricImmersion M g F :=
  smooth_isometric_immersion_conditional g PublishedInputs.whitneySurfaceInput

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion_oai.{u_1}
