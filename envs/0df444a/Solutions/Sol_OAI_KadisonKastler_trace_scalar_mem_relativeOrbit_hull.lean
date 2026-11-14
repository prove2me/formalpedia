-- Prove2me | solution 1 for OAI.KadisonKastler.trace_scalar_mem_relativeOrbit_hull
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:10:21.245282+00:00
-- url     : https://prove2.me/submissions/06ee2129-2b28-42e7-acee-a4b8e87aa388

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Sublists
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K066
import Theorems.Thm_OAI_KadisonKastler_traceHull_mem_ball

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryDiagonal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Pointwise diagonal comparison in a finite algebra

The least-norm argument is carried out in a supplied faithful tracial
Hilbert realization. Bounded completeness of the concrete finite algebra
keeps Hilbert limits in the operator algebra. No measurable selection or
existence of a boundary space is asserted here.
-/

namespace KadisonKastler

open Filter Set
open scoped Topology

noncomputable section

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The least-norm vector of a convex set is unique. -/
theorem eq_of_convex_least_norm {K : Set E} (hK : Convex ℝ K)
    {x y : E} (hx : x ∈ K) (hy : y ∈ K)
    (hxm : ∀ z ∈ K, ‖x‖ ≤ ‖z‖) (hym : ∀ z ∈ K, ‖y‖ ≤ ‖z‖) : x = y := by
  have hn : ‖y‖ = ‖x‖ := le_antisymm (hym x hx) (hxm y hy)
  have hm : (1 / 2 : ℝ) • (x + y) ∈ K := by
    simpa only [smul_add] using hK hx hy (by norm_num : 0 ≤ (1 / 2 : ℝ))
      (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hp := hxm _ hm
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at hp
  have hs := mul_self_le_mul_self (norm_nonneg x) hp
  have hpar := parallelogram_law_with_norm_mul ℂ x y
  rw [hn] at hpar
  have hz : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- Every nonempty closed convex subset of a Hilbert space has a unique
least-norm vector. -/
theorem exists_unique_least_norm [CompleteSpace E] {K : Set E}
    (hne : K.Nonempty) (hclosed : IsClosed K) (hconvex : Convex ℝ K) :
    ∃! x : E, x ∈ K ∧ ∀ y ∈ K, ‖x‖ ≤ ‖y‖ := by
  let : InnerProductSpace ℝ E := InnerProductSpace.rclikeToReal ℂ E
  obtain ⟨x, hx, hmin⟩ := exists_norm_eq_iInf_of_complete_convex
    hne hclosed.isComplete hconvex (0 : E)
  have hxm : ∀ y ∈ K, ‖x‖ ≤ ‖y‖ := by
    intro y hy
    have hi : (⨅ w : K, ‖(0 : E) - w‖) ≤ ‖(0 : E) - y‖ :=
      ciInf_le ⟨(0 : ℝ), Set.forall_mem_range.mpr (fun _ => norm_nonneg _)⟩ (⟨y, hy⟩ : K)
    simpa only [zero_sub, norm_neg] using hmin.le.trans hi
  exact ⟨x, ⟨hx, hxm⟩, fun y hy => eq_of_convex_least_norm hconvex hy.1 hx hy.2 hxm⟩

end Hilbert

section Concrete

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {M : VonNeumannAlgebra H} {τ : FaithfulTracialState (Algebra M)}
variable (J : Algebra M →ₗ[ℂ] E)
variable (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)

/-- The definition agrees with the ordinary Hilbert closed convex hull. -/
theorem diagonalTraceHull_eq (s : Set (Algebra M)) :
    diagonalTraceHull J s = closure (convexHull ℝ (J '' s)) := by
  unfold diagonalTraceHull
  congr 1
  exact (J.restrictScalars ℝ).image_convexHull s

/-- The trace hull is convex. -/
theorem diagonalTraceHull_convex (s : Set (Algebra M)) :
    Convex ℝ (diagonalTraceHull J s) := by
  rw [diagonalTraceHull_eq]
  exact (convex_convexHull ℝ _).closure


include hJ in
/-- Trace-isometric linear maps carry trace convex hulls into the hull of
any containing image of the generators. -/
theorem traceHull_map (F : Algebra M →ₗ[ℂ] Algebra M)
    (hF : ∀ x, traceTwoNorm τ (F x) = traceTwoNorm τ x)
    {s t : Set (Algebra M)} (himage : F '' s ⊆ t)
    {b : Algebra M} (hb : J b ∈ diagonalTraceHull J s) :
    J (F b) ∈ diagonalTraceHull J t := by
  obtain ⟨v, hv, hvlim⟩ := mem_closure_iff_seq_limit.mp hb
  choose x hxmem hx using hv
  apply isClosed_closure.mem_of_tendsto
    (show Tendsto (fun n => J (F (x n))) atTop (𝓝 (J (F b))) from ?_)
    (Eventually.of_forall fun n => subset_closure ?_)
  · rw [← tendsto_sub_nhds_zero_iff]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hn := (hvlim.sub_const (J b)).norm
    simpa only [sub_self, norm_zero, ← hx, ← map_sub, hJ, hF] using hn
  · refine ⟨F (x n), ?_, rfl⟩
    apply convexHull_mono himage
    have hm : F (x n) ∈ F '' convexHull ℝ s := ⟨x n, hxmem n, rfl⟩
    have heq : F '' convexHull ℝ s = convexHull ℝ (F '' s) :=
      (F.restrictScalars ℝ).image_convexHull s
    rwa [heq] at hm

include hJ in
/-- Least vectors transform exactly under left and right unitary actions,
provided these actions identify the two generating sets. -/
theorem diagonal_least_covariance (u v : unitary (Algebra M))
    {s t : Set (Algebra M)}
    (hforward : ∀ x ∈ s, (u : Algebra M) * x * star (v : Algebra M) ∈ t)
    (hbackward : ∀ y ∈ t, star (u : Algebra M) * y * (v : Algebra M) ∈ s)
    {b c : Algebra M}
    (hb : J b ∈ diagonalTraceHull J s)
    (hc : J c ∈ diagonalTraceHull J t)
    (hbm : ∀ z ∈ diagonalTraceHull J s, ‖J b‖ ≤ ‖z‖)
    (hcm : ∀ z ∈ diagonalTraceHull J t, ‖J c‖ ≤ ‖z‖) :
    c = (u : Algebra M) * b * star (v : Algebra M) := by
  let F := LinearMap.mulLeftRight ℂ ((u : Algebra M), star (v : Algebra M))
  let R := LinearMap.mulLeftRight ℂ (star (u : Algebra M), (v : Algebra M))
  have hF (x : Algebra M) : traceTwoNorm τ (F x) = traceTwoNorm τ x := by
    change traceTwoNorm τ (((u : Algebra M) * x) * (star v : unitary (Algebra M))) = _
    simp only [traceTwoNorm_mul_unitary, traceTwoNorm_unitary_mul]
  have hR (x : Algebra M) : traceTwoNorm τ (R x) = traceTwoNorm τ x := by
    change traceTwoNorm τ (((star u : unitary (Algebra M)) : Algebra M) * x *
      (v : Algebra M)) = _
    simp only [traceTwoNorm_mul_unitary, traceTwoNorm_unitary_mul]
  have hFb := traceHull_map J hJ F hF (by rintro _ ⟨x, hx, rfl⟩; exact hforward x hx) hb
  have hRc := traceHull_map J hJ R hR (by rintro _ ⟨x, hx, rfl⟩; exact hbackward x hx) hc
  have hle : ‖J (F b)‖ ≤ ‖J c‖ := by
    simpa only [hJ, hF, hR] using hbm _ hRc
  apply traceHilbert_injective J hJ
  exact eq_of_convex_least_norm (diagonalTraceHull_convex J t) hc hFb hcm
    (fun z hz => hle.trans (hcm z hz))


end Concrete


end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TraceHullTrace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The trace is constant on trace-closed convex orbit hulls -/

namespace KadisonKastler

open Set Filter
open scoped Topology

noncomputable section

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {M : VonNeumannAlgebra H} {τ : FaithfulTracialState (Algebra M)}

/-- A trace value shared by every generator is shared by every algebra
element in the trace Hilbert closure of their convex hull. -/
theorem trace_eq_of_mem_traceHull (J : Algebra M →ₗ[ℂ] E)
    (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    {S : Set (Algebra M)} {c : ℂ} (hS : ∀ x ∈ S, τ.toLinearMap x = c)
    {b : Algebra M} (hb : J b ∈ diagonalTraceHull J S) : τ.toLinearMap b = c := by
  have hconv : ∀ x ∈ convexHull ℝ S, τ.toLinearMap x = c := by
    have hc : Convex ℝ {x : Algebra M | τ.toLinearMap x = c} :=
      (convex_singleton c).linear_preimage (τ.toLinearMap.restrictScalars ℝ)
    exact convexHull_min hS hc
  obtain ⟨v, hv, hvlim⟩ := mem_closure_iff_seq_limit.mp hb
  choose x hxmem hx using hv
  have htrace (n : ℕ) : τ.toLinearMap (x n) = c := hconv _ (hxmem n)
  have hbound (n : ℕ) : ‖τ.toLinearMap (x n) - τ.toLinearMap b‖ ≤ ‖v n - J b‖ := by
    calc
      _ = ‖τ.toLinearMap (x n - b)‖ := by rw [map_sub]
      _ ≤ traceTwoNorm τ (x n - b) := τ.norm_apply_le_traceTwoNorm _
      _ = ‖J (x n - b)‖ := (hJ _).symm
      _ = _ := by rw [map_sub, hx]
  have hlim : Tendsto (fun n => ‖τ.toLinearMap (x n) - τ.toLinearMap b‖)
      atTop (𝓝 0) := by
    have ht := (hvlim.sub_const (J b)).norm
    simp only [sub_self, norm_zero] at ht
    exact squeeze_zero (fun n => norm_nonneg _) hbound ht
  have he : ‖c - τ.toLinearMap b‖ = 0 := by
    have hconst : Tendsto (fun _ : ℕ => ‖c - τ.toLinearMap b‖) atTop (𝓝 0) := by
      simpa only [htrace] using hlim
    exact tendsto_nhds_unique tendsto_const_nhds hconst
  exact (sub_eq_zero.mp (norm_eq_zero.mp he)).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RelativeTraceAveraging
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.TraceQuotientMap.comapEquiv_quotient _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.expectedTrace_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrixSequenceQuotient_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.realTrace_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.traceStateRepresentation_vector _root_.OAI.KadisonKastler.traceStateRight_vector _root_.OAI.KadisonKastler.traceStateVector_sub _root_.OAI.KadisonKastler.tracialHilbertConjugation_embedding _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceContinuous_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.tracialSequenceValue_one _root_.OAI.KadisonKastler.tracialStarIsometry_embedding _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Relative scalar averaging in the trace Hilbert space

The least-vector argument applies to the unitary group of an irreducible
subalgebra. This supplies the relative averaging needed for bounded-ball
tests without an amenability hypothesis on the ambient factor.
-/

namespace KadisonKastler

open Set

noncomputable section

variable {H E R : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [CStarAlgebra R] {M : VonNeumannAlgebra H}
  {τ : FaithfulTracialState (Algebra M)}

/-- Irreducibility makes the unique least vector of a relative unitary
orbit scalar. The closure is taken in the actual trace Hilbert space. -/
theorem exists_relative_scalar_in_traceOrbit
    (J : Algebra M →ₗ[ℂ] E) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (hτ : FiniteVectorTrace τ) (φ : R →⋆ₐ[ℂ] Algebra M)
    (hirr : ∀ b : Algebra M, (∀ r : R, φ r * b = b * φ r) →
      ∃ c : ℂ, b = c • (1 : Algebra M))
    (a : Algebra M) :
    ∃ c : ℂ, J (c • (1 : Algebra M)) ∈ diagonalTraceHull J (relativeUnitaryOrbit φ a) := by
  let U (u : unitary R) : unitary (Algebra M) :=
    Unitary.map (StarMonoidHom.ofClass φ) u
  have hU (u : unitary R) : (U u : Algebra M) = φ u := rfl
  have horbit : ∀ x ∈ relativeUnitaryOrbit φ a, ‖x‖ ≤ ‖a‖ := by
    rintro _ ⟨u, rfl⟩
    change ‖(U u : Algebra M) * a * star (U u : Algebra M)‖ ≤ ‖a‖
    simpa only [CStarRing.norm_coe_unitary_mul, ← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary] using (le_rfl : ‖a‖ ≤ ‖a‖)
  have hne : (relativeUnitaryOrbit φ a).Nonempty := by
    refine ⟨a, 1, ?_⟩
    simp
  obtain ⟨z, hz, _⟩ := exists_unique_least_norm
    (show (diagonalTraceHull J (relativeUnitaryOrbit φ a)).Nonempty from by
      obtain ⟨x, hx⟩ := hne
      exact ⟨J x, subset_closure ⟨x, subset_convexHull ℝ _ hx, rfl⟩⟩)
    isClosed_closure (diagonalTraceHull_convex J _)
  obtain ⟨b, hbz, _⟩ := traceHull_mem_ball J hJ hτ 0 (norm_nonneg a)
    (fun x hx => by simpa only [sub_zero] using horbit x hx) hz.1
  have hb : J b ∈ diagonalTraceHull J (relativeUnitaryOrbit φ a) := hbz.symm ▸ hz.1
  have hbm : ∀ w ∈ diagonalTraceHull J (relativeUnitaryOrbit φ a), ‖J b‖ ≤ ‖w‖ :=
    hbz.symm ▸ hz.2
  have hfix (u : unitary R) : b = (U u : Algebra M) * b * star (U u : Algebra M) := by
    apply diagonal_least_covariance J hJ (U u) (U u)
      (s := relativeUnitaryOrbit φ a) (t := relativeUnitaryOrbit φ a)
      ?_ ?_ hb hb hbm hbm
    · rintro _ ⟨v, rfl⟩
      refine ⟨u * v, ?_⟩
      simp only [hU, Submonoid.coe_mul, map_mul, star_mul, mul_assoc]
    · rintro _ ⟨v, rfl⟩
      refine ⟨star u * v, ?_⟩
      simp only [hU, Submonoid.coe_mul,
        Unitary.coe_star, map_mul, map_star, star_mul, star_star, mul_assoc]
  have hcomm (u : unitary R) : φ u * b = b * φ u := by
    have he := congrArg (fun x : Algebra M => x * (U u : Algebra M)) (hfix u)
    have he' : (U u : Algebra M) * b = b * (U u : Algebra M) := by
      simpa only [mul_assoc, Unitary.star_mul_self_of_mem (U u).property, mul_one] using he.symm
    simpa only [hU] using he'
  let T : R →ₗ[ℂ] Algebra M :=
    (LinearMap.mulRight ℂ b - LinearMap.mulLeft ℂ b).comp φ.toLinearMap
  have hcentral (r : R) : φ r * b = b * φ r := by
    have hn := norm_le_twice_unitary_bound T (C := 0) (fun u => by
      change ‖φ u * b - b * φ u‖ ≤ 0
      rw [hcomm, sub_self, norm_zero]) r
    have hz : T r = 0 := norm_eq_zero.mp (le_antisymm (by simpa using hn) (norm_nonneg _))
    exact sub_eq_zero.mp hz
  obtain ⟨c, rfl⟩ := hirr b hcentral
  exact ⟨c, hb⟩

/-- Relative unitary conjugation preserves the given trace. -/
theorem trace_relativeUnitaryOrbit (φ : R →⋆ₐ[ℂ] Algebra M) (a : Algebra M)
    {x : Algebra M} (hx : x ∈ relativeUnitaryOrbit φ a) :
    τ.toLinearMap x = τ.toLinearMap a := by
  obtain ⟨u, rfl⟩ := hx
  have hu : star (φ u) * φ u = 1 := by
    simpa only [map_mul, map_star, map_one] using
      congrArg φ (Unitary.star_mul_self_of_mem u.property)
  calc
    _ = τ.toLinearMap (φ u * (a * star (φ u))) := congrArg τ.toLinearMap (mul_assoc _ _ _)
    _ = τ.toLinearMap ((a * star (φ u)) * φ u) := τ.tracial _ _
    _ = _ := by rw [mul_assoc, hu, mul_one]

/-- The scalar in the relative orbit hull is precisely the trace. -/
theorem trace_scalar_mem_relativeOrbit_hull_oai
    (J : Algebra M →ₗ[ℂ] E) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (hτ : FiniteVectorTrace τ) (φ : R →⋆ₐ[ℂ] Algebra M)
    (hirr : ∀ b : Algebra M, (∀ r : R, φ r * b = b * φ r) →
      ∃ c : ℂ, b = c • (1 : Algebra M)) (a : Algebra M) :
    J (τ.toLinearMap a • (1 : Algebra M)) ∈ diagonalTraceHull J (relativeUnitaryOrbit φ a) := by
  obtain ⟨c, hc⟩ := exists_relative_scalar_in_traceOrbit J hJ hτ φ hirr a
  have htrace := trace_eq_of_mem_traceHull J hJ
    (fun x hx => trace_relativeUnitaryOrbit φ a hx) hc
  simp only [map_smul, τ.map_one, smul_eq_mul, mul_one] at htrace
  rwa [htrace] at hc

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.KadisonKastler.trace_scalar_mem_relativeOrbit_hull_oai.{u_1, u_2, u_3} := @OAI.KadisonKastler.trace_scalar_mem_relativeOrbit_hull_oai.{u_1, u_2, u_3}
