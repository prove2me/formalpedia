-- Prove2me | solution 1 for OAI.KadisonKastler.FullMatrixCorner.representedCorner_isII1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:25:00.996118+00:00
-- url     : https://prove2.me/submissions/c7a4cb95-0c11-488d-af79-13c2d26c1557

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
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Adjoint
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
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
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
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.DeriveCountable
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
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K014
import Definitions.Def_Q260K061

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RepresentedCorner
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Concrete compression to a common closed subspace

The corner acts on the subspace itself. Its operators are characterized by
membership of their extension by zero in the original von Neumann algebra.
This constructs the actual corner and proves that a common compression does
not increase Kadison--Kastler distance.
-/

namespace KadisonKastler

open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (E : Submodule ℂ H) [CompleteSpace E]

variable [CompleteSpace H]

theorem cornerCompression_mem {M : VonNeumannAlgebra H} (hp : E.starProjection ∈ M)
    {T : H →L[ℂ] H} (hT : T ∈ M) :
    cornerCompression E T ∈ representedCorner E M hp := by
  rw [mem_representedCorner, cornerExtension_compression]
  exact M.mul_mem (M.mul_mem hp hT) hp

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InfiniteCornerInflation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Inflation through countably many matrix corners

The hypotheses are the algebraic matrix-unit relations and the strong sum
of their diagonal projections. They give an actual Hilbert direct-sum
decomposition. A corner operator is then applied on each summand; in
particular a corner unitary inflates with no loss in displacement.
-/

namespace KadisonKastler

open scoped BigOperators Topology
open Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : Submodule ℂ H) [CompleteSpace E]

namespace FullMatrixCorner

variable {E} (F : FullMatrixCorner E)

theorem column_adjoint_apply (i : ℕ) (x : H) :
    (F.column i).toContinuousLinearMap.adjoint x =
      E.orthogonalProjectionOnto (F.entry 0 i x) := by
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (F.entry i 0 y) x =
    inner ℂ y (E.orthogonalProjectionOnto (F.entry 0 i x))
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  rw [← F.star_entry i 0, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]

theorem matrixEntry_apply (T : H →L[ℂ] H) (i j : ℕ) (x : E) :
    F.matrixEntry T i j x =
      E.orthogonalProjectionOnto (F.entry 0 i (T (F.entry j 0 x))) := by
  exact F.column_adjoint_apply i _

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InflatedConjugacy
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.FullMatrixCorner.regroupingIsometry_column _root_.OAI.KadisonKastler.FullMatrixCorner.regroupingOperator_column _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransport_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.canonicalMatrixCorner_entry _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Recovering the full algebra from its common matrix corners -/

namespace KadisonKastler

open Filter
open scoped BigOperators Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

theorem extension_matrixEntry (T : H →L[ℂ] H) (i j : ℕ) :
    cornerExtension E (F.matrixEntry T i j) = F.entry 0 i * T * F.entry j 0 := by
  have he : F.matrixEntry T i j =
      cornerCompression E (F.entry 0 i * T * F.entry j 0) := by
    apply ContinuousLinearMap.ext
    intro x
    exact F.matrixEntry_apply T i j x
  rw [he, cornerExtension_compression, ← F.zero_zero]
  calc
    F.entry 0 0 * (F.entry 0 i * T * F.entry j 0) * F.entry 0 0 =
        (F.entry 0 0 * F.entry 0 i) * T * (F.entry j 0 * F.entry 0 0) := by
      noncomm_ring
    _ = _ := by rw [F.mul_entry, F.mul_entry]; simp

/-- Membership of every transported matrix entry determines membership of
the whole operator. The proof uses actual finite compressions and WOT closure. -/
theorem mem_of_matrixEntries (N : VonNeumannAlgebra H)
    (hF : ∀ i j, F.entry i j ∈ N) (T : H →L[ℂ] H)
    (hT : ∀ i j, cornerExtension E (F.matrixEntry T i j) ∈ N) : T ∈ N := by
  have hterm (i j : ℕ) : F.entry i i * T * F.entry j j ∈ N := by
    have h := N.mul_mem (N.mul_mem (hF i 0) (hT i j)) (hF 0 j)
    rw [F.extension_matrixEntry] at h
    have he : F.entry i 0 * (F.entry 0 i * T * F.entry j 0) * F.entry 0 j =
        F.entry i i * T * F.entry j j := by
      calc
        _ = (F.entry i 0 * F.entry 0 i) * T * (F.entry j 0 * F.entry 0 j) := by
          noncomm_ring
        _ = _ := by rw [F.mul_entry, F.mul_entry]; simp
    rwa [he] at h
  have hmem (s : Finset ℕ) : F.partialDiagonal s * T * F.partialDiagonal s ∈ N := by
    simp only [partialDiagonal, Finset.sum_mul, Finset.mul_sum]
    exact N.sum_mem (fun i _ => N.sum_mem (fun j _ => hterm j i))
  let a (s : Finset ℕ) : Algebra N :=
    ⟨F.partialDiagonal s * T * F.partialDiagonal s, hmem s⟩
  apply Generator.Tracial.weak_operator_limit_mem (l := atTop) N a T
  intro x y
  have ht := (F.partialDiagonal_tendsto y).inner (𝕜 := ℂ)
    (T.continuous.continuousAt.tendsto.comp (F.partialDiagonal_tendsto x))
  have he (s : Finset ℕ) :
      inner ℂ (F.partialDiagonal s y) (T (F.partialDiagonal s x)) =
        inner ℂ y ((F.partialDiagonal s * T * F.partialDiagonal s) x) := by
    rw [mul_apply_eq_comp, mul_apply_eq_comp]
    rw [← ContinuousLinearMap.adjoint_inner_left (F.partialDiagonal s)
      (T (F.partialDiagonal s x)) y]
    simp only [← ContinuousLinearMap.star_eq_adjoint, F.partialDiagonal_star]
  exact ht.congr he

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AmplifiedAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A concrete infinite amplification

The amplification of a corner algebra is the commutant of its diagonally
represented commutant. Its matrix entries are exactly the operators in the
corner algebra. This construction uses the actual countable matrix units.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

theorem inner_matrixEntry (T : H →L[ℂ] H) (i j : ℕ) (x y : E) :
    inner ℂ y (F.matrixEntry T i j x) = inner ℂ (F.column i y) (T (F.column j x)) := by
  exact ContinuousLinearMap.adjoint_inner_right (F.column i).toContinuousLinearMap y _

theorem matrixEntry_inflate_mul (S : E →L[ℂ] E) (T : H →L[ℂ] H) (i j : ℕ) :
    F.matrixEntry (F.inflateHom S * T) i j = S * F.matrixEntry T i j := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [F.inner_matrixEntry]
  change inner ℂ (F.column i y) (F.inflateHom S (T (F.column j x))) = _
  rw [← ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ (star (F.inflateHom S) (F.column i y)) (T (F.column j x)) = _
  rw [← map_star, F.inflateHom_column, ← F.inner_matrixEntry]
  exact ContinuousLinearMap.adjoint_inner_left S (F.matrixEntry T i j x) y

theorem matrixEntry_mul_inflate (S : E →L[ℂ] E) (T : H →L[ℂ] H) (i j : ℕ) :
    F.matrixEntry (T * F.inflateHom S) i j = F.matrixEntry T i j * S := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [F.inner_matrixEntry]
  change inner ℂ (F.column i y) (T (F.inflateHom S (F.column j x))) = _
  rw [F.inflateHom_column, ← F.inner_matrixEntry]
  rfl

theorem ext_matrixEntry {T U : H →L[ℂ] H}
    (h : ∀ i j, F.matrixEntry T i j = F.matrixEntry U i j) : T = U := by
  apply F.ext_on_columns
  intro j x
  apply F.eq_of_inner_columns
  intro i y
  rw [← F.inner_matrixEntry, ← F.inner_matrixEntry, h]

theorem mem_amplifiedAlgebra_iff_commute (M : VonNeumannAlgebra E) (T : H →L[ℂ] H) :
    T ∈ F.amplifiedAlgebra M ↔
      ∀ S ∈ M.commutant, Commute (F.inflateHom S) T := by
  change T ∈ StarSubalgebra.centralizer ℂ _ ↔ _
  rw [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h S hS
    exact (h (F.inflateHom S) ⟨S, hS, rfl⟩).1
  · intro h _ hS
    obtain ⟨S, hS, rfl⟩ := hS
    refine ⟨(h S hS).eq, ?_⟩
    rw [← map_star]
    exact (h (star S) (star_mem hS)).eq

/-- Matrix-entry membership characterizes the concrete amplification. -/
theorem mem_amplifiedAlgebra_iff (M : VonNeumannAlgebra E) (T : H →L[ℂ] H) :
    T ∈ F.amplifiedAlgebra M ↔ ∀ i j, F.matrixEntry T i j ∈ M := by
  rw [F.mem_amplifiedAlgebra_iff_commute]
  constructor
  · intro h i j
    rw [← M.commutant_commutant, VonNeumannAlgebra.mem_commutant_iff]
    intro S hS
    have hh := congrArg (fun R => F.matrixEntry R i j) (h S hS).eq
    simpa only [F.matrixEntry_inflate_mul, F.matrixEntry_mul_inflate] using hh
  · intro h S hS
    apply F.ext_matrixEntry
    intro i j
    rw [F.matrixEntry_inflate_mul, F.matrixEntry_mul_inflate]
    exact (VonNeumannAlgebra.mem_commutant_iff.mp hS _ (h i j)).symm

theorem inflate_mem_amplifiedAlgebra (M : VonNeumannAlgebra E) {T : E →L[ℂ] E}
    (hT : T ∈ M) : F.inflateHom T ∈ F.amplifiedAlgebra M := by
  rw [F.mem_amplifiedAlgebra_iff_commute]
  intro S hS
  change F.inflateHom S * F.inflateHom T = F.inflateHom T * F.inflateHom S
  rw [← map_mul, ← map_mul]
  exact congrArg F.inflateHom (VonNeumannAlgebra.mem_commutant_iff.mp hS T hT).symm

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CornerFactorStructure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Factor and finite-isometry structure of represented corners

Countable full matrix units identify the original algebra with the actual
amplification of its first corner. A central corner operator therefore
inflates to a central ambient operator. Finiteness of the first projection
also passes directly to the represented corner by extension by zero.
No trace or semifinite decomposition is assumed in these arguments.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

/-- Common full matrix units recover an algebra from its actual first corner. -/
theorem amplified_representedCorner_eq (M : VonNeumannAlgebra H)
    (hF : ∀ i j, F.entry i j ∈ M) :
    F.amplifiedAlgebra (representedCorner E M (F.zero_zero ▸ hF 0 0)) = M := by
  apply VonNeumannAlgebra.ext
  intro T
  rw [F.mem_amplifiedAlgebra_iff]
  constructor
  · intro h
    exact F.mem_of_matrixEntries M hF T h
  · intro h i j
    rw [mem_representedCorner, F.extension_matrixEntry]
    exact M.mul_mem (M.mul_mem (hF 0 i) h) (hF j 0)

theorem inflateHom_injective : Function.Injective F.inflateHom := by
  intro T S h
  apply ContinuousLinearMap.ext
  intro x
  have he := congrArg (fun A : H →L[ℂ] H => A (F.column 0 x)) h
  rw [F.inflateHom_column, F.inflateHom_column] at he
  exact (F.column 0).injective he

/-- Scalar center descends through the concrete matrix-corner decomposition. -/
theorem scalarCenter_representedCorner (M : VonNeumannAlgebra H)
    (hF : ∀ i j, F.entry i j ∈ M) (hM : ScalarCenter M) :
    ScalarCenter (representedCorner E M (F.zero_zero ▸ hF 0 0)) := by
  intro T hT hcomm
  let P := representedCorner E M (F.zero_zero ▸ hF 0 0)
  have hPT : T ∈ P := hT
  have hI : F.inflateHom T ∈ M := by
    rw [← F.amplified_representedCorner_eq M hF]
    exact F.inflate_mem_amplifiedAlgebra P hPT
  have hc : ∀ S ∈ M, S * F.inflateHom T = F.inflateHom T * S := by
    intro S hS
    apply F.ext_matrixEntry
    intro i j
    rw [F.matrixEntry_mul_inflate, F.matrixEntry_inflate_mul]
    apply hcomm
    rw [mem_representedCorner, F.extension_matrixEntry]
    exact M.mul_mem (M.mul_mem (hF 0 i) hS) (hF j 0)
  obtain ⟨z, hz⟩ := hM (F.inflateHom T) hI hc
  refine ⟨z, F.inflateHom_injective ?_⟩
  simpa only [map_smul, map_one] using hz

end FullMatrixCorner

omit [CompleteSpace H] in
/-- Extension by zero is faithful, even when the original representation is
not the standard tracial representation. -/
theorem cornerExtension_injective : Function.Injective (cornerExtension E) := by
  intro T S h
  have he := congrArg (cornerCompression E) h
  simpa only [cornerCompression_extension] using he

/-- A finite ambient projection makes the represented corner a finite algebra. -/
theorem finite_representedCorner_of_finite_projection (M : VonNeumannAlgebra H)
    (hE : E.starProjection ∈ M)
    (hfinite : FiniteProjectionIn M ⟨E.starProjection, hE⟩) :
    ∀ v : Algebra (representedCorner E M hE),
      star v * v = 1 → v * star v = 1 := by
  intro v hv
  let w : Algebra M := ⟨cornerExtension E (v : E →L[ℂ] E), v.property⟩
  have hv' : star (v : E →L[ℂ] E) * (v : E →L[ℂ] E) = 1 :=
    congrArg Subtype.val hv
  have hi : star w * w = (⟨E.starProjection, hE⟩ : Algebra M) := by
    apply Subtype.ext
    change star (cornerExtension E (v : E →L[ℂ] E)) *
      cornerExtension E (v : E →L[ℂ] E) = E.starProjection
    rw [← cornerExtension_star, ← cornerExtension_mul, hv', cornerExtension_one]
  have hs : (⟨E.starProjection, hE⟩ : Algebra M) * w = w := by
    apply Subtype.ext
    exact starProjection_mul_cornerExtension E (v : E →L[ℂ] E)
  have ho := congrArg Subtype.val (hfinite w hi hs)
  apply Subtype.ext
  apply cornerExtension_injective
  change cornerExtension E ((v : E →L[ℂ] E) * star (v : E →L[ℂ] E)) =
    cornerExtension E (1 : E →L[ℂ] E)
  rw [cornerExtension_mul, cornerExtension_star, cornerExtension_one]
  exact ho

omit [CompleteSpace H] in
/-- A nonzero corner projection gives a nonzero represented identity. -/
theorem representedCorner_nonzero_of_projection_ne_zero
    (hE : E.starProjection ≠ (0 : H →L[ℂ] H)) : (0 : E →L[ℂ] E) ≠ 1 := by
  intro h
  have he := congrArg (cornerExtension E) h
  exact hE (by simpa only [map_zero, cornerExtension_one] using he.symm)

/-- Proper projection splittings remain proper after compression to a larger
projection. Thus diffuseness passes to every represented corner. -/
theorem diffuse_representedCorner (M : VonNeumannAlgebra H)
    (hE : E.starProjection ∈ M)
    (hdiff : ∀ p : Algebra M, IsStarProjection p → p ≠ 0 →
      ∃ q : Algebra M, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q) :
    ∀ p : Algebra (representedCorner E M hE), IsStarProjection p → p ≠ 0 →
      ∃ q : Algebra (representedCorner E M hE), IsStarProjection q ∧ q ≠ 0 ∧
        q ≠ p ∧ p * q = q ∧ q * p = q := by
  intro p hp hp0
  let a : Algebra M := ⟨cornerExtension E (p : E →L[ℂ] E), p.property⟩
  have ha : IsStarProjection a := by
    constructor
    · apply Subtype.ext
      change cornerExtension E (p : E →L[ℂ] E) *
        cornerExtension E (p : E →L[ℂ] E) = cornerExtension E (p : E →L[ℂ] E)
      rw [← cornerExtension_mul]
      exact congrArg (cornerExtension E) (congrArg Subtype.val hp.isIdempotentElem.eq)
    · apply Subtype.ext
      change star (cornerExtension E (p : E →L[ℂ] E)) =
        cornerExtension E (p : E →L[ℂ] E)
      rw [← cornerExtension_star]
      exact congrArg (cornerExtension E) (congrArg Subtype.val hp.isSelfAdjoint.star_eq)
  have ha0 : a ≠ 0 := by
    intro hz
    apply hp0
    apply Subtype.ext
    apply cornerExtension_injective
    have hh := congrArg Subtype.val hz
    change cornerExtension E (p : E →L[ℂ] E) = 0 at hh
    simpa only [ZeroMemClass.coe_zero, map_zero] using hh
  obtain ⟨q, hq, hq0, hqa, haq, hqa'⟩ := hdiff a ha ha0
  have hl : E.starProjection * (q : H →L[ℂ] H) = q := by
    have he : cornerExtension E (p : E →L[ℂ] E) * (q : H →L[ℂ] H) = q :=
      congrArg Subtype.val haq
    calc
      _ = E.starProjection * (cornerExtension E (p : E →L[ℂ] E) * q.val) := by rw [he]
      _ = (E.starProjection * cornerExtension E (p : E →L[ℂ] E)) * q.val :=
        (mul_assoc _ _ _).symm
      _ = q := by rw [starProjection_mul_cornerExtension, he]
  have hr : (q : H →L[ℂ] H) * E.starProjection = q := by
    have he : (q : H →L[ℂ] H) * cornerExtension E (p : E →L[ℂ] E) = q :=
      congrArg Subtype.val hqa'
    calc
      _ = (q.val * cornerExtension E (p : E →L[ℂ] E)) * E.starProjection := by rw [he]
      _ = q.val * (cornerExtension E (p : E →L[ℂ] E) * E.starProjection) :=
        mul_assoc _ _ _
      _ = q := by rw [cornerExtension_mul_starProjection, he]
  let b : Algebra (representedCorner E M hE) :=
    ⟨cornerCompression E (q : H →L[ℂ] H), cornerCompression_mem E hE q.property⟩
  have hb : cornerExtension E (b : E →L[ℂ] E) = (q : H →L[ℂ] H) := by
    change cornerExtension E (cornerCompression E q.val) = q.val
    rw [cornerExtension_compression, hl, hr]
  refine ⟨b, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · apply Subtype.ext
      apply cornerExtension_injective
      change cornerExtension E ((b : E →L[ℂ] E) * b.val) = cornerExtension E b.val
      rw [cornerExtension_mul, hb]
      exact congrArg Subtype.val hq.isIdempotentElem.eq
    · apply Subtype.ext
      apply cornerExtension_injective
      change cornerExtension E (star (b : E →L[ℂ] E)) = cornerExtension E b.val
      rw [cornerExtension_star, hb]
      exact congrArg Subtype.val hq.isSelfAdjoint.star_eq
  · intro hz
    apply hq0
    apply Subtype.ext
    rw [← hb]
    have he := congrArg (fun t : Algebra (representedCorner E M hE) =>
      cornerExtension E (t : E →L[ℂ] E)) hz
    simpa only [ZeroMemClass.coe_zero, map_zero] using he
  · intro hbp
    apply hqa
    apply Subtype.ext
    rw [← hb]
    exact congrArg (fun t : Algebra (representedCorner E M hE) =>
      cornerExtension E (t : E →L[ℂ] E)) hbp
  · apply Subtype.ext
    apply cornerExtension_injective
    change cornerExtension E ((p : E →L[ℂ] E) * b.val) = cornerExtension E b.val
    rw [cornerExtension_mul, hb]
    exact congrArg Subtype.val haq
  · apply Subtype.ext
    apply cornerExtension_injective
    change cornerExtension E ((b : E →L[ℂ] E) * p.val) = cornerExtension E b.val
    rw [cornerExtension_mul, hb]
    exact congrArg Subtype.val hqa'

/-- The finite nonzero first corner of a diffuse scalar-center algebra is an
actual II₁ factor. All projection and finiteness hypotheses are geometric. -/
theorem FullMatrixCorner.representedCorner_isII1_oai (F : FullMatrixCorner E)
    (M : VonNeumannAlgebra H) (hF : ∀ i j, F.entry i j ∈ M)
    (hM : ScalarCenter M) (hE0 : E.starProjection ≠ (0 : H →L[ℂ] H))
    (hfinite : FiniteProjectionIn M ⟨E.starProjection, F.zero_zero ▸ hF 0 0⟩)
    (hdiff : ∀ p : Algebra M, IsStarProjection p → p ≠ 0 →
      ∃ q : Algebra M, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p * q = q ∧ q * p = q) :
    Generator.IsII1Factor
      (representedCorner E M (F.zero_zero ▸ hF 0 0)).toStarSubalgebra := by
  refine {
    nonzero := representedCorner_nonzero_of_projection_ne_zero hE0
    weaklyClosed := representedCornerAlgebra_wotClosed E M (F.zero_zero ▸ hF 0 0)
    factor := ?_
    finite := finite_representedCorner_of_finite_projection M (F.zero_zero ▸ hF 0 0) hfinite
    diffuse := diffuse_representedCorner M (F.zero_zero ▸ hF 0 0) hdiff }
  intro x hx
  obtain ⟨z, hz⟩ := F.scalarCenter_representedCorner M hF hM x.val x.property
    (fun y hy => congrArg Subtype.val (hx ⟨y, hy⟩))
  refine ⟨z, ?_⟩
  rw [Algebra.algebraMap_eq_smul_one]
  apply Subtype.ext
  exact hz

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.FullMatrixCorner.representedCorner_isII1_oai.{u_1} := @OAI.KadisonKastler.FullMatrixCorner.representedCorner_isII1_oai.{u_1}
