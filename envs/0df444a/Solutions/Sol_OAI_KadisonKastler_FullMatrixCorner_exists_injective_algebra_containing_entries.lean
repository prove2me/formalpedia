-- Prove2me | solution 1 for OAI.KadisonKastler.FullMatrixCorner.exists_injective_algebra_containing_entries
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:21:39.703763+00:00
-- url     : https://prove2.me/submissions/326eeb9c-bad2-4dd6-b6d7-39460cb0227c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Spectrum
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
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.LinearAlgebra.Complex.Module
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
import Definitions.Def_Q260K017
import Theorems.Thm_OAI_KadisonKastler_FullMatrixCorner_scalarMatrixAlgebra_isInjective

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
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.FullMatrixCorner.regroupingIsometry_column _root_.OAI.KadisonKastler.FullMatrixCorner.regroupingOperator_column _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransport_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.canonicalMatrixCorner_entry _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FullMatrixInjectivity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.finiteSignedGroup_finite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The type I algebra generated by full countable matrix units

Taking the commutant of the diagonal corner operators realizes the scalar
matrix factor directly. Its matrix coefficients are scalar, so it lies in
any von Neumann algebra containing the original matrix units.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {E : Submodule ℂ H} [CompleteSpace E]

namespace FullMatrixCorner

variable (F : FullMatrixCorner E)

/-- Each corner coefficient of a scalar matrix operator is scalar. -/
theorem scalarMatrixAlgebra_coefficient {T : H →L[ℂ] H}
    (hT : T ∈ F.scalarMatrixAlgebra) (i j : ℕ) :
    ∃ z : ℂ, F.matrixEntry T i j = z • (1 : E →L[ℂ] E) := by
  have hc : F.matrixEntry T i j ∈ Subalgebra.center ℂ (E →L[ℂ] E) := by
    rw [Subalgebra.mem_center_iff]
    intro S
    have h := congrArg (fun R => F.matrixEntry R i j)
      ((F.mem_scalarMatrixAlgebra_iff T).mp hT S).eq
    simpa only [F.matrixEntry_inflate_mul, F.matrixEntry_mul_inflate] using h
  rw [Algebra.IsCentral.center_eq_bot, Algebra.mem_bot] at hc
  obtain ⟨z,hz⟩ := hc
  exact ⟨z, by simpa only [Algebra.algebraMap_eq_smul_one] using hz.symm⟩

/-- Every represented scalar matrix operator lies in any algebra containing the entries. -/
theorem scalarMatrixAlgebra_le (M : VonNeumannAlgebra H)
    (hF : ∀ i j, F.entry i j ∈ M) : F.scalarMatrixAlgebra ≤ M := by
  intro T hT
  apply F.mem_of_matrixEntries M hF
  intro i j
  obtain ⟨z,hz⟩ := F.scalarMatrixAlgebra_coefficient hT i j
  rw [hz, map_smul, cornerExtension_one, ← F.zero_zero]
  exact M.toStarSubalgebra.smul_mem (hF 0 0) z

/-- The matrix preparation can use this type I algebra without an AFD hypothesis. -/
theorem exists_injective_algebra_containing_entries_oai (M : VonNeumannAlgebra H)
    (hF : ∀ i j, F.entry i j ∈ M) :
    ∃ S : VonNeumannAlgebra H, S ≤ M ∧ IsInjective S ∧ ∀ i j, F.entry i j ∈ S :=
  ⟨F.scalarMatrixAlgebra,F.scalarMatrixAlgebra_le M hF,
    F.scalarMatrixAlgebra_isInjective,F.entry_mem_scalarMatrixAlgebra⟩

end FullMatrixCorner

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.FullMatrixCorner.exists_injective_algebra_containing_entries_oai.{u_1} := @OAI.KadisonKastler.FullMatrixCorner.exists_injective_algebra_containing_entries_oai.{u_1}
