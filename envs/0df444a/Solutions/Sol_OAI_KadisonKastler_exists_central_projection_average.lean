-- Prove2me | solution 1 for OAI.KadisonKastler.exists_central_projection_average
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:57:21.781884+00:00
-- url     : https://prove2.me/submissions/087bb6f0-0a5b-4bcb-9138-97c4d5234209

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Torsion.Field
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
import Mathlib.Analysis.Convex.Combination
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
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Banach
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
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
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
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
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
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveCountable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
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
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K064

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteProjectionAveraging
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Constructed finite-factor projection averages -/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] {M : VonNeumannAlgebra H}

omit [Nontrivial H] in
/-- The ambient operator order agrees with the algebraic projection order. -/
theorem ambient_projection_le {p q : AlgebraProjection M} (hpq : p ≤ q) :
    p.val.val ≤ q.val.val := by
  apply ((p.property.map M.toStarSubalgebra.subtype).le_iff_mul_eq_right
    (q.property.map M.toStarSubalgebra.subtype)).mpr
  exact congrArg Subtype.val hpq

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteInnerComposition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Composition and scalar invariance of finite inner averages -/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

namespace FiniteInnerAverage

theorem apply_scalar (A : FiniteInnerAverage M) (z : ℂ) :
    A.apply (z • (1 : H →L[ℂ] H)) = z • (1 : H →L[ℂ] H) := by
  have h (i : A.Index) : unitaryConj (ambientAlgebraUnitary (A.unitary i))
      (z • (1 : H →L[ℂ] H)) = z • (1 : H →L[ℂ] H) := by
    simp only [unitaryConj, mul_smul_comm, mul_one, smul_mul_assoc,
      Unitary.mul_star_self_of_mem (ambientAlgebraUnitary (A.unitary i)).property]
  change finiteAverage (fun i => unitaryConj (ambientAlgebraUnitary (A.unitary i))
    (z • (1 : H →L[ℂ] H))) = _
  simp only [h]
  exact finiteAverage_const _

end FiniteInnerAverage

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionSwapAverage
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Averaging a projection into half the identity by projection comparison -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- Orthogonal equivalent projections are exchanged by an ambient unitary. -/
theorem exists_unitary_swap_orthogonal_formula (v : PartialIsometry M)
    (ho : v.support.val * v.target.val = 0) :
    ∃ u : unitary (Algebra M),
      (u : Algebra M) * v.support.val * star (u : Algebra M) = v.target.val ∧
      (u : Algebra M) = v.val + star v.val + (1 - (v.support.val + v.target.val)) := by
  let p := v.support
  let q := v.target
  have hv : v.support = p := rfl
  have ht : v.target = q := rfl
  have hi : v.support.val * v.adjoint.support.val = 0 := by
    change v.support.val * v.target.val = 0
    rw [hv, ht]
    exact ho
  have hf : v.target.val * v.adjoint.target.val = 0 := by
    rw [PartialIsometry.adjoint_target, hv, ht]
    exact PartialIsometry.orthogonal_reverse p q ho
  let a := v.patch v.adjoint hi hf
  have hat : a.target = a.support := by
    apply Subtype.ext
    rw [PartialIsometry.patch_target, PartialIsometry.adjoint_target]
    change v.target.val + v.support.val = v.support.val + v.target.val
    exact add_comm _ _
  let c : AlgebraProjection M := ⟨1 - a.support.val, a.support.property.one_sub⟩
  have hac : a.support.val * (PartialIsometry.onProjection c).support.val = 0 :=
    a.support.property.mul_one_sub_self
  have hatc : a.target.val * (PartialIsometry.onProjection c).target.val = 0 := by
    rw [PartialIsometry.onProjection_target, hat]
    exact hac
  let z := a.patch (PartialIsometry.onProjection c) hac hatc
  have hzi : star z.val * z.val = 1 := by
    rw [z.initial]
    change a.support.val + (1 - a.support.val) = 1
    abel
  have hzt : z.val * star z.val = 1 := by
    change z.target.val = 1
    rw [PartialIsometry.patch_target, PartialIsometry.onProjection_target, hat]
    change a.support.val + (1 - a.support.val) = 1
    abel
  let u : unitary (Algebra M) := ⟨z.val, hzi, hzt⟩
  have hvz : v ≤ z := (v.le_patch v.adjoint hi hf).trans (a.le_patch _ hac hatc)
  have hup : (u : Algebra M) * p.val = v.val := by
    rw [← hv]
    exact hvz
  refine ⟨u, ?_, ?_⟩
  · calc
      (u : Algebra M) * p.val * star (u : Algebra M) =
        ((u : Algebra M) * p.val) * star ((u : Algebra M) * p.val) := by
          rw [star_mul, p.property.isSelfAdjoint.star_eq]
          calc
            _ = (u : Algebra M) * (p.val * p.val) * star (u : Algebra M) := by
              rw [p.property.isIdempotentElem.eq]
            _ = _ := by simp only [mul_assoc]
      _ = q.val := by rw [hup]; exact congrArg Subtype.val ht
  · rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CentralProjectionComparison
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Central separation of the remainders in projection comparison -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- A maximal partial isometry leaves no algebraic link between its two
remainder projections. This statement does not require scalar center. -/
theorem exists_partialIsometry_separated_remainders (p q : AlgebraProjection M) :
    ∃ (v : PartialIsometry M) (hp : v.support ≤ p) (hq : v.target ≤ q),
      ∀ a : Algebra M,
        (AlgebraProjection.remainder v.target q hq).val * a *
          (AlgebraProjection.remainder v.support p hp).val = 0 := by
  obtain ⟨v, hp, hq, hmax⟩ := PartialIsometry.traceFree_exists_maximal_between p q
  refine ⟨v, hp, hq, ?_⟩
  let r := AlgebraProjection.remainder v.support p hp
  let s := AlgebraProjection.remainder v.target q hq
  intro a
  by_contra ha
  obtain ⟨w, hwr, hws, hw0⟩ := exists_partialIsometry_of_link r s (s.val * a * r.val)
    (by rw [mul_assoc, r.property.isIdempotentElem.eq])
    (by rw [← mul_assoc, ← mul_assoc, s.property.isIdempotentElem.eq]) ha
  have hpw : v.support.val * w.support.val = 0 := by
    calc
      _ = v.support.val * (r.val * w.support.val) := by rw [hwr]
      _ = (v.support.val * r.val) * w.support.val := (mul_assoc _ _ _).symm
      _ = 0 := by rw [AlgebraProjection.remainder_orthogonal, zero_mul]
  have hqw : v.target.val * w.target.val = 0 := by
    calc
      _ = v.target.val * (s.val * w.target.val) := by rw [hws]
      _ = (v.target.val * s.val) * w.target.val := (mul_assoc _ _ _).symm
      _ = 0 := by rw [AlgebraProjection.remainder_orthogonal, zero_mul]
  let u := v.patch w hpw hqw
  have hup : u.support ≤ p := by
    change p.val * (v.support.val + w.support.val) = v.support.val + w.support.val
    rw [mul_add, hp, show p.val * w.support.val = w.support.val from
      hwr.trans (AlgebraProjection.remainder_le _ _ hp)]
  have huq : u.target ≤ q := by
    apply (u.target_le_iff_mul q).mpr
    change q.val * (v.val + w.val) = v.val + w.val
    rw [mul_add, (v.target_le_iff_mul q).mp hq,
      (w.target_le_iff_mul q).mp (hws.trans (AlgebraProjection.remainder_le _ _ hq))]
  have hvu : v ≤ u := v.le_patch w hpw hqw
  exact (v.patch_ne w hpw hqw hw0) (le_antisymm (hmax u hup huq hvu) hvu)

/-- One central projection separates the two unmatched remainders. -/
theorem exists_centrally_separated_comparison (p q : AlgebraProjection M) :
    ∃ (v : PartialIsometry M) (hp : v.support ≤ p) (hq : v.target ≤ q)
      (z : AlgebraProjection M),
      (∀ a : Algebra M, a * z.val = z.val * a) ∧
      AlgebraProjection.remainder v.support p hp ≤ z ∧
      AlgebraProjection.remainder v.target q hq ≤
        (⟨1 - z.val, z.property.one_sub⟩ : AlgebraProjection M) := by
  obtain ⟨v, hp, hq, hlink⟩ := exists_partialIsometry_separated_remainders p q
  let r := AlgebraProjection.remainder v.support p hp
  let s := AlgebraProjection.remainder v.target q hq
  let z := centralSupport r
  refine ⟨v, hp, hq, z, centralSupport_commutes r, le_centralSupport r, ?_⟩
  have hz : s.val * z.val = 0 := mul_centralSupport_eq_zero_of_no_links r s hlink
  have hz' : z.val * s.val = 0 := PartialIsometry.orthogonal_reverse s z hz
  change (1 - z.val) * s.val = s.val
  rw [sub_mul, one_mul, hz', sub_zero]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CentralProjectionAveraging
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.ScalarInvariantMean.conjugationFamily_apply _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.StandardTracialPosition.conjugation_algebraVector _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Central bounds for a two-unitary projection average -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] {M : VonNeumannAlgebra H}

/-- Swapping the matched parts fixes every projection orthogonal to both. -/
theorem swap_formula_fixes_projection (v : PartialIsometry M)
    (u : unitary (Algebra M))
    (hu : (u : Algebra M) = v.val + star v.val + (1 - (v.support.val + v.target.val)))
    (r : AlgebraProjection M)
    (hr : v.support.val * r.val = 0) (ht : v.target.val * r.val = 0) :
    (u : Algebra M) * r.val * star (u : Algebra M) = r.val := by
  have hvr : v.val * r.val = 0 := v.mul_eq_zero (PartialIsometry.onProjection r)
    (by simpa only [PartialIsometry.onProjection_target] using hr)
  have hsr : star v.val * r.val = 0 :=
    v.adjoint.mul_eq_zero (PartialIsometry.onProjection r)
      (by
        rw [PartialIsometry.onProjection_target]
        change v.target.val * r.val = 0
        exact ht)
  have hur : (u : Algebra M) * r.val = r.val := by
    rw [hu, add_mul, add_mul, hvr, hsr, zero_add, sub_mul, one_mul, add_mul, hr, ht]
    simp
  calc
    (u : Algebra M) * r.val * star (u : Algebra M) =
        ((u : Algebra M) * r.val) * star ((u : Algebra M) * r.val) := by
      rw [star_mul, r.property.isSelfAdjoint.star_eq]
      calc
        _ = (u : Algebra M) * (r.val * r.val) * star (u : Algebra M) := by
          rw [r.property.isIdempotentElem.eq]
        _ = _ := by simp only [mul_assoc]
    _ = r.val := by rw [hur, r.property.isSelfAdjoint.star_eq, r.property.isIdempotentElem.eq]

/-- Matched positive and negative spectral parts give complementary upper
bounds measured by one central projection. -/
theorem exists_central_projection_average_oai (p : AlgebraProjection M) :
    ∃ (A : FiniteInnerAverage M) (z : AlgebraProjection M),
      (∀ a : Algebra M, a * z.val = z.val * a) ∧
      A.apply p.val.val ≤ (1 / 2 : ℝ) • (1 + z.val.val) ∧
      A.apply (1 - p.val.val) ≤ (1 / 2 : ℝ) • (2 • (1 : H →L[ℂ] H) - z.val.val) := by
  let q : AlgebraProjection M := ⟨1 - p.val, p.property.one_sub⟩
  obtain ⟨v, hp, hq, z, hz, hrz, hsz⟩ := exists_centrally_separated_comparison p q
  let r := AlgebraProjection.remainder v.support p hp
  let s := AlgebraProjection.remainder v.target q hq
  have hpq : p.val * q.val = 0 := p.property.mul_one_sub_self
  have ho : v.support.val * v.target.val = 0 :=
    projection_orthogonal_of_le hpq hp hq
  obtain ⟨u, hu, huf⟩ := exists_unitary_swap_orthogonal_formula v ho
  have hvr : v.support.val * r.val = 0 := AlgebraProjection.remainder_orthogonal _ _ hp
  have htr : v.target.val * r.val = 0 := projection_orthogonal_of_le
    (PartialIsometry.orthogonal_reverse p q hpq) hq (AlgebraProjection.remainder_le _ _ hp)
  have hur := swap_formula_fixes_projection v u huf r hvr htr
  have hup : (u : Algebra M) * p.val * star (u : Algebra M) = v.target.val + r.val := by
    have he : p.val = v.support.val + r.val := by
      change p.val = v.support.val + (p.val - v.support.val)
      abel
    rw [he, mul_add, add_mul, hu, hur]
  let A : FiniteInnerAverage M := {
    Index := Bool
    fintype := inferInstance
    nonempty := inferInstance
    unitary b := if b then u else 1 }
  have hA : A.apply p.val.val = (1 / 2 : ℝ) • (1 + r.val.val - s.val.val) := by
    change (Fintype.card Bool : ℂ)⁻¹ •
      (∑ b : Bool, unitaryConj (ambientAlgebraUnitary (if b then u else 1)) p.val.val) = _
    rw [Fintype.sum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hu' : unitaryConj (ambientAlgebraUnitary u) p.val.val = v.target.val.val + r.val.val :=
      congrArg Subtype.val hup
    rw [hu']
    have h1 : unitaryConj (ambientAlgebraUnitary (1 : unitary (Algebra M))) p.val.val = p.val.val := by
      change (1 : H →L[ℂ] H) * p.val.val * star (1 : H →L[ℂ] H) = _
      simp
    rw [h1]
    have he : v.target.val.val + r.val.val + p.val.val = 1 + r.val.val - s.val.val := by
      change v.target.val.val + r.val.val + p.val.val =
        1 + r.val.val - ((1 - p.val.val) - v.target.val.val)
      abel
    rw [he]
    rw [← Complex.coe_smul]
    norm_num
  have hB : A.apply (1 - p.val.val) = (1 / 2 : ℝ) • (1 - r.val.val + s.val.val) := by
    rw [A.apply_sub, show A.apply 1 = 1 by simpa using A.apply_scalar 1, hA]
    module
  have hr0 : (0 : H →L[ℂ] H) ≤ r.val.val :=
    (r.property.map M.toStarSubalgebra.subtype).nonneg
  have hs0 : (0 : H →L[ℂ] H) ≤ s.val.val :=
    (s.property.map M.toStarSubalgebra.subtype).nonneg
  have hr : r.val.val ≤ z.val.val := ambient_projection_le hrz
  have hs : s.val.val ≤ 1 - z.val.val := ambient_projection_le hsz
  refine ⟨A, z, hz, ?_, ?_⟩
  · rw [hA]
    apply smul_le_smul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    exact (sub_le_self _ hs0).trans (add_le_add le_rfl hr)
  · rw [hB]
    apply smul_le_smul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have h := add_le_add (sub_le_self (1 : H →L[ℂ] H) hr0) hs
    convert h using 1 <;> first | (with_reducible_and_instances rfl) | (module)

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.exists_central_projection_average_oai.{u_1} := @OAI.KadisonKastler.exists_central_projection_average_oai.{u_1}
