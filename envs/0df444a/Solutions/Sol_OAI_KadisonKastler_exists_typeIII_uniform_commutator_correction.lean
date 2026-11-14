-- Prove2me | solution 1 for OAI.KadisonKastler.exists_typeIII_uniform_commutator_correction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:08:06.527937+00:00
-- url     : https://prove2.me/submissions/05de6324-ddd1-47b8-96dc-c7073c5253a5

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
import Mathlib.Analysis.Normed.Operator.NNNorm
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
import Definitions.Def_Q260K028
import Definitions.Def_Q260K030
import Theorems.Thm_OAI_KadisonKastler_typeIII_normUltraproduct_simple

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormUltraproduct
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.algebraCStarAlgebra _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.NonsingularAction.operatorAction_constant _root_.OAI.KadisonKastler.NonsingularAction.operatorEquiv_apply _root_.OAI.KadisonKastler.NonsingularAction.restrictedOperatorAction_coe _root_.OAI.KadisonKastler.ScalarBoundaryMean.operatorMean_apply _root_.OAI.KadisonKastler.WeakOperatorField.pullback_constant _root_.OAI.KadisonKastler.WeakOperatorField.pullback_id _root_.OAI.KadisonKastler.constantFieldRepresentation_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.normProductMap_apply _root_.OAI.KadisonKastler.normUltraproductInducedMap_apply_map _root_.OAI.KadisonKastler.operatorFieldFamilyInclusion_apply _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceContinuous_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.tracialSequenceValue_one _root_.OAI.KadisonKastler.varyingSequenceHom_apply _root_.OAI.KadisonKastler.varyingUnitarySequence_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The actual norm ultraproduct for the infinitesimal normalizer argument

The null sequences form a closed star ideal in the bounded product. Its
C-star quotient is the norm ultraproduct used in the infinitesimal
normalizer argument.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable (B : ℕ → Type*) [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]

attribute [local instance] OAI.KadisonKastler.instPartialOrderSubtypePreLpNatMemAddSubgroupVaryingBoundedSequence
attribute [local instance] OAI.KadisonKastler.instStarOrderedRingSubtypePreLpNatMemAddSubgroupVaryingBoundedSequence
/-- Taking the self-adjoint part supplies actual self-adjoint sequence
representatives for the implementer produced by Sakai's theorem. -/
theorem exists_selfAdjoint_normUltraproduct_lift (ω : Ultrafilter ℕ)
    (a : NormUltraproduct B ω) (ha : IsSelfAdjoint a) :
    ∃ x : VaryingBoundedSequence B, IsSelfAdjoint x ∧ normUltraproductMap B ω x = a := by
  obtain ⟨x, hx⟩ := normUltraproductMap_surjective B ω a
  refine ⟨(1 / 2 : ℂ) • (x + star x), ?_, ?_⟩
  · exact (show IsSelfAdjoint (1 / 2 : ℂ) by norm_num [isSelfAdjoint_iff]).smul
      (IsSelfAdjoint.add_star_self x)
  · rw [map_smul, map_add, map_star, hx, ha.star_eq, ← two_smul ℂ a, smul_smul]
    norm_num

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormUltraproductMaps
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Coordinate embeddings induce faithful norm-ultraproduct embeddings -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {B C : ℕ → Type*} [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]
  [∀ j, CStarAlgebra (C j)] [∀ j, Nontrivial (C j)]

theorem normUltraproductInducedMap_injective (φ : ∀ j, B j →⋆ₐ[ℂ] C j)
    (hφ : ∀ j, Function.Injective (φ j)) (ω : Ultrafilter ℕ) :
    Function.Injective (normUltraproductInducedMap φ ω) := by
  intro a b hab
  have hz : normUltraproductInducedMap φ ω (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨x, hx⟩ := normUltraproductMap_surjective B ω (a - b)
  have hzero : normUltraproductMap C ω (normProductMap φ x) = 0 := by
    rw [← normUltraproductInducedMap_apply_map, hx]
    exact hz
  have hnull := (normUltraproductMap_eq_zero_iff C ω _).mp hzero
  have hnorm : (fun j => ‖normProductMap φ x j‖) = (fun j => ‖x j‖) := by
    funext j
    exact NonUnitalStarAlgHom.norm_map (φ j) (hφ j) (x j)
  have hnullx : NormNullSequence B ω x := by
    change Tendsto (fun j => ‖x j‖) (ω : Filter ℕ) (𝓝 0)
    rw [← hnorm]
    exact hnull
  exact sub_eq_zero.mp (hx ▸ (normUltraproductMap_eq_zero_iff B ω x).mpr hnullx)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedSimpleDerivation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Sakai's inner-derivation theorem, in its needed unital form

S. Sakai, *Derivations of simple C*-algebras II*, Bulletin de la Société
Mathématique de France 99 (1971), 259--263, §2, unnumbered theorem on p.260,
together with the unital specialization explained in §1 on p.259.
DOI: 10.24033/bsmf.1719. The only input is innerness of bounded derivations
of a simple unital C-star algebra. Self-adjointness of an implementer is
derived below, not included in that input.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

/-- A commutator with a self-adjoint ambient element is anti-star
compatible. Taking the real part of any inner implementer preserves it. -/
theorem selfAdjoint_inner_implementer (D : A →L[ℂ] A)
    (hstar : ∀ x, D (star x) = -star (D x))
    {a : A} (ha : ∀ x, D x = a * x - x * a) :
    ∃ b : A, IsSelfAdjoint b ∧ ∀ x, D x = b * x - x * b := by
  have has : ∀ x, D x = star a * x - x * star a := by
    intro x
    have h := congrArg star (ha (star x))
    rw [hstar, star_neg, star_star, star_sub, star_mul, star_mul, star_star] at h
    exact neg_injective (by simpa only [neg_sub] using h)
  refine ⟨(1 / 2 : ℂ) • (a + star a),
    (show IsSelfAdjoint (1 / 2 : ℂ) by norm_num [isSelfAdjoint_iff]).smul
      (IsSelfAdjoint.add_star_self a), ?_⟩
  intro x
  calc
    D x = (1 / 2 : ℂ) • (D x + D x) := by
      rw [← two_smul ℂ (D x), smul_smul]
      norm_num
    _ = (1 / 2 : ℂ) • ((a * x - x * a) + (star a * x - x * star a)) := by
      conv_lhs => arg 2; arg 1; rw [ha]
      conv_lhs => arg 2; arg 2; rw [has]
    _ = ((1 / 2 : ℂ) • (a + star a)) * x -
        x * ((1 / 2 : ℂ) • (a + star a)) := by
      simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, smul_sub, smul_add]
      abel

theorem exists_selfAdjoint_implementer_of_published
    [Nontrivial A] (hPublished : PublishedSimpleDerivationInner.{u})
    (hSimple : CStarSimple A) (D : A →L[ℂ] A)
    (hderiv : ∀ x y, D (x * y) = D x * y + x * D y)
    (hstar : ∀ x, D (star x) = -star (D x)) :
    ∃ a : A, IsSelfAdjoint a ∧ ∀ x, D x = a * x - x * a := by
  obtain ⟨a, ha⟩ := hPublished A hSimple D hderiv
  exact selfAdjoint_inner_implementer D hstar ha

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RestrictedInnerDerivation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Restricting a spatial commutator to an invariant C-star subalgebra

An injective star homomorphism reflects the algebraic identities and the
norm bound. Thus invariance under an ambient commutator gives an actual
bounded derivation on the source algebra.
-/

namespace KadisonKastler

noncomputable section

universe u v

variable {A : Type u} {E : Type v} [CStarAlgebra A] [CStarAlgebra E]

theorem exists_restricted_inner_derivation (φ : A →⋆ₐ[ℂ] E)
    (hφ : Function.Injective φ) (T : E)
    (hrange : ∀ x : A, ∃ y : A, φ y = T * φ x - φ x * T) :
    ∃ D : A →L[ℂ] A,
      (∀ x, φ (D x) = T * φ x - φ x * T) ∧
      (∀ x y, D (x * y) = D x * y + x * D y) ∧
      (IsSelfAdjoint T → ∀ x, D (star x) = -star (D x)) := by
  choose f hf using hrange
  let L : A →ₗ[ℂ] A :=
    { toFun := f
      map_add' := by
        intro x y
        apply hφ
        simp only [hf, map_add]
        noncomm_ring
      map_smul' := by
        intro c x
        apply hφ
        simp only [hf, map_smul, smul_mul_assoc, mul_smul_comm, smul_sub]
        rfl }
  have hL : ∀ x, φ (L x) = T * φ x - φ x * T := hf
  have hbound : ∀ x, ‖L x‖ ≤ (2 * ‖T‖) * ‖x‖ := by
    intro x
    rw [← NonUnitalStarAlgHom.norm_map φ hφ (L x), hL]
    calc
      ‖T * φ x - φ x * T‖ ≤ ‖T * φ x‖ + ‖φ x * T‖ := norm_sub_le _ _
      _ ≤ ‖T‖ * ‖φ x‖ + ‖φ x‖ * ‖T‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = (2 * ‖T‖) * ‖x‖ := by
        rw [NonUnitalStarAlgHom.norm_map φ hφ x]
        ring
  let D := L.mkContinuous (2 * ‖T‖) hbound
  have hD : ∀ x, φ (D x) = T * φ x - φ x * T := hL
  refine ⟨D, hD, ?_, ?_⟩
  · intro x y
    apply hφ
    simp only [map_add, map_mul, hD]
    noncomm_ring
  · intro hT x
    apply hφ
    simp only [map_neg, map_star, hD, star_sub, star_mul, hT.star_eq, neg_sub]

theorem exists_selfAdjoint_ambient_correction
    [Nontrivial A] (hPublished : PublishedSimpleDerivationInner.{u})
    (hSimple : CStarSimple A) (φ : A →⋆ₐ[ℂ] E)
    (hφ : Function.Injective φ) (T : E) (hT : IsSelfAdjoint T)
    (hrange : ∀ x : A, ∃ y : A, φ y = T * φ x - φ x * T) :
    ∃ a : A, IsSelfAdjoint a ∧ ∀ x : A, Commute (T - φ a) (φ x) := by
  obtain ⟨D, hD, hderiv, hstar⟩ := exists_restricted_inner_derivation φ hφ T hrange
  obtain ⟨a, ha, hDa⟩ := exists_selfAdjoint_implementer_of_published
    hPublished hSimple D hderiv (hstar hT)
  refine ⟨a, ha, fun x => ?_⟩
  have h := hD x
  rw [hDa, map_sub, map_mul, map_mul] at h
  change (T - φ a) * φ x = φ x * (T - φ a)
  rw [sub_mul, mul_sub]
  calc
    T * φ x - φ a * φ x = (T * φ x - φ x * T) -
        (φ a * φ x - φ x * φ a) + (φ x * T - φ x * φ a) := by abel
    _ = φ x * T - φ x * φ a := by rw [← h, sub_self, zero_add]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UniformNormDetection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded-sequence tests detect a uniform operator-norm limit

This is the diagonal choice in the infinitesimal normalizer argument:
equality of derivations on every element of the norm ultraproduct forces
their coordinate operator norms to tend to zero.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {B C : ℕ → Type*} [∀ j, CStarAlgebra (B j)]
  [∀ j, CStarAlgebra (C j)]

theorem exists_unitBall_half_norm_witness (j : ℕ) (D : B j →L[ℂ] C j) :
    ∃ x : B j, ‖x‖ ≤ 1 ∧ ‖D‖ ≤ 2 * ‖D x‖ := by
  by_cases hD : ‖D‖ = 0
  · exact ⟨0, by simp, by simp [hD]⟩
  · have hp : 0 < ‖D‖ := (norm_nonneg D).lt_of_ne' hD
    obtain ⟨x, hx, hDx⟩ := D.exists_lt_apply_of_lt_opNorm (by linarith : ‖D‖ / 2 < ‖D‖)
    exact ⟨x, hx.le, by linarith⟩

theorem tendsto_opNorm_zero_of_bounded_sequence_tests (ω : Ultrafilter ℕ)
    (D : ∀ j, B j →L[ℂ] C j)
    (hD : ∀ x : VaryingBoundedSequence B,
      Tendsto (fun j => ‖D j (x j)‖) (ω : Filter ℕ) (𝓝 0)) :
    Tendsto (fun j => ‖D j‖) (ω : Filter ℕ) (𝓝 0) := by
  choose x hx hDx using fun j => exists_unitBall_half_norm_witness j (D j)
  let X : VaryingBoundedSequence B :=
    ⟨x, memℓp_infty ⟨1, by rintro _ ⟨j, rfl⟩; exact hx j⟩⟩
  apply squeeze_zero (fun j => norm_nonneg (D j)) hDx
  simpa only [mul_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) (ω : Filter ℕ) (𝓝 2)).mul (hD X)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormUltraproductDerivation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Innerness in the norm ultraproduct gives uniform commutator control

This proves the analytic core of the infinitesimal-normalizer contradiction.
The hypotheses are simplicity of the type III ultraproduct and invariance
under the commutator.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u v

variable {A : Type u} {E : Type v} [CStarAlgebra A] [CStarAlgebra E]

variable {B : ℕ → Type u} {C : ℕ → Type v}
  [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]
  [∀ j, CStarAlgebra (C j)] [∀ j, Nontrivial (C j)]

theorem normUltraproduct_commutator_in_range
    (φ : ∀ j, B j →⋆ₐ[ℂ] C j) (ω : Ultrafilter ℕ)
    (T : VaryingBoundedSequence C)
    (hrange : ∀ x : VaryingBoundedSequence B,
      ∃ y : VaryingBoundedSequence B,
        NormNullSequence C ω (T * normProductMap φ x - normProductMap φ x * T -
          normProductMap φ y)) :
    ∀ x : NormUltraproduct B ω, ∃ y : NormUltraproduct B ω,
      normUltraproductInducedMap φ ω y =
        normUltraproductMap C ω T * normUltraproductInducedMap φ ω x -
          normUltraproductInducedMap φ ω x * normUltraproductMap C ω T := by
  intro x
  obtain ⟨X, rfl⟩ := normUltraproductMap_surjective B ω x
  obtain ⟨Y, hY⟩ := hrange X
  refine ⟨normUltraproductMap B ω Y, ?_⟩
  have hzero := (normUltraproductMap_eq_zero_iff C ω _).mpr hY
  rw [map_sub, map_sub, map_mul, map_mul] at hzero
  simpa only [normUltraproductInducedMap_apply_map] using (sub_eq_zero.mp hzero).symm

/-- Equality of the two derivations gives a single bounded self-adjoint
coordinate correction whose commutator norms converge uniformly to zero. -/
theorem exists_uniform_commutator_correction
    (hPublished : PublishedSimpleDerivationInner.{u})
    (φ : ∀ j, B j →⋆ₐ[ℂ] C j) (hφ : ∀ j, Function.Injective (φ j))
    (ω : Ultrafilter ℕ) (hSimple : CStarSimple (NormUltraproduct B ω))
    (T : VaryingBoundedSequence C) (hT : IsSelfAdjoint T)
    (hrange : ∀ x : VaryingBoundedSequence B,
      ∃ y : VaryingBoundedSequence B,
        NormNullSequence C ω (T * normProductMap φ x - normProductMap φ x * T -
          normProductMap φ y)) :
    ∃ a : VaryingBoundedSequence B, IsSelfAdjoint a ∧
      Tendsto (fun j => ‖commutatorAlong (φ j) (T j - φ j (a j))‖)
        (ω : Filter ℕ) (𝓝 0) := by
  let Φ := normUltraproductInducedMap φ ω
  let t := normUltraproductMap C ω T
  have ht : IsSelfAdjoint t := by
    change star (normUltraproductMap C ω T) = normUltraproductMap C ω T
    rw [← map_star, hT.star_eq]
  obtain ⟨a, ha, hcomm⟩ := exists_selfAdjoint_ambient_correction hPublished hSimple Φ
    (normUltraproductInducedMap_injective φ hφ ω) t ht
    (normUltraproduct_commutator_in_range φ ω T hrange)
  obtain ⟨aSeq, haSeq, haLift⟩ := exists_selfAdjoint_normUltraproduct_lift B ω a ha
  refine ⟨aSeq, haSeq, ?_⟩
  apply tendsto_opNorm_zero_of_bounded_sequence_tests ω
  intro X
  have hnull : NormNullSequence C ω
      ((T - normProductMap φ aSeq) * normProductMap φ X -
        normProductMap φ X * (T - normProductMap φ aSeq)) := by
    apply (normUltraproductMap_eq_zero_iff C ω _).mp
    rw [map_sub, map_mul, map_mul, map_sub,
      ← normUltraproductInducedMap_apply_map,
      ← normUltraproductInducedMap_apply_map, haLift]
    exact sub_eq_zero.mpr (hcomm (normUltraproductMap B ω X)).eq
  exact hnull

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ApproximateCommutatorRange
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Approximate invariance gives exact invariance in the norm ultraproduct -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {B C : ℕ → Type*} [∀ j, CStarAlgebra (B j)] [∀ j, Nontrivial (B j)]
  [∀ j, CStarAlgebra (C j)] [∀ j, Nontrivial (C j)]

theorem exists_normNull_commutator_approximation
    (φ : ∀ j, B j →⋆ₐ[ℂ] C j) (hφ : ∀ j, Function.Injective (φ j))
    (ω : Ultrafilter ℕ)
    (T : VaryingBoundedSequence C) (ε : ℕ → ℝ)
    (hε : Tendsto ε (ω : Filter ℕ) (𝓝 0))
    (hε0 : ∀ j, 0 ≤ ε j) {K : ℝ} (hK : ∀ j, ε j ≤ K)
    (happrox : ∀ j (x : B j), ∃ y : B j,
      ‖T j * φ j x - φ j x * T j - φ j y‖ ≤ ε j * ‖x‖)
    (X : VaryingBoundedSequence B) :
    ∃ Y : VaryingBoundedSequence B,
      NormNullSequence C ω (T * normProductMap φ X - normProductMap φ X * T -
        normProductMap φ Y) := by
  choose y hy using fun j => happrox j (X j)
  have hX : ∀ j, ‖φ j (X j)‖ ≤ ‖X‖ := fun j =>
    (NonUnitalStarAlgHom.norm_apply_le (φ j) _).trans (varyingSequence_norm_apply_le X j)
  have hcomm : ∀ j, ‖T j * φ j (X j) - φ j (X j) * T j‖ ≤ 2 * ‖T‖ * ‖X‖ := by
    intro j
    calc
      _ ≤ ‖T j‖ * ‖φ j (X j)‖ + ‖φ j (X j)‖ * ‖T j‖ :=
        (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ ‖T‖ * ‖X‖ + ‖X‖ * ‖T‖ := by
        gcongr <;> first | exact hX j | exact varyingSequence_norm_apply_le T j
      _ = 2 * ‖T‖ * ‖X‖ := by ring
  have hyBound : ∀ j, ‖y j‖ ≤ (2 * ‖T‖ + K) * ‖X‖ := by
    intro j
    rw [← NonUnitalStarAlgHom.norm_map (φ j) (hφ j) (y j)]
    calc
      ‖φ j (y j)‖ ≤ ‖T j * φ j (X j) - φ j (X j) * T j‖ +
          ‖T j * φ j (X j) - φ j (X j) * T j - φ j (y j)‖ := by
        simpa only [sub_sub_cancel] using
          norm_sub_le (T j * φ j (X j) - φ j (X j) * T j)
            (T j * φ j (X j) - φ j (X j) * T j - φ j (y j))
      _ ≤ 2 * ‖T‖ * ‖X‖ + ε j * ‖X j‖ := add_le_add (hcomm j) (hy j)
      _ ≤ 2 * ‖T‖ * ‖X‖ + K * ‖X‖ := by
        exact add_le_add le_rfl (mul_le_mul (hK j) (varyingSequence_norm_apply_le X j)
          (norm_nonneg _) ((hε0 j).trans (hK j)))
      _ = (2 * ‖T‖ + K) * ‖X‖ := by ring
  let Y : VaryingBoundedSequence B :=
    ⟨y, memℓp_infty ⟨(2 * ‖T‖ + K) * ‖X‖, by
      rintro _ ⟨j, rfl⟩
      exact hyBound j⟩⟩
  refine ⟨Y, ?_⟩
  apply squeeze_zero (fun j => norm_nonneg _)
    (fun j => (hy j).trans (mul_le_mul_of_nonneg_left
      (varyingSequence_norm_apply_le X j) (hε0 j)))
  simpa only [zero_mul] using hε.mul_const ‖X‖

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIIIUltraproduct
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Simplicity and commutator correction for type III norm ultraproducts

Spectral cuts, projection comparison, and Sakai innerness give simplicity
of the norm ultraproduct and a uniform coordinate correction for its
invariant derivations.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable {K : ℕ → Type u} [∀ j, NormedAddCommGroup (K j)]
  [∀ j, InnerProductSpace ℂ (K j)] [∀ j, CompleteSpace (K j)]
  [∀ j, TopologicalSpace.SeparableSpace (K j)]

theorem exists_typeIII_uniform_commutator_correction_oai
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (hSakai : PublishedSimpleDerivationInner.{u})
    (M : ∀ j, VonNeumannAlgebra (K j)) (hM : ∀ j, TypeIIIFactor (M j))
    (ω : Ultrafilter ℕ) (T : VaryingBoundedSequence (fun j => K j →L[ℂ] K j))
    (hT : IsSelfAdjoint T) (ε : ℕ → ℝ)
    (hε : Tendsto ε (ω : Filter ℕ) (𝓝 0)) (hε0 : ∀ j, 0 ≤ ε j)
    {R : ℝ} (hR : ∀ j, ε j ≤ R)
    (happrox : ∀ j (x : Algebra (M j)), ∃ y : Algebra (M j),
      ‖T j * (x : K j →L[ℂ] K j) - (x : K j →L[ℂ] K j) * T j -
        (y : K j →L[ℂ] K j)‖ ≤ ε j * ‖x‖) :
    ∃ a : VaryingBoundedSequence (fun j => Algebra (M j)), IsSelfAdjoint a ∧
      Tendsto (fun j => ‖commutatorAlong (M j).toStarSubalgebra.subtype
        (T j - (a j : K j →L[ℂ] K j))‖) (ω : Filter ℕ) (𝓝 0) := by
  let : ∀ j, Nontrivial (Algebra (M j)) := fun j => (hM j).algebraNontrivial
  let : ∀ j, Nontrivial (K j →L[ℂ] K j) := fun j => ⟨⟨1, 0, (hM j).nonzero⟩⟩
  let φ := fun j => (M j).toStarSubalgebra.subtype
  have hφ : ∀ j, Function.Injective (φ j) := fun _ => Subtype.val_injective
  apply exists_uniform_commutator_correction hSakai φ hφ ω
    (typeIII_normUltraproduct_simple hSpectral hCompare M hM ω) T hT
  exact exists_normNull_commutator_approximation φ hφ ω T ε hε hε0 hR happrox

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.exists_typeIII_uniform_commutator_correction_oai.{u} := @OAI.KadisonKastler.exists_typeIII_uniform_commutator_correction_oai.{u}
