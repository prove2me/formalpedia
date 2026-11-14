-- Prove2me | solution 1 for OAI.KadisonKastler.first_leg_field_of_product_centralizer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:25:56.70983+00:00
-- url     : https://prove2.me/submissions/e50d0de9-ec4a-4cf1-a732-b422f054e7c9

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
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Continuous
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
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
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
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
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
import Definitions.Def_Q260K019
import Definitions.Def_Q260K064
import Theorems.Thm_OAI_KadisonKastler_spatial_relative_commutant_of_local_swaps

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StrongCommutantTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-- d13f23b's `TopologicalSpace.exists_countable_dense_subset` (port compat, absent from our Mathlib). -/
private theorem ecdsCompat_p1 {α : Type*} [TopologicalSpace α] (s : Set α) [TopologicalSpace.SeparableSpace s] :
    ∃ t : Set α, t.Countable ∧ t ⊆ s ∧ s ⊆ closure t := by
  obtain ⟨t, ct, dt⟩ := TopologicalSpace.exists_countable_dense s
  exact ⟨Subtype.val '' t, ct.image _, by simp, fun x hx ↦ closure_subtype.1 (dt ⟨x, hx⟩)⟩

/-! # Countable strong-operator tests for commutation

On a uniformly bounded set of operators, convergence on a countable dense
set of vectors implies convergence on every vector. A countable dense set
of coordinate sequences therefore supplies all commutant tests.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Every contraction-valued set on a separable space has a countable
subset that approximates each of its elements strongly by a sequence. -/
theorem exists_countable_strong_dense_contractions [SeparableSpace H]
    (S : Set (H →L[ℂ] H)) (hS : ∀ T ∈ S, ‖T‖ ≤ 1) :
    ∃ E : Set (H →L[ℂ] H), E.Countable ∧ E ⊆ S ∧
      ∀ T ∈ S, ∃ A : ℕ → H →L[ℂ] H,
        (∀ n, A n ∈ E) ∧ ∀ ξ, Tendsto (fun n => A n ξ) atTop (𝓝 (T ξ)) := by
  obtain ⟨v, hv⟩ := exists_dense_seq (α := H)
  let coordinates : (H →L[ℂ] H) → ℕ → H := fun A n => A (v n)
  obtain ⟨D, hDc, hDsub, hDdense⟩ := ecdsCompat_p1 (coordinates '' S)
  choose lift hliftS hlift using fun z : D => hDsub z.property
  let E : Set (H →L[ℂ] H) := Set.range lift
  have hEc : E.Countable := by
    let := hDc.to_subtype
    exact Set.countable_range lift
  have hES : E ⊆ S := by
    rintro T ⟨z, rfl⟩
    exact hliftS z
  refine ⟨E, hEc, hES, ?_⟩
  intro T hT
  obtain ⟨z, hz, hzt⟩ := mem_closure_iff_seq_limit.mp (hDdense ⟨T, hT, rfl⟩)
  let A : ℕ → H →L[ℂ] H := fun n => lift ⟨z n, hz n⟩
  have hAE (n : ℕ) : A n ∈ E := ⟨⟨z n, hz n⟩, rfl⟩
  refine ⟨A, hAE, ?_⟩
  apply tendsto_apply_of_dense_contractions v hv A T
    (fun n => hS (A n) (hES (hAE n))) (hS T hT)
  intro j
  have ht := tendsto_pi_nhds.mp hzt j
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  exact congrFun (hlift ⟨z n, hz n⟩) j

/-- Commutation with a fixed bounded operator is closed under strong
convergence. -/
theorem commute_of_strong_tendsto (A T : H →L[ℂ] H) (B : ℕ → H →L[ℂ] H)
    (hB : ∀ ξ, Tendsto (fun n => B n ξ) atTop (𝓝 (T ξ)))
    (hcomm : ∀ n, Commute A (B n)) : Commute A T := by
  apply ContinuousLinearMap.ext
  intro ξ
  have hl := (A.continuous.tendsto (T ξ)).comp (hB ξ)
  change Tendsto (fun n => A (B n ξ)) atTop (𝓝 (A (T ξ))) at hl
  have hr := hB (A ξ)
  have he : (fun n => A (B n ξ)) = fun n => B n (A ξ) := by
    funext n
    exact congrArg (fun U : H →L[ℂ] H => U ξ) (hcomm n).eq
  rw [he] at hl
  exact tendsto_nhds_unique hl hr

/-- Countably many operators determine the entire commutant of an
arbitrary contraction-valued set. -/
theorem exists_countable_commutant_tests [SeparableSpace H]
    (S : Set (H →L[ℂ] H)) (hS : ∀ T ∈ S, ‖T‖ ≤ 1) :
    ∃ E : Set (H →L[ℂ] H), E.Countable ∧ E ⊆ S ∧
      ∀ A : H →L[ℂ] H, (∀ T ∈ E, Commute A T) ↔ ∀ T ∈ S, Commute A T := by
  obtain ⟨E, hEc, hES, hE⟩ := exists_countable_strong_dense_contractions S hS
  refine ⟨E, hEc, hES, fun A => ⟨?_, ?_⟩⟩
  · intro hcomm T hT
    obtain ⟨B, hBE, hBT⟩ := hE T hT
    exact commute_of_strong_tendsto A T B hBT (fun n => hcomm (B n) (hBE n))
  · exact fun hcomm T hT => hcomm T (hES hT)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UnitBallClosure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Unit balls in norm closures of complex linear subspaces

Radial contraction keeps approximants in their original subspace. It
proves the norm-density statement needed for the separable test algebras.
-/

namespace KadisonKastler

noncomputable section

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]

theorem unitBallClip_norm_le (x : B) : ‖unitBallClip x‖ ≤ 1 := by
  have hp : 0 < max 1 ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [unitBallClip, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hp.le), inv_mul_eq_div]
  exact (div_le_one hp).mpr (le_max_right _ _)

theorem unitBallClip_mem (S : Submodule ℂ B) {x : B} (hx : x ∈ S) :
    unitBallClip x ∈ S := S.smul_mem _ hx

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreFields
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.conjugationFamily_apply _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded field multiplication and constant translation-fixed fields

Bounded measurable operator fields act on the actual vector-valued `L²`
space. Finite-measure indicator tests recover their coefficients, so this
action is faithful modulo almost-everywhere equality. A decomposable
operator commuting with every real translation is a constant operator.
No decomposability assertion for an arbitrary operator is assumed here.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Indicator tests recover each vector coefficient of an operator field
on a finite-measure set. -/
theorem RepresentsOperatorField.eval_eq_ae_on {μ : Measure X}
    {F G : X → H →L[ℂ] H} {T : Lp H 2 μ →L[ℂ] Lp H 2 μ}
    (hF : RepresentsOperatorField μ F T) (hG : RepresentsOperatorField μ G T)
    {s : Set X} (hs : MeasurableSet s) (hfinite : μ s ≠ ∞) (ξ : H) :
    ∀ᵐ t ∂μ, t ∈ s → F t ξ = G t ξ := by
  let f : Lp H 2 μ := indicatorConstLp 2 hs hfinite ξ
  filter_upwards [hF f, hG f,
    (indicatorConstLp_coeFn_mem (p := 2) (hs := hs) (hμs := hfinite) (c := ξ))]
    with t hf hg hξ
  intro ht
  rw [hξ ht] at hf hg
  exact hf.symm.trans hg

omit [CompleteSpace H] in
/-- Equality of actual real-line multiplication operators recovers each
vector value almost everywhere. -/
theorem RepresentsOperatorField.eval_eq_ae_real
    {F G : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T) (hG : RepresentsOperatorField volume G T)
    (ξ : H) : (fun t => F t ξ) =ᵐ[volume] fun t => G t ξ := by
  have hall : ∀ᵐ t : ℝ ∂volume, ∀ n : ℕ,
      t ∈ Set.Icc (-(n : ℝ)) (n : ℝ) → F t ξ = G t ξ := by
    apply ae_all_iff.mpr
    intro n
    exact hF.eval_eq_ae_on hG measurableSet_Icc (by simp) ξ
  filter_upwards [hall] with t ht
  obtain ⟨n, hn⟩ := exists_nat_gt |t|
  exact ht n (Set.mem_Icc.mpr (abs_le.mp hn.le))

omit [CompleteSpace H] in
/-- On a separable Hilbert space, equality of multiplication operators
recovers the entire field almost everywhere. -/
theorem RepresentsOperatorField.field_eq_ae_real [TopologicalSpace.SeparableSpace H]
    {F G : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T) (hG : RepresentsOperatorField volume G T) :
    F =ᵐ[volume] G := by
  obtain ⟨v, hv⟩ := TopologicalSpace.exists_dense_seq (α := H)
  have hall : ∀ᵐ t : ℝ ∂volume, ∀ n : ℕ, F t (v n) = G t (v n) :=
    ae_all_iff.mpr fun n => hF.eval_eq_ae_real hG (v n)
  filter_upwards [hall] with t ht
  apply ContinuousLinearMap.ext
  exact congrFun (hv.equalizer (F t).continuous (G t).continuous (funext ht))

/-- Translation conjugates an actual multiplication operator by shifting
its field. -/
theorem RepresentsOperatorField.real_translate
    {F : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T) (s : Multiplicative ℝ) :
    RepresentsOperatorField volume (fun t => F (t + s.toAdd))
      (unitaryConj (regularRightTranslation (H := H) s) T) := by
  intro f
  have hstar : (star (regularRightTranslation (H := H) s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      (regularRightTranslation (H := H) s⁻¹ :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
    rw [map_inv]
    rfl
  unfold unitaryConj
  rw [hstar]
  filter_upwards [regularRightTranslation_apply_ae s
      (T ((regularRightTranslation (H := H) s⁻¹ :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)),
    (measurePreserving_add_right volume s.toAdd).quasiMeasurePreserving.ae_eq_comp
      (hF ((regularRightTranslation (H := H) s⁻¹ :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)),
    (measurePreserving_add_right volume s.toAdd).quasiMeasurePreserving.ae_eq_comp
      (regularRightTranslation_apply_ae s⁻¹ f)] with t hρ hFshift hback
  simp only [Function.comp_def] at hFshift hback
  change (regularRightTranslation (H := H) s :
    RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (T ((regularRightTranslation (H := H) s⁻¹ :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)) t = _
  rw [hρ, hFshift, hback]
  simp

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialProduct
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.countableTensorAlgebraic_tmul _root_.OAI.KadisonKastler.countableTensorEquiv_symm_single _root_.OAI.KadisonKastler.countableTensorEquiv_tmul _root_.OAI.KadisonKastler.countableTensorIsometry_tmul _root_.OAI.KadisonKastler.countableTensorVector_apply _root_.OAI.KadisonKastler.countableTensorVector_single _root_.OAI.KadisonKastler.leftTensorVector_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.rightTensorSlice_apply _root_.OAI.KadisonKastler.spatialIsometry_tmul _root_.OAI.KadisonKastler.spatialMap_id _root_.OAI.KadisonKastler.spatialMap_tmul _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonKastler.tensorVectorSliceCP_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The concrete spatial tensor product used in the fixed-factor reduction

The spatial von Neumann algebra is the bicommutant of the bounded tensor
operators. Vector slices act on the completed tensor Hilbert space.
-/

namespace KadisonKastler

open UnitalTomsWinter
open scoped TensorProduct InnerProductSpace

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] [CompleteSpace K] in
theorem norm_tensorVector_le (ξ : K) : ‖tensorVector (H := H) ξ‖ ≤ ‖ξ‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [norm_tensorVector_apply, mul_comm]

omit [CompleteSpace K] in
/-- Slicing a simple tensor gives its actual vector-state coefficient. -/
theorem tensorVectorSlice_tensor (ξ : K) (S : H →L[ℂ] H) (T : K →L[ℂ] K) :
    tensorVectorSlice ξ (spatialTensorOp S T) = (inner ℂ ξ (T ξ)) • S := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro y
  rw [tensorVectorSlice_apply, ContinuousLinearMap.adjoint_inner_right]
  simp only [tensorVector_apply, spatialTensorOp_coe, TensorProduct.mapL_tmul,
    UniformSpace.Completion.inner_coe, TensorProduct.inner_tmul, smul_apply,
    inner_smul_right]
  ring

/-- A unit vector makes the slice a left inverse of the first-leg inclusion. -/
theorem tensorVectorSlice_spatialLeft (ξ : K) (hξ : ‖ξ‖ = 1) (S : H →L[ℂ] H) :
    tensorVectorSlice ξ (spatialLeft S) = S := by
  change tensorVectorSlice ξ (spatialTensorOp S 1) = S
  rw [tensorVectorSlice_tensor, one_apply_eq_self, inner_self_eq_norm_sq_to_K, hξ]
  simp

omit [CompleteSpace K] in
theorem norm_tensorVectorSlice_le (ξ : K) (hξ : ‖ξ‖ = 1)
    (T : SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :
    ‖tensorVectorSlice ξ T‖ ≤ ‖T‖ := by
  change ‖(tensorVector ξ).adjoint ∘L T ∘L tensorVector ξ‖ ≤ ‖T‖
  have hV : ‖tensorVector (H := H) ξ‖ ≤ 1 := (norm_tensorVector_le ξ).trans_eq hξ
  have hVs : ‖(tensorVector (H := H) ξ).adjoint‖ ≤ 1 := by
    simpa only [ContinuousLinearMap.adjoint.norm_map] using hV
  calc
    _ ≤ (‖(tensorVector ξ).adjoint‖ * ‖T‖) * ‖tensorVector ξ‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ (1 * ‖T‖) * 1 := by gcongr
    _ = ‖T‖ := by ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialFieldPeriods
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Tensor coefficients turn central commutation into frequency periods

In Fourier coordinates a site eigenoperator is a constant second-leg
operator followed by a frequency translation. Commuting with it forces
an actual first-leg coefficient field to have that period. Two
incommensurable site frequencies therefore make the field constant.
-/

namespace KadisonKastler

open MeasureTheory UnitalTomsWinter
open scoped TensorProduct InnerProductSpace

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Commutation with a constant coefficient followed by translation gives
an almost-everywhere field intertwining identity. -/
theorem RepresentsOperatorField.intertwine_translation
    [TopologicalSpace.SeparableSpace E]
    {F : ℝ → E →L[ℂ] E}
    {T : RegularCoreHilbert E →L[ℂ] RegularCoreHilbert E}
    (hF : RepresentsOperatorField volume F T) (b : E →L[ℂ] E) (s : ℝ)
    (hcomm : Commute T (regularConstantHom volume b *
      (regularRightTranslation (H := E) (Multiplicative.ofAdd s) :
        RegularCoreHilbert E →L[ℂ] RegularCoreHilbert E))) :
    ∀ᵐ t ∂volume, F t * b = b * F (t + s) := by
  let R := regularRightTranslation (H := E) (Multiplicative.ofAdd s)
  change Commute T (regularConstantHom volume b *
    (R : RegularCoreHilbert E →L[ℂ] RegularCoreHilbert E)) at hcomm
  have he : T * regularConstantHom volume b = regularConstantHom volume b *
      unitaryConj R T := by
    have h := congrArg (fun S : RegularCoreHilbert E →L[ℂ] RegularCoreHilbert E =>
      S * (star R : RegularCoreHilbert E →L[ℂ] RegularCoreHilbert E)) hcomm.eq
    simpa only [mul_assoc, Unitary.mul_star_self_of_mem R.property, mul_one,
      unitaryConj] using h
  have hl : RepresentsOperatorField volume (fun t => F t * b)
      (T * regularConstantHom volume b) := by
    intro f
    filter_upwards [hF (regularConstantHom volume b f),
      regularConstantHom_apply_ae volume b f] with t ht hb
    change T (regularConstantHom volume b f) t = _
    rw [ht, hb]
    rfl
  have hr : RepresentsOperatorField volume (fun t => b * F (t + s))
      (T * regularConstantHom volume b) := by
    rw [he]
    intro f
    filter_upwards [regularConstantHom_apply_ae volume b (unitaryConj R T f),
      hF.real_translate (Multiplicative.ofAdd s) f] with t hb ht
    change regularConstantHom volume b (unitaryConj R T f) t = _
    rw [hb, ht]
    rfl
  exact hl.field_eq_ae_real hr

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularFieldMembership
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Countable tests recover fiberwise algebra membership

A represented measurable field inherits commutation with a bounded set
of constant operators on one common conull set. Countable strong tests
justify the interchange of the almost-everywhere and operator quantifiers.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-- Constant commutation descends to a represented field almost everywhere. -/
theorem RepresentsOperatorField.commute_constant_ae
    {F : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T) (b : H →L[ℂ] H)
    (hcomm : Commute T (regularConstantHom volume b)) :
    ∀ᵐ t ∂volume, Commute (F t) b := by
  have he := hF.intertwine_translation b 0 (by simpa using hcomm)
  filter_upwards [he] with t ht
  change F t * b = b * F t
  simpa only [add_zero] using ht

/-- One common conull set works for a whole bounded collection of tests. -/
theorem RepresentsOperatorField.commute_set_ae
    {F : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T) (S : Set (H →L[ℂ] H))
    (hS : ∀ b ∈ S, ‖b‖ ≤ 1)
    (hcomm : ∀ b ∈ S, Commute T (regularConstantHom volume b)) :
    ∀ᵐ t ∂volume, ∀ b ∈ S, Commute (F t) b := by
  obtain ⟨E, hEc, hES, htest⟩ := exists_countable_commutant_tests S hS
  have hall : ∀ᵐ t ∂volume, ∀ b ∈ E, Commute (F t) b := by
    apply (ae_ball_iff hEc).mpr
    intro b hb
    exact hF.commute_constant_ae b (hcomm b (hES hb))
  exact hall.mono fun t ht => (htest (F t)).mp ht

/-- The field of an operator in the constant-commutant tensor algebra
belongs to the original algebra almost everywhere. -/
theorem RepresentsOperatorField.mem_algebra_ae
    {F : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hF : RepresentsOperatorField volume F T) (P : VonNeumannAlgebra H)
    (hT : T ∈ regularTensorAlgebra P) : ∀ᵐ t ∂volume, F t ∈ P := by
  have hc := hF.commute_set_ae (unitBall P.commutant) (fun _ hb => hb.2)
    (fun b hb => ((mem_regularTensorAlgebra_iff P T).mp hT b hb.1).symm)
  filter_upwards [hc] with t ht
  rw [← P.commutant_commutant]
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro b hb
  have hclip : Commute (F t) (unitBallClip b) := ht _
    ⟨unitBallClip_mem P.commutant.toStarSubalgebra.toSubalgebra.toSubmodule hb,
      unitBallClip_norm_le b⟩
  have hp : 0 < max 1 ‖b‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have he : ((max 1 ‖b‖ : ℝ) : ℂ) • unitBallClip b = b := by
    rw [unitBallClip, smul_smul]
    have hn : ((max 1 ‖b‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    simp only [Complex.ofReal_inv, mul_inv_cancel₀ hn, one_smul]
  have h := congrArg (fun B : H →L[ℂ] H => ((max 1 ‖b‖ : ℝ) : ℂ) • B) hclip.eq
  have heq : F t * (((max 1 ‖b‖ : ℝ) : ℂ) • unitBallClip b) =
      (((max 1 ‖b‖ : ℝ) : ℂ) • unitBallClip b) * F t := by
    rw [mul_smul_comm, smul_mul_assoc]
    exact h
  rw [he] at heq
  exact heq.symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularSpatialField
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.conjugation_algebraVector _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.countableTensorAlgebraic_tmul _root_.OAI.KadisonKastler.countableTensorEquiv_symm_single _root_.OAI.KadisonKastler.countableTensorEquiv_tmul _root_.OAI.KadisonKastler.countableTensorIsometry_tmul _root_.OAI.KadisonKastler.countableTensorVector_apply _root_.OAI.KadisonKastler.countableTensorVector_single _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.spatialIsometry_tmul _root_.OAI.KadisonKastler.spatialMap_id _root_.OAI.KadisonKastler.spatialMap_tmul _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonKastler.tensorVectorSliceCP_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # First-leg fields in the relative commutant of the product centralizer -/

namespace KadisonKastler

open MeasureTheory UnitalTomsWinter

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [TopologicalSpace.SeparableSpace (SpatialHilbert H K)]

/-- In the Fourier decomposition of a central core operator, constant
product-centralizer commutation removes the entire second tensor leg.
The coefficient field is obtained by a concrete slice, so measurability
and its norm bound are retained. -/
theorem first_leg_field_of_product_centralizer_oai
    (M : VonNeumannAlgebra H) {D : VonNeumannAlgebra K} {Ω : K}
    (L : LocalProductSwaps D Ω) (hΩ : ‖Ω‖ = 1)
    (hsep : Function.Injective (algebraVectorMap D Ω))
    (F : ℝ → SpatialHilbert H K →L[ℂ] SpatialHilbert H K)
    (T : RegularCoreHilbert (SpatialHilbert H K) →L[ℂ]
      RegularCoreHilbert (SpatialHilbert H K))
    (hFT : RepresentsOperatorField volume F T)
    (hmeas : ∀ ξ, AEStronglyMeasurable (fun t => F t ξ) volume)
    (C : ℝ) (hbound : ∀ᵐ t ∂volume, ‖F t‖ ≤ C)
    (hT : T ∈ regularTensorAlgebra (spatialProductAlgebra M D))
    (hcomm : ∀ u : unitary (K →L[ℂ] K), (u : K →L[ℂ] K) ∈ D →
      ProductStateCentralizes D Ω u → Commute T
        (regularConstantHom volume (spatialRight (H := H) (u : K →L[ℂ] K)))) :
    ∃ A : ℝ → H →L[ℂ] H,
      (∀ ξ, AEStronglyMeasurable (fun t => A t ξ) volume) ∧
      (∀ᵐ t ∂volume, ‖A t‖ ≤ C) ∧ (∀ᵐ t ∂volume, A t ∈ M) ∧
      RepresentsOperatorField volume (fun t => spatialLeft (K := K) (A t)) T := by
  let S : Set (SpatialHilbert H K →L[ℂ] SpatialHilbert H K) :=
    {b | ∃ u : unitary (K →L[ℂ] K), (u : K →L[ℂ] K) ∈ D ∧
      ProductStateCentralizes D Ω u ∧ b = spatialRight (H := H) (u : K →L[ℂ] K)}
  have hS (b) (hb : b ∈ S) : ‖b‖ ≤ 1 := by
    obtain ⟨u, _, _, rfl⟩ := hb
    change ‖spatialTensorOp (1 : H →L[ℂ] H) (u : K →L[ℂ] K)‖ ≤ 1
    have hId : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := norm_unitary_le_one 1
    calc
      _ ≤ ‖(1 : H →L[ℂ] H)‖ * ‖(u : K →L[ℂ] K)‖ := spatialTensorOp_norm_le _ _
      _ ≤ 1 * 1 := mul_le_mul hId (norm_unitary_le_one u) (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul 1
  have hcommS (b) (hb : b ∈ S) : Commute T (regularConstantHom volume b) := by
    obtain ⟨u, hu, hc, rfl⟩ := hb
    exact hcomm u hu hc
  have hc := hFT.commute_set_ae S hS hcommS
  have hm := hFT.mem_algebra_ae (spatialProductAlgebra M D) hT
  let A : ℝ → H →L[ℂ] H := fun t => tensorVectorSlice Ω (F t)
  have he : ∀ᵐ t ∂volume, F t = spatialLeft (K := K) (A t) := by
    filter_upwards [hc, hm] with t hct hmt
    obtain ⟨a, ha, hFa⟩ := spatial_relative_commutant_of_local_swaps M L hΩ hsep
      (F t) hmt (fun u hu hcu => (hct _ ⟨u, hu, hcu, rfl⟩).eq.symm)
    have hAa : A t = a := by
      dsimp [A]
      rw [hFa, tensorVectorSlice_spatialLeft Ω hΩ]
    exact hFa.trans (congrArg (spatialLeft (K := K)) hAa.symm)
  refine ⟨A, ?_, ?_, ?_, ?_⟩
  · intro ξ
    exact (tensorVector Ω).adjoint.continuous.comp_aestronglyMeasurable
      (hmeas (tensorVector Ω ξ))
  · filter_upwards [hbound] with t ht
    exact (norm_tensorVectorSlice_le Ω hΩ (F t)).trans ht
  · filter_upwards [hm] with t ht
    exact tensorVectorSlice_mem M D Ω (F t) ht
  · intro f
    filter_upwards [hFT f, he] with t ht het
    exact ht.trans (congrArg (fun B : SpatialHilbert H K →L[ℂ] SpatialHilbert H K =>
      B (f t)) het)

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.first_leg_field_of_product_centralizer_oai.{u_1, u_2} := @OAI.KadisonKastler.first_leg_field_of_product_centralizer_oai.{u_1, u_2}
