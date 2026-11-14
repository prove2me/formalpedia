-- Prove2me | solution 1 for OAI.KadisonKastler.StandardTracialPosition.exists_ae_diagonal_unitary_comparison
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:22:33.905824+00:00
-- url     : https://prove2.me/submissions/1060a933-f4b5-44c6-9174-dc6458b0055e

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
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
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
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Banach
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
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
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
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K014
import Definitions.Def_Q260K029
import Theorems.Thm_OAI_KadisonKastler_exists_measurable_diagonal_unitary_on_set

section
-- module Solutions.OAIQ075_KS.FactorGeneration_OperatorLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Generator

/-! Operator-norm completeness of the manuscript's concrete algebra, derived
from its actual double-commutant property. No quotient completeness is assumed. -/

/-! Operator order bounds are closed in the weak operator topology. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem weakOperator_nonneg_isClosed :
    IsClosed {T : H →WOT[ℂ] H | 0 ≤ T.toCLM} := by
  have hi (x : H) : Continuous (fun T : H →WOT[ℂ] H => inner ℂ (T x) x) := by
    simpa only [Function.comp_def, id_eq, inner_conj_symm] using
      (Complex.continuous_conj.comp
        (ContinuousLinearMapWOT.continuous_inner_apply continuous_id x x))
  have he : {T : H →WOT[ℂ] H | 0 ≤ T.toCLM} =
      ⋂ x : H, {T : H →WOT[ℂ] H |
        ((inner ℂ (T x) x).re : ℂ) = inner ℂ (T x) x ∧ 0 ≤ (inner ℂ (T x) x).re} := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, ContinuousLinearMap.nonneg_iff_isPositive,
      ContinuousLinearMap.isPositive_iff_complex]
    rfl
  rw [he]
  apply isClosed_iInter
  intro x
  exact (isClosed_eq (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (hi x)))
    (hi x)).inter (isClosed_le continuous_const (Complex.continuous_re.comp (hi x)))

end Generator

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConcreteTraceTransfer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.Tracial.conjugateLinear_one _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.quotientInclusion_mk _root_.OAI.Generator.Tracial.quotientInclusion_trace _root_.OAI.Generator.Tracial.traceFreeCopy_inner _root_.OAI.Generator.Tracial.traceFreeHilbertCoefficient_apply _root_.OAI.Generator.Tracial.traceFreeInclusion_inner _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.conjugation_algebraVector _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.TraceQuotientMap.comapEquiv_quotient _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.concreteTraceEmbedding_inner _root_.OAI.KadisonKastler.concreteTraceLeftAction_embedding _root_.OAI.KadisonKastler.concreteTraceLeftUnitary_coe _root_.OAI.KadisonKastler.concreteTraceRightAction_embedding _root_.OAI.KadisonKastler.concreteTraceRightUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.expectedTrace_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrixSequenceQuotient_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.productBoundaryRepresentation_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.realTrace_apply _root_.OAI.KadisonKastler.rescaledGraphMap_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.traceCenter_apply _root_.OAI.KadisonKastler.traceStateRepresentation_vector _root_.OAI.KadisonKastler.traceStateRight_vector _root_.OAI.KadisonKastler.traceStateVector_sub _root_.OAI.KadisonKastler.traceTwoNorm_eq_zero_iff _root_.OAI.KadisonKastler.traceTwoNorm_neg _root_.OAI.KadisonKastler.traceTwoNorm_zero _root_.OAI.KadisonKastler.trace_traceCenter _root_.OAI.KadisonKastler.tracialHilbertConjugation_embedding _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceContinuous_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.tracialSequenceValue_one _root_.OAI.KadisonKastler.tracialStarIsometry_embedding _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe _root_.OAI.UltrapowerBridge.quotientMap_smul _root_.OAI.UltrapowerBridge.quotientMap_star _root_.OAI.UltrapowerBridge.quotientTrace_mk _root_.OAI.UltrapowerBridge.quotientTrace_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Strong trace transfer in a concrete finite representation

A finite vector-functional formula for the trace is enough: weak
compactness of the positive operator ball and faithfulness prove the
uniform two-norm-to-strong implication. No transfer theorem is assumed.
-/

namespace KadisonKastler

open Filter
open scoped Topology BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

attribute [local instance] OAI.KadisonKastler.concreteTraceOrder
local instance concreteTracePreorder_r6cd51c_1 : Preorder (Algebra M) := (CStarAlgebra.spectralOrder _).toPreorder
attribute [local instance] OAI.KadisonKastler.concreteTraceLE
local instance concreteTraceStarOrder : StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

/-- Faithfulness and weak compactness turn the normal trace into a
uniform strong-topology control on each operator-norm ball. -/
theorem FiniteVectorTrace.strongContinuous {τ : FaithfulTracialState (Algebra M)}
    (hτ : FiniteVectorTrace τ) : TraceStrongContinuous τ M.toStarSubalgebra.subtype := by
  intro z C hC ε hε
  by_contra! hbad
  have hex (n : ℕ) := hbad (1 / ((n : ℝ) + 1)) (by positivity)
  choose x hxC hx2 hxε using hex
  let ω := Ultrafilter.of (atTop : Filter ℕ)
  have hω : (ω : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  have htwo : Tendsto (fun n => traceTwoNorm τ (x n)) (ω : Filter ℕ) (𝓝 0) := by
    apply squeeze_zero (fun n => traceTwoNorm_nonneg τ (x n)) (fun n => (hx2 n).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat.mono_left hω
  let a : ℕ → Algebra M := fun n => star (x n) * x n
  have ha : ∀ n, ‖a n‖ ≤ C ^ 2 := by
    intro n
    dsimp [a]
    rw [CStarRing.norm_star_mul_self, ← pow_two]
    exact pow_le_pow_left₀ (norm_nonneg _) (hxC n) 2
  obtain ⟨T, _, hT⟩ := Generator.Tracial.exists_weak_operator_ultralimit ω
    (fun n => (a n : H →L[ℂ] H)) (C ^ 2) (sq_nonneg C) ha
  have hm : T ∈ M := Generator.Tracial.weak_operator_limit_mem M a T hT
  let b : Algebra M := ⟨T, hm⟩
  have hWOT : Tendsto (fun n => ContinuousLinearMapWOT.ofCLM (a n : H →L[ℂ] H))
      (ω : Filter ℕ) (𝓝 (ContinuousLinearMapWOT.ofCLM T)) :=
    ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr hT
  have hposT : 0 ≤ T := (Generator.weakOperator_nonneg_isClosed (H := H)).mem_of_tendsto
    hWOT (Eventually.of_forall fun n => by
      change 0 ≤ star (x n : H →L[ℂ] H) * (x n : H →L[ℂ] H)
      exact star_mul_self_nonneg _)
  have hpos : 0 ≤ b := by
    apply (NonUnitalStarAlgHom.map_le_map_iff M.toStarSubalgebra.subtype
      Subtype.val_injective).mp
    simpa only [map_zero, b, StarSubalgebra.subtype_apply] using hposT
  have htτ := hτ.tendsto a b hT
  have htzero : Tendsto (fun n => τ.toLinearMap (a n)) (ω : Filter ℕ) (𝓝 0) := by
    have he (n : ℕ) : τ.toLinearMap (a n) = ((traceTwoNorm τ (x n) ^ 2 : ℝ) : ℂ) := by
      apply Complex.ext
      · simp only [Complex.ofReal_re, a, traceTwoNorm_sq]
      · simp only [a, τ.positive_im, Complex.ofReal_im]
    simp_rw [he]
    simpa only [Function.comp_def, zero_pow (by decide : (2 : ℕ) ≠ 0), Complex.ofReal_zero] using
      (Complex.continuous_ofReal.tendsto 0).comp (by simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using htwo.pow 2)
  have hbτ : τ.toLinearMap b = 0 := tendsto_nhds_unique htτ htzero
  obtain ⟨v, hv⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hpos
  have hvτ : τ.toLinearMap (star v * v) = 0 := by rw [← hv, hbτ]
  have hv0 := τ.faithful v hvτ
  have hb0 : b = 0 := by rw [hv, hv0, star_zero, zero_mul]
  have hT0 : T = 0 := congrArg Subtype.val hb0
  have ht := (Complex.continuous_re.tendsto _).comp (hT z z)
  have hlo : ε ^ 2 ≤ (inner ℂ z (T z)).re := by
    apply ge_of_tendsto ht
    apply Eventually.of_forall
    intro n
    have he : (inner ℂ z ((a n : H →L[ℂ] H) z)).re = ‖(x n : H →L[ℂ] H) z‖ ^ 2 := by
      change (inner ℂ z ((star (x n : H →L[ℂ] H)) ((x n : H →L[ℂ] H) z))).re = _
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
      simpa only [RCLike.re_eq_complex_re] using
        (inner_self_eq_norm_sq (𝕜 := ℂ) ((x n : H →L[ℂ] H) z))
    change ε ^ 2 ≤ (inner ℂ z ((a n : H →L[ℂ] H) z)).re
    rw [he]
    exact pow_le_pow_left₀ hε.le (hxε n) 2
  rw [hT0] at hlo
  simp only [zero_apply, inner_zero_right, Complex.zero_re] at hlo
  nlinarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TraceFieldMeasurable
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instTopologicalSpaceElemProdForallNatStrongUnitarySpace _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Measurable operator fields from their tracial Hilbert realizations

On an operator-norm bounded ball, trace two-norm convergence implies
strong operator convergence. Thus a measurable trace-Hilbert field gives
measurable Hilbert-valued evaluations in the original representation.
-/

namespace KadisonKastler

open MeasureTheory TopologicalSpace

noncomputable section

variable {D H E : Type*} [MeasurableSpace D]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {M : VonNeumannAlgebra H} {τ : FaithfulTracialState (Algebra M)}

/-- Strong-operator evaluation is continuous on a bounded trace-Hilbert ball. -/
theorem continuous_traceBall_eval (J : Algebra M →ₗ[ℂ] E)
    (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (hτ : FiniteVectorTrace τ) {C : ℝ} (hC : 0 ≤ C)
    (lift : (J '' Metric.closedBall (0 : Algebra M) C) → Algebra M)
    (hlift : ∀ z, J (lift z) = z.val ∧ ‖lift z‖ ≤ C) (ξ : H) :
    Continuous (fun z => (lift z : H →L[ℂ] H) ξ) := by
  apply Metric.continuous_iff.mpr
  intro z ε hε
  obtain ⟨δ, hδ, hsmall⟩ := hτ.strongContinuous ξ (2 * C) (by positivity) ε hε
  refine ⟨δ, hδ, fun w hw => ?_⟩
  have hnorm : ‖lift w - lift z‖ ≤ 2 * C := by
    have h := (norm_sub_le (lift w) (lift z)).trans
      (add_le_add (hlift w).2 (hlift z).2)
    linarith
  have htwo : traceTwoNorm τ (lift w - lift z) < δ := by
    rw [← hJ, map_sub, (hlift w).1, (hlift z).1]
    simpa only [Subtype.dist_eq, dist_eq_norm] using hw
  have hs := hsmall (lift w - lift z) hnorm htwo
  change ‖(lift w : H →L[ℂ] H) ξ - (lift z : H →L[ℂ] H) ξ‖ < ε at hs
  simpa only [dist_eq_norm] using hs

/-- A globally bounded algebra field measurable in its trace Hilbert
space is strongly measurable after evaluation at any Hilbert vector. -/
theorem aestronglyMeasurable_operator_eval_of_trace [SeparableSpace H]
    (J : Algebra M →ₗ[ℂ] E) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (hτ : FiniteVectorTrace τ) {μ : Measure D}
    (a : D → Algebra M) {C : ℝ} (hC : 0 ≤ C) (ha : ∀ x, ‖a x‖ ≤ C)
    (hmeas : AEStronglyMeasurable (fun x => J (a x)) μ) (ξ : H) :
    AEStronglyMeasurable (fun x => (a x : H →L[ℂ] H) ξ) μ := by
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let S : Set E := J '' Metric.closedBall (0 : Algebra M) C
  have hs (z : S) : ∃ b : Algebra M, J b = z.val ∧ ‖b‖ ≤ C := by
    obtain ⟨b, hb, he⟩ := z.property
    exact ⟨b, he, by simpa only [Metric.mem_closedBall, dist_zero_right] using hb⟩
  choose lift hlift using hs
  let f : D → S := fun x => ⟨J (a x), ⟨a x, by
    simpa only [Metric.mem_closedBall, dist_zero_right] using ha x, rfl⟩⟩
  have hf : AEMeasurable f μ := hmeas.aemeasurable.subtype_mk
  have he := continuous_traceBall_eval J hJ hτ hC lift hlift ξ
  have hm : AEStronglyMeasurable (fun x => (lift (f x) : H →L[ℂ] H) ξ) μ :=
    (he.measurable.comp_aemeasurable hf).aestronglyMeasurable
  apply hm.congr
  exact Filter.Eventually.of_forall fun x => by
    have hax : lift (f x) = a x := traceHilbert_injective J hJ (hlift (f x)).1
    exact congrArg (fun b : Algebra M => (b : H →L[ℂ] H) ξ) hax

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NonsingularBoundary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Nonsingular boundary actions and simultaneous representatives

The action preserves null sets, not necessarily the measure. Countability
allows all the identities used in the boundary argument to hold on one
invariant conull set. The final definition isolates the exact unitary
coefficient property in Björklund, arXiv:1406.0763, Theorem 2.1 and
Remark 2.2, expressed as a property of the unitary coefficients.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {G D : Type*} [Group G] [MeasurableSpace D]

namespace NonsingularAction

variable {μ : Measure D} (α : NonsingularAction G D μ)

/-- Countably many almost-everywhere properties, together with all their
translates, hold on a single invariant conull set. -/
theorem exists_invariant_conull [Countable G] {ι : Type*} [Countable ι]
    (P : ι → D → Prop) (hP : ∀ i, ∀ᵐ x ∂μ, P i x) :
    ∃ S : Set D, (∀ᵐ x ∂μ, x ∈ S) ∧
      (∀ g x, x ∈ S → α.toPerm g x ∈ S) ∧
      (∀ x ∈ S, ∀ i, P i x) := by
  let S : Set D := {x | ∀ g : G, ∀ i : ι, P i (α.toPerm g x)}
  refine ⟨S, ?_, ?_, ?_⟩
  · exact eventually_countable_forall.mpr fun g =>
      eventually_countable_forall.mpr fun i => (α.quasi g).ae (hP i)
  · intro g x hx h i
    exact α.mul_apply h g x ▸ hx (h * g) i
  · intro x hx i
    simpa only [α.one_apply] using hx 1 i

end NonsingularAction

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StandardTracialPosition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Concrete standard tracial position

A faithful vector trace and cyclicity suffice to construct the standard
tracial conjugation. Its isometry and involution are proved rather than
included in the common-position input.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace StandardTracialPosition

variable {M : VonNeumannAlgebra H} (p : StandardTracialPosition M)

theorem finiteVectorTrace : FiniteVectorTrace p.trace := by
  refine ⟨1, fun _ => p.vector, fun _ => p.vector, ?_⟩
  intro a
  simpa only [Fin.sum_univ_one] using p.trace_eq a

end StandardTracialPosition

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AEBoundaryDiagonal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.NonsingularAction.leftOnProduct_apply _root_.OAI.KadisonKastler.NonsingularAction.operatorAction_constant _root_.OAI.KadisonKastler.NonsingularAction.operatorEquiv_apply _root_.OAI.KadisonKastler.NonsingularAction.restrictedOperatorAction_coe _root_.OAI.KadisonKastler.ScalarBoundaryMean.operatorMean_apply _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.productBoundaryRepresentation_coe _root_.OAI.KadisonKastler.productBoundaryValue_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.randomWalkPathAction_apply _root_.OAI.KadisonKastler.rescaledGraphMap_apply _root_.OAI.KadisonKastler.shiftBoundaryAction_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Diagonal comparison from almost-everywhere cocycle data

A countable group has a common invariant conull set for the cocycle laws
and approximation bounds. Outside that set the generating family is filled
with one good value. This provides global bounds for the least-vector and
polar constructions; covariance is required only on the conull set.
-/

namespace KadisonKastler

open MeasureTheory Filter TopologicalSpace

noncomputable section

section AE

variable {H E G D : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [SeparableSpace E]
  [MeasurableSpace E] [BorelSpace E] [Group G] [Countable G] [MeasurableSpace D]
  {μ : Measure D} [SFinite μ] [NeZero μ]
  {M : VonNeumannAlgebra H} {τ : FaithfulTracialState (Algebra M)}

/-- The unitary-pair displacement equals the distance between the pair. -/
theorem norm_unitary_mul_star_sub_one (u v : unitary (Algebra M)) :
    ‖(u : Algebra M) * star (v : Algebra M) - 1‖ = ‖(u : Algebra M) - v‖ := by
  have he : (u : Algebra M) * star (v : Algebra M) - 1 =
      ((u : Algebra M) - v) * star (v : Algebra M) := by
    rw [sub_mul, Unitary.mul_star_self_of_mem v.property]
  rw [he]
  exact CStarRing.norm_mul_coe_unitary ((u : Algebra M) - v) (star v)

/-- Countably many almost-everywhere laws give the diagonal comparison,
with its explicit `4δ` displacement and almost-everywhere covariance. -/
theorem exists_ae_measurable_diagonal_unitary_comparison
    (J : Algebra M →ₗ[ℂ] E) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (hτ : FiniteVectorTrace τ) (α : NonsingularAction G D μ)
    (W : G → D → unitary (Algebra M))
    (hW : ∀ g t, ∀ᵐ x ∂μ, (W (g * t) x : Algebra M) =
      (W g x : Algebra M) * (W t (α.toPerm g⁻¹ x) : Algebra M))
    (hWmeas : ∀ t, AEStronglyMeasurable
      (fun p : D × D => J ((W t p.1 : Algebra M) * star (W t p.2 : Algebra M))) (μ.prod μ))
    (U : G → unitary (H →L[ℂ] H)) {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : 2 * δ < 1)
    (hclose : ∀ g, ∀ᵐ x ∂μ, ‖(W g x : Algebra M).val - (U g : H →L[ℂ] H)‖ ≤ δ) :
    ∃ a : D → D → unitary (Algebra M),
      AEStronglyMeasurable (fun p : D × D => J (a p.1 p.2 : Algebra M)) (μ.prod μ) ∧
      (∀ x y, ‖(a x y : Algebra M) - 1‖ ≤ 4 * δ) ∧
      (∀ g, ∀ᵐ p ∂μ.prod μ, (a p.1 p.2 : Algebra M) =
        (W g p.1 : Algebra M) *
          (a (α.toPerm g⁻¹ p.1) (α.toPerm g⁻¹ p.2) : Algebra M) *
            star (W g p.2 : Algebra M)) := by
  classical
  let P : (G × G) ⊕ G → D → Prop := fun i x => match i with
    | Sum.inl gh => (W (gh.1 * gh.2) x : Algebra M) =
        (W gh.1 x : Algebra M) * (W gh.2 (α.toPerm gh.1⁻¹ x) : Algebra M)
    | Sum.inr g => ‖(W g x : Algebra M).val - (U g : H →L[ℂ] H)‖ ≤ δ
  have hP (i) : ∀ᵐ x ∂μ, P i x := by
    cases i with
    | inl gh => exact hW gh.1 gh.2
    | inr g => exact hclose g
  obtain ⟨S, hS, hSinv, hSP⟩ := α.exists_invariant_conull P hP
  obtain ⟨x₀, hx₀⟩ := hS.exists
  let pick : D → D := fun x => if x ∈ S then x else x₀
  have hpick (x : D) : pick x ∈ S := by
    dsimp only [pick]
    split_ifs with hx
    · exact hx
    · exact hx₀
  have hpick_eq {x : D} (hx : x ∈ S) : pick x = x := ite_eq_left hx
  let W' : G → D → unitary (Algebra M) := fun g x => W g (pick x)
  have heq (g : G) {x : D} (hx : x ∈ S) : W' g x = W g x := by
    dsimp only [W']
    rw [hpick_eq hx]
  have hW' (g t : G) (x : D) (hx : x ∈ S) :
      (W' (g * t) x : Algebra M) =
        (W' g x : Algebra M) * (W' t (α.toPerm g⁻¹ x) : Algebra M) := by
    rw [heq _ hx, heq _ hx, heq _ (hSinv g⁻¹ x hx)]
    exact hSP x hx (.inl (g, t))
  have hW'meas (t : G) : AEStronglyMeasurable
      (fun p : D × D => J ((W' t p.1 : Algebra M) * star (W' t p.2 : Algebra M))) (μ.prod μ) := by
    apply (hWmeas t).congr
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hS,
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hS] with p hx hy
    rw [heq _ hx, heq _ hy]
  have hW'close (g : G) (x : D) :
      ‖(W' g x : Algebra M).val - (U g : H →L[ℂ] H)‖ ≤ δ :=
    hSP (pick x) (hpick x) (.inr g)
  have hnear (g : G) (x y : D) :
      ‖(W' g x : Algebra M) * star (W' g y : Algebra M) - 1‖ ≤ 2 * δ := by
    rw [norm_unitary_mul_star_sub_one]
    change ‖(W' g x : Algebra M).val - (W' g y : Algebra M).val‖ ≤ 2 * δ
    calc
      _ ≤ ‖(W' g x : Algebra M).val - (U g : H →L[ℂ] H)‖ +
          ‖(U g : H →L[ℂ] H) - (W' g y : Algebra M).val‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖(W' g x : Algebra M).val - (U g : H →L[ℂ] H)‖ +
          ‖(W' g y : Algebra M).val - (U g : H →L[ℂ] H)‖ := by
        rw [norm_sub_rev (U g : H →L[ℂ] H)]
      _ ≤ δ + δ := add_le_add (hW'close g x) (hW'close g y)
      _ = 2 * δ := (two_mul δ).symm
  obtain ⟨a, ham, han, hac⟩ := exists_measurable_diagonal_unitary_on_set J hJ hτ S
    (fun g x => α.toPerm g⁻¹ x) W' hW' hW'meas (by positivity) hsmall hnear
  refine ⟨a, ham, ?_, ?_⟩
  · intro x y
    calc
      _ ≤ 2 * (2 * δ) := han x y
      _ = 4 * δ := by ring
  · intro g
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hS,
      (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hS] with p hx hy
    simpa only [heq _ hx, heq _ hy] using hac g p.1 p.2 hx hy

end AE

section Standard

variable {H G D : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [SeparableSpace H] [Group G] [Countable G] [MeasurableSpace D]
  {μ : Measure D} [SFinite μ] [NeZero μ] {M : VonNeumannAlgebra H}

/-- The standard-position version needs only measurable operator evaluations
of the original cocycle. Its diagonal unitary field is likewise measurable
on every vector of the ambient Hilbert space. -/
theorem StandardTracialPosition.exists_ae_diagonal_unitary_comparison_oai
    (p : StandardTracialPosition M) (α : NonsingularAction G D μ)
    (W : G → D → unitary (Algebra M))
    (hW : ∀ g t, ∀ᵐ x ∂μ, (W (g * t) x : Algebra M) =
      (W g x : Algebra M) * (W t (α.toPerm g⁻¹ x) : Algebra M))
    (hWmeas : ∀ g ξ, AEStronglyMeasurable (fun x => (W g x : Algebra M).val ξ) μ)
    (U : G → unitary (H →L[ℂ] H)) {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : 2 * δ < 1)
    (hclose : ∀ g, ∀ᵐ x ∂μ, ‖(W g x : Algebra M).val - (U g : H →L[ℂ] H)‖ ≤ δ) :
    ∃ a : D → D → unitary (Algebra M),
      (∀ ξ, AEStronglyMeasurable
        (fun x : D × D => (a x.1 x.2 : Algebra M).val ξ) (μ.prod μ)) ∧
      (∀ x y, ‖(a x y : Algebra M) - 1‖ ≤ 4 * δ) ∧
      (∀ g, ∀ᵐ x ∂μ.prod μ, (a x.1 x.2 : Algebra M) =
        (W g x.1 : Algebra M) *
          (a (α.toPerm g⁻¹ x.1) (α.toPerm g⁻¹ x.2) : Algebra M) *
            star (W g x.2 : Algebra M)) := by
  borelize H
  have hgen (g : G) : AEStronglyMeasurable
      (fun x : D × D => algebraVectorMap M p.vector
        ((W g x.1 : Algebra M) * star (W g x.2 : Algebra M))) (μ.prod μ) := by
    exact aestronglyMeasurable_field_apply
      (fun x : D × D => (W g x.1 : Algebra M).val)
      (fun ξ => (hWmeas g ξ).comp_fst)
      (fun x : D × D => star (W g x.2 : Algebra M).val p.vector)
      ((operator_adjoint_eval_aestronglyMeasurable
        (fun x => (W g x : Algebra M).val) (hWmeas g) p.vector).comp_snd)
  obtain ⟨a, ham, han, hac⟩ := exists_ae_measurable_diagonal_unitary_comparison
    (algebraVectorMap M p.vector) p.vectorMap_norm p.finiteVectorTrace
    α W hW hgen U hδ hsmall hclose
  refine ⟨a, ?_, han, hac⟩
  intro ξ
  exact aestronglyMeasurable_operator_eval_of_trace (algebraVectorMap M p.vector)
    p.vectorMap_norm p.finiteVectorTrace
    (fun x : D × D => (a x.1 x.2 : Algebra M)) (by norm_num : (0 : ℝ) ≤ 1)
    (fun x => norm_unitary_le_one (a x.1 x.2)) ham ξ

end Standard

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.KadisonKastler.StandardTracialPosition.exists_ae_diagonal_unitary_comparison_oai.{u_1, u_2, u_3} := @OAI.KadisonKastler.StandardTracialPosition.exists_ae_diagonal_unitary_comparison_oai.{u_1, u_2, u_3}
