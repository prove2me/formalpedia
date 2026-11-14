-- Prove2me | solution 1 for OAI.KadisonKastler.exists_continuous_unital_transfer_of_traceDense
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:16:39.626649+00:00
-- url     : https://prove2.me/submissions/e08e01ac-56fa-491b-a28a-27817a94219d

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
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
import Mathlib.Analysis.Convex.Combination
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
import Mathlib.Topology.DenseEmbedding
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
import Definitions.Def_Q260K014
import Definitions.Def_Q260K029

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
local instance concreteTracePreorder_rec6e50_1 : Preorder (Algebra M) := (CStarAlgebra.spectralOrder _).toPreorder
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
-- module Solutions.OAIQ075_KS.KadisonKastler_ConcreteTraceComplete
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Completeness of bounded tracial two-norm balls

Strong trace transfer and Hilbert-space completeness retain tracial
limits in the von Neumann algebra, allowing continuous circle cutoffs
to converge to spectral projections.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

/-- On a bounded operator ball the finite-vector trace is continuous for
strong convergence, also in the tracial two-norm. -/
theorem FiniteVectorTrace.traceTwoNorm_tendsto_of_strong
    {τ : FaithfulTracialState (Algebra M)} (hτ : FiniteVectorTrace τ)
    {J : Type*} {l : Filter J} (x : J → Algebra M) (a : Algebra M)
    {C : ℝ} (hx : ∀ j, ‖x j‖ ≤ C)
    (hstrong : ∀ ξ, Tendsto (fun j => (x j : H →L[ℂ] H) ξ) l
      (𝓝 ((a : H →L[ℂ] H) ξ))) :
    Tendsto (fun j => traceTwoNorm τ (x j - a)) l (𝓝 0) := by
  let d : J → Algebra M := fun j => x j - a
  have hd (ξ : H) : Tendsto (fun j => (d j : H →L[ℂ] H) ξ) l (𝓝 0) := by
    change Tendsto (fun j => (x j : H →L[ℂ] H) ξ - (a : H →L[ℂ] H) ξ) l (𝓝 0)
    simpa only [sub_self] using (hstrong ξ).sub (tendsto_const_nhds : Tendsto (fun _ : J => (a : H →L[ℂ] H) ξ) l (𝓝 ((a : H →L[ℂ] H) ξ)))
  have hdb (j : J) : ‖d j‖ ≤ C + ‖a‖ := (norm_sub_le _ _).trans (add_le_add (hx j) le_rfl)
  have hstar (ξ : H) : Tendsto
      (fun j => (star (d j) * d j : Algebra M).val ξ) l (𝓝 0) := by
    apply squeeze_zero_norm
    · intro j
      calc
        ‖(star (d j) * d j : Algebra M).val ξ‖ ≤ ‖star (d j : H →L[ℂ] H)‖ * ‖(d j : H →L[ℂ] H) ξ‖ :=
          (star (d j : H →L[ℂ] H)).le_opNorm _
        _ ≤ (C + ‖a‖) * ‖(d j : H →L[ℂ] H) ξ‖ := by
          rw [norm_star]
          exact mul_le_mul_of_nonneg_right (hdb j) (norm_nonneg _)
    · simpa only [norm_zero, mul_zero] using (hd ξ).norm.const_mul (C + ‖a‖)
  have ht := hτ.tendsto (fun j => star (d j) * d j) 0 (fun ξ η => by
    simpa only [ZeroMemClass.coe_zero, zero_apply, inner_zero_right] using
      tendsto_const_nhds.inner (hstar ξ))
  have hr := (Complex.continuous_re.tendsto _).comp ht
  have hs := (Real.continuous_sqrt.tendsto _).comp hr
  simpa only [traceTwoNorm, d, map_zero, Complex.zero_re, Real.sqrt_zero,
    Function.comp_def] using hs

/-- A uniformly bounded tracial two-Cauchy sequence has an actual limit
in the concrete von Neumann algebra, with strong and two-norm convergence. -/
theorem FiniteVectorTrace.bounded_complete
    {τ : FaithfulTracialState (Algebra M)} (hτ : FiniteVectorTrace τ)
    (x : ℕ → Algebra M) {C : ℝ} (hC : 0 ≤ C) (hx : ∀ j, ‖x j‖ ≤ C)
    (hCauchy : ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      traceTwoNorm τ (x m - x n) < ε) :
    ∃ a : Algebra M, ‖a‖ ≤ C ∧
      (∀ ξ, Tendsto (fun j => (x j : H →L[ℂ] H) ξ) atTop
        (𝓝 ((a : H →L[ℂ] H) ξ))) ∧
      Tendsto (fun j => traceTwoNorm τ (x j - a)) atTop (𝓝 0) := by
  have hc (ξ : H) : CauchySeq (fun j => (x j : H →L[ℂ] H) ξ) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hsmall⟩ := hτ.strongContinuous ξ (2 * C) (by positivity) ε hε
    obtain ⟨N, hN⟩ := hCauchy δ hδ
    refine ⟨N, fun m hm n hn => ?_⟩
    have hnorm : ‖x m - x n‖ ≤ 2 * C := by
      have hb := (norm_sub_le (x m) (x n)).trans (add_le_add (hx m) (hx n))
      linarith
    have hs := hsmall (x m - x n) hnorm (hN m hm n hn)
    change ‖(x m : H →L[ℂ] H) ξ - (x n : H →L[ℂ] H) ξ‖ < ε at hs
    simpa only [dist_eq_norm] using hs
  have hex (ξ : H) := cauchySeq_tendsto_of_complete (hc ξ)
  choose v hv using hex
  let F : H →ₗ[ℂ] H :=
    { toFun := v
      map_add' := by
        intro ξ η
        apply tendsto_nhds_unique (hv (ξ + η))
        simpa only [map_add] using (hv ξ).add (hv η)
      map_smul' := by
        intro c ξ
        apply tendsto_nhds_unique (hv (c • ξ))
        simpa only [map_smul, RingHom.id_apply] using (hv ξ).const_smul c }
  have hF (ξ : H) : ‖F ξ‖ ≤ C * ‖ξ‖ := by
    exact le_of_tendsto (hv ξ).norm
      (Eventually.of_forall fun j => (x j).val.le_of_opNorm_le (hx j) ξ)
  let T : H →L[ℂ] H := F.mkContinuous C hF
  have hT (ξ : H) : Tendsto (fun j => (x j : H →L[ℂ] H) ξ) atTop (𝓝 (T ξ)) := hv ξ
  have hm : T ∈ M := Generator.Tracial.weak_operator_limit_mem M x T (fun ξ η =>
    tendsto_const_nhds.inner (hT ξ))
  let a : Algebra M := ⟨T, hm⟩
  refine ⟨a, ?_, hT, hτ.traceTwoNorm_tendsto_of_strong x a hx hT⟩
  exact T.opNorm_le_bound hC hF

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundaryDiagonal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

section Concrete

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {M : VonNeumannAlgebra H} {τ : FaithfulTracialState (Algebra M)}
variable (J : Algebra M →ₗ[ℂ] E)
variable (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)

include hJ in
/-- Operator closed balls have closed images in a faithful tracial Hilbert
realization, by concrete bounded two-norm completeness. -/
theorem FiniteVectorTrace.isClosed_traceHilbert_ball (hτ : FiniteVectorTrace τ)
    (a : Algebra M) {r : ℝ} (hr : 0 ≤ r) :
    IsClosed (J '' Metric.closedBall a r) := by
  apply isClosed_of_closure_subset
  intro y hy
  obtain ⟨v, hv, hvlim⟩ := mem_closure_iff_seq_limit.mp hy
  choose x hxmem hx using hv
  have hxn (n : ℕ) : ‖x n - a‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hxmem n
  have hxb (n : ℕ) : ‖x n‖ ≤ r + ‖a‖ := by
    calc
      ‖x n‖ = ‖(x n - a) + a‖ := by rw [sub_add_cancel]
      _ ≤ ‖x n - a‖ + ‖a‖ := norm_add_le _ _
      _ ≤ r + ‖a‖ := add_le_add (hxn n) le_rfl
  have hxc : ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      traceTwoNorm τ (x m - x n) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hvlim.cauchySeq ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    simpa only [← hJ, map_sub, hx, dist_eq_norm] using hN m hm n hn
  obtain ⟨b, hb, hstrong, htwo⟩ := hτ.bounded_complete x
    (add_nonneg hr (norm_nonneg a)) hxb hxc
  have hJb : Tendsto v atTop (𝓝 (J b)) := by
    rw [← tendsto_sub_nhds_zero_iff]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [← hx, ← map_sub, hJ] using htwo
  have hyb : J b = y := tendsto_nhds_unique hJb hvlim
  have hbball : b ∈ Metric.closedBall a r := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    apply ContinuousLinearMap.opNorm_le_bound _ hr
    intro ξ
    have hs := (hstrong ξ).sub (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (a : H →L[ℂ] H) ξ) atTop (𝓝 ((a : H →L[ℂ] H) ξ)))
    exact le_of_tendsto hs.norm (Eventually.of_forall fun n =>
      (x n - a).val.le_of_opNorm_le (hxn n) ξ)
  exact ⟨b, hbball, hyb⟩

end Concrete


end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TraceUnitaryClosure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.conjugation_algebraVector _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.TraceQuotientMap.comapEquiv_quotient _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.expectedTrace_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrixSequenceQuotient_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.productBoundaryRepresentation_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.rescaledGraphMap_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.traceStateRepresentation_vector _root_.OAI.KadisonKastler.traceStateRight_vector _root_.OAI.KadisonKastler.traceStateVector_sub _root_.OAI.KadisonKastler.tracialHilbertConjugation_embedding _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceContinuous_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.tracialSequenceValue_one _root_.OAI.KadisonKastler.tracialStarIsometry_embedding _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Closure of unitary vectors in a finite trace representation -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

private theorem star_mul_eq_one_of_trace_norm_one
    (τ : FaithfulTracialState A) (a : A) (ha : ‖a‖ ≤ 1)
    (hτa : traceTwoNorm τ a = 1) : star a * a = 1 := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hb : star a * a ≤ 1 := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg (star a * a)).mp
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg a]
  obtain ⟨c, hc⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (sub_nonneg.mpr hb)
  have ht : τ.toLinearMap (star a * a) = 1 := by
    apply Complex.ext
    · have h := traceTwoNorm_sq τ a
      rw [hτa] at h
      simpa only [one_pow, Complex.one_re] using h.symm
    · simpa only [Complex.one_im] using τ.positive_im a
  have hcτ : τ.toLinearMap (star c * c) = 0 := by
    rw [← hc, map_sub, τ.map_one, ht, sub_self]
  have hc0 := τ.faithful c hcτ
  have hz : (1 : A) - star a * a = 0 := by rw [hc, hc0, star_zero, zero_mul]
  exact (sub_eq_zero.mp hz).symm

/-- A contraction attaining trace two-norm one is unitary. -/
theorem mem_unitary_of_traceTwoNorm_eq_one
    (τ : FaithfulTracialState A) (a : A) (ha : ‖a‖ ≤ 1)
    (hτa : traceTwoNorm τ a = 1) : a ∈ unitary A := by
  refine ⟨star_mul_eq_one_of_trace_norm_one τ a ha hτa, ?_⟩
  simpa only [star_star] using star_mul_eq_one_of_trace_norm_one τ (star a)
    (by simpa only [norm_star] using ha) (by simpa only [traceTwoNorm_star] using hτa)

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] {M : VonNeumannAlgebra H}

/-- The unitary vectors form a closed subset of any faithful tracial
Hilbert realization of a concrete finite algebra. -/
theorem FiniteVectorTrace.isClosed_traceUnitary_image
    {τ : FaithfulTracialState (Algebra M)} (hτ : FiniteVectorTrace τ)
    (J : Algebra M →ₗ[ℂ] E) (hJ : ∀ a, ‖J a‖ = traceTwoNorm τ a) :
    IsClosed (J '' (unitary (Algebra M) : Set (Algebra M))) := by
  have hball : J '' (unitary (Algebra M) : Set (Algebra M)) ⊆
      J '' Metric.closedBall (0 : Algebra M) 1 := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨u, ?_, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      norm_unitary_le_one (⟨u, hu⟩ : unitary (Algebra M))
  have hnorm : J '' (unitary (Algebra M) : Set (Algebra M)) ⊆ {v | ‖v‖ = 1} := by
    rintro _ ⟨u, hu, rfl⟩
    rw [Set.mem_ofPred_eq, hJ]
    simpa only [mul_one, traceTwoNorm_one] using
      traceTwoNorm_unitary_mul τ (⟨u, hu⟩ : unitary (Algebra M)) (1 : Algebra M)
  apply isClosed_of_closure_subset
  intro v hv
  obtain ⟨a, ha, hav⟩ :=
    (closure_minimal hball (hτ.isClosed_traceHilbert_ball J hJ 0 (by norm_num))) hv
  have hvnorm : ‖v‖ = 1 :=
    (closure_minimal hnorm (isClosed_eq continuous_norm continuous_const)) hv
  refine ⟨a, mem_unitary_of_traceTwoNorm_eq_one τ a ?_ ?_, hav⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using ha
  · rw [← hJ, hav, hvnorm]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UnitaryImageLinearMap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The linear map determined by unitary trace vectors

Once every unitary vector has a unitary image, the four-unitary
decomposition constructs a map on the whole algebra. A separating
embedding proves linearity and the quantitative operator-norm bound.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {A B E : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [AddCommGroup E] [Module ℂ E]

/-- A linear map on trace vectors extends to an actual algebra-valued
linear map if it sends every unitary vector to a unitary vector. -/
theorem exists_linear_map_of_unitary_vectors
    (J : A →ₗ[ℂ] E) (K : B →ₗ[ℂ] E) (hK : Function.Injective K)
    (S : E →ₗ[ℂ] E)
    (hU : ∀ u : unitary A, ∃ v : unitary B, K v = S (J u)) :
    ∃ θ : A →ₗ[ℂ] B,
      (∀ a, K (θ a) = S (J a)) ∧ (∀ u : unitary A, θ u ∈ unitary B) := by
  classical
  have hmem (a : A) : ∃ b : B, K b = S (J a) := by
    obtain ⟨u, c, ha, _⟩ := CStarAlgebra.exists_sum_four_unitary a
    choose v hv using fun i => hU (u i)
    refine ⟨∑ i, c i • (v i : B), ?_⟩
    rw [ha]
    simp only [map_sum, map_smul, hv]
  choose T hT using hmem
  let θ : A →ₗ[ℂ] B :=
    { toFun := T
      map_add' := by
        intro a b
        apply hK
        simp only [hT, map_add]
      map_smul' := by
        intro c a
        apply hK
        simp only [hT, map_smul, RingHom.id_apply] }
  refine ⟨θ, hT, ?_⟩
  intro u
  obtain ⟨v, hv⟩ := hU u
  have he : θ u = (v : B) := hK ((hT u).trans hv.symm)
  rw [he]
  exact v.property

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TraceUnitaryImages
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Extending the boundary unitary images to the whole algebra -/

namespace KadisonKastler

noncomputable section

variable {H E I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {M N : VonNeumannAlgebra H}

/-- Closedness of the unitary trace vectors extends the boundary image
formula from a trace-dense family to every unitary. -/
theorem exists_unitary_vector_image_of_traceDense
    (τM : FaithfulTracialState (Algebra M)) (τN : FaithfulTracialState (Algebra N))
    (J : Algebra M →ₗ[ℂ] E) (K : Algebra N →ₗ[ℂ] E)
    (hJ : ∀ a, ‖J a‖ = traceTwoNorm τM a)
    (hK : ∀ a, ‖K a‖ = traceTwoNorm τN a) (hτN : FiniteVectorTrace τN)
    (ρ : I → unitary (Algebra M))
    (hρ : ∀ u : unitary (Algebra M), ∀ ε : ℝ, 0 < ε →
      ∃ i, traceTwoNorm τM ((u : Algebra M) - ρ i) < ε)
    (S : unitary (E →L[ℂ] E))
    (himages : ∀ i, ∃ v : unitary (Algebra N), K v = (S : E →L[ℂ] E) (J (ρ i)))
    (u : unitary (Algebra M)) :
    ∃ v : unitary (Algebra N), K v = (S : E →L[ℂ] E) (J u) := by
  have hclosed := hτN.isClosed_traceUnitary_image K hK
  have hmem : (S : E →L[ℂ] E) (J u) ∈
      K '' (unitary (Algebra N) : Set (Algebra N)) := by
    apply hclosed.closure_subset
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨i, hi⟩ := hρ u ε hε
    obtain ⟨v, hv⟩ := himages i
    refine ⟨K v, ⟨v, v.property, rfl⟩, ?_⟩
    rw [hv, dist_eq_norm, ← map_sub, Unitary.norm_map, ← map_sub, hJ]
    exact hi
  obtain ⟨v, hv, he⟩ := hmem
  exact ⟨⟨v, hv⟩, he⟩

/-- The normalized boundary unitary defines a unital linear map into
the neighboring algebra and sends every unitary to a unitary. -/
theorem exists_unital_linear_transfer_of_traceDense
    (τM : FaithfulTracialState (Algebra M)) (τN : FaithfulTracialState (Algebra N))
    (J : Algebra M →ₗ[ℂ] E) (K : Algebra N →ₗ[ℂ] E)
    (hJ : ∀ a, ‖J a‖ = traceTwoNorm τM a)
    (hK : ∀ a, ‖K a‖ = traceTwoNorm τN a) (hτN : FiniteVectorTrace τN)
    (ρ : I → unitary (Algebra M))
    (hρ : ∀ u : unitary (Algebra M), ∀ ε : ℝ, 0 < ε →
      ∃ i, traceTwoNorm τM ((u : Algebra M) - ρ i) < ε)
    (S : unitary (E →L[ℂ] E)) (hS1 : (S : E →L[ℂ] E) (J 1) = K 1)
    (himages : ∀ i, ∃ v : unitary (Algebra N), K v = (S : E →L[ℂ] E) (J (ρ i))) :
    ∃ θ : Algebra M →ₗ[ℂ] Algebra N,
      θ 1 = 1 ∧ (∀ a, K (θ a) = (S : E →L[ℂ] E) (J a)) ∧
      (∀ u : unitary (Algebra M), θ u ∈ unitary (Algebra N)) := by
  obtain ⟨θ, hθ, hθU⟩ := exists_linear_map_of_unitary_vectors J K
    (traceHilbert_injective K hK) (S : E →L[ℂ] E).toLinearMap
    (exists_unitary_vector_image_of_traceDense τM τN J K hJ hK hτN ρ hρ S himages)
  refine ⟨θ, ?_, hθ, hθU⟩
  apply traceHilbert_injective K hK
  exact (hθ 1).trans hS1

/-- The algebra transfer constructed from the boundary images is also
continuous in the operator norm, as needed for spectral approximation. -/
theorem exists_continuous_unital_transfer_of_traceDense_oai
    (τM : FaithfulTracialState (Algebra M)) (τN : FaithfulTracialState (Algebra N))
    (J : Algebra M →ₗ[ℂ] E) (K : Algebra N →ₗ[ℂ] E)
    (hJ : ∀ a, ‖J a‖ = traceTwoNorm τM a)
    (hK : ∀ a, ‖K a‖ = traceTwoNorm τN a) (hτN : FiniteVectorTrace τN)
    (ρ : I → unitary (Algebra M))
    (hρ : ∀ u : unitary (Algebra M), ∀ ε : ℝ, 0 < ε →
      ∃ i, traceTwoNorm τM ((u : Algebra M) - ρ i) < ε)
    (S : unitary (E →L[ℂ] E)) (hS1 : (S : E →L[ℂ] E) (J 1) = K 1)
    (himages : ∀ i, ∃ v : unitary (Algebra N), K v = (S : E →L[ℂ] E) (J (ρ i))) :
    ∃ θ : Algebra M →L[ℂ] Algebra N,
      θ 1 = 1 ∧ (∀ a, K (θ a) = (S : E →L[ℂ] E) (J a)) ∧
      (∀ u : unitary (Algebra M), θ u ∈ unitary (Algebra N)) := by
  obtain ⟨θ, hθ1, hθ, hθU⟩ := exists_unital_linear_transfer_of_traceDense
    τM τN J K hJ hK hτN ρ hρ S hS1 himages
  exact ⟨continuousLinearMapOfUnitaryImages θ hθU, hθ1, hθ, hθU⟩

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.KadisonKastler.exists_continuous_unital_transfer_of_traceDense_oai.{u_1, u_2, u_3} := @OAI.KadisonKastler.exists_continuous_unital_transfer_of_traceDense_oai.{u_1, u_2, u_3}
