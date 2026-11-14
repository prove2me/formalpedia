-- Prove2me | solution 1 for OAI.KadisonKastler.scalar_center_of_near_II1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:16:51.45221+00:00
-- url     : https://prove2.me/submissions/b64d100d-97de-4271-a5bb-d8a46109642f

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
import Mathlib.Analysis.Normed.Module.FiniteDimension
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
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K029
import Definitions.Def_Q260K066
import Theorems.Thm_OAI_KadisonKastler_traceHull_mem_ball

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
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.Tracial.conjugateLinear_one _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.quotientInclusion_mk _root_.OAI.Generator.Tracial.quotientInclusion_trace _root_.OAI.Generator.Tracial.traceFreeCopy_inner _root_.OAI.Generator.Tracial.traceFreeHilbertCoefficient_apply _root_.OAI.Generator.Tracial.traceFreeInclusion_inner _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.conjugation_algebraVector _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.TraceQuotientMap.comapEquiv_quotient _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.concreteTraceEmbedding_inner _root_.OAI.KadisonKastler.concreteTraceLeftAction_embedding _root_.OAI.KadisonKastler.concreteTraceLeftUnitary_coe _root_.OAI.KadisonKastler.concreteTraceRightAction_embedding _root_.OAI.KadisonKastler.concreteTraceRightUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.expectedTrace_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrixSequenceQuotient_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.productBoundaryRepresentation_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.realTrace_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.rescaledGraphMap_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.traceCenter_apply _root_.OAI.KadisonKastler.traceStateRepresentation_vector _root_.OAI.KadisonKastler.traceStateRight_vector _root_.OAI.KadisonKastler.traceStateVector_sub _root_.OAI.KadisonKastler.traceTwoNorm_eq_zero_iff _root_.OAI.KadisonKastler.traceTwoNorm_neg _root_.OAI.KadisonKastler.traceTwoNorm_zero _root_.OAI.KadisonKastler.trace_traceCenter _root_.OAI.KadisonKastler.tracialHilbertConjugation_embedding _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceContinuous_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.tracialSequenceValue_one _root_.OAI.KadisonKastler.tracialStarIsometry_embedding _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe _root_.OAI.UltrapowerBridge.quotientMap_smul _root_.OAI.UltrapowerBridge.quotientMap_star _root_.OAI.UltrapowerBridge.quotientTrace_mk _root_.OAI.UltrapowerBridge.quotientTrace_one
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
local instance concreteTracePreorder_r636b0d_1 : Preorder (Algebra M) := (CStarAlgebra.spectralOrder _).toPreorder
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
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.Tracial.conjugateLinear_one _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.quotientInclusion_mk _root_.OAI.Generator.Tracial.quotientInclusion_trace _root_.OAI.Generator.Tracial.traceFreeCopy_inner _root_.OAI.Generator.Tracial.traceFreeHilbertCoefficient_apply _root_.OAI.Generator.Tracial.traceFreeInclusion_inner _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.conjugation_algebraVector _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.TraceQuotientMap.comapEquiv_quotient _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.concreteTraceEmbedding_inner _root_.OAI.KadisonKastler.concreteTraceLeftAction_embedding _root_.OAI.KadisonKastler.concreteTraceLeftUnitary_coe _root_.OAI.KadisonKastler.concreteTraceRightAction_embedding _root_.OAI.KadisonKastler.concreteTraceRightUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.expectedTrace_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrixSequenceQuotient_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.productBoundaryRepresentation_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.realTrace_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.rescaledGraphMap_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.traceStateRepresentation_vector _root_.OAI.KadisonKastler.traceStateRight_vector _root_.OAI.KadisonKastler.traceStateVector_sub _root_.OAI.KadisonKastler.tracialHilbertConjugation_embedding _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceContinuous_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.tracialSequenceValue_one _root_.OAI.KadisonKastler.tracialStarIsometry_embedding _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe _root_.OAI.UltrapowerBridge.quotientMap_smul _root_.OAI.UltrapowerBridge.quotientMap_star _root_.OAI.UltrapowerBridge.quotientTrace_mk _root_.OAI.UltrapowerBridge.quotientTrace_one
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
/-- A nonempty family of contractions near one has an actual unique
least-two-norm operator in its trace Hilbert closed convex hull. -/
theorem exists_unique_diagonal_least [CompleteSpace E]
    (hτ : FiniteVectorTrace τ) {s : Set (Algebra M)} (hsne : s.Nonempty)
    {r : ℝ} (hr : 0 ≤ r) (hs1 : ∀ x ∈ s, ‖x‖ ≤ 1)
    (hsr : ∀ x ∈ s, ‖x - 1‖ ≤ r) :
    ∃! b : Algebra M, J b ∈ diagonalTraceHull J s ∧ ‖b‖ ≤ 1 ∧ ‖b - 1‖ ≤ r ∧
      ∀ z ∈ diagonalTraceHull J s, ‖J b‖ ≤ ‖z‖ := by
  obtain ⟨z, hz, hzu⟩ := exists_unique_least_norm
    (show (diagonalTraceHull J s).Nonempty from by
      obtain ⟨x, hx⟩ := hsne
      exact ⟨J x, subset_closure ⟨x, subset_convexHull ℝ s hx, rfl⟩⟩)
    isClosed_closure (diagonalTraceHull_convex J s)
  obtain ⟨b, hbz, hbr⟩ := traceHull_mem_ball J hJ hτ 1 hr hsr hz.1
  obtain ⟨c, hcz, hc1⟩ := traceHull_mem_ball J hJ hτ 0 (r := 1) (by norm_num)
    (fun x hx => by simpa only [sub_zero] using hs1 x hx) hz.1
  have hbc : b = c := traceHilbert_injective J hJ (hbz.trans hcz.symm)
  have hb1 : ‖b‖ ≤ 1 := by simpa only [hbc, sub_zero] using hc1
  refine ⟨b, ⟨hbz ▸ hz.1, hb1, hbr, hbz ▸ hz.2⟩, ?_⟩
  intro c hc
  apply traceHilbert_injective J hJ
  exact (hzu (J c) ⟨hc.1, hc.2.2.2⟩).trans hbz.symm


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
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteCenter
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.conjugation_algebraVector _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.TraceQuotientMap.comapEquiv_quotient _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.concreteTraceEmbedding_inner _root_.OAI.KadisonKastler.concreteTraceLeftAction_embedding _root_.OAI.KadisonKastler.concreteTraceLeftUnitary_coe _root_.OAI.KadisonKastler.concreteTraceRightAction_embedding _root_.OAI.KadisonKastler.concreteTraceRightUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.expectedTrace_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrixSequenceQuotient_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.productBoundaryRepresentation_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.realTrace_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.rescaledGraphMap_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.traceStateRepresentation_vector _root_.OAI.KadisonKastler.traceStateRight_vector _root_.OAI.KadisonKastler.traceStateVector_sub _root_.OAI.KadisonKastler.tracialHilbertConjugation_embedding _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceContinuous_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.tracialSequenceValue_one _root_.OAI.KadisonKastler.tracialStarIsometry_embedding _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Scalar orbit averages and central projections of a nearby algebra

Least vectors in the trace Hilbert space give scalar orbit averages in a
finite factor. Operator-norm balls centred at ambient operators are retained
under this averaging, even when their centre is outside the factor.
-/

namespace KadisonKastler

open Filter Set
open scoped Topology

noncomputable section

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {M : VonNeumannAlgebra H} {τ : FaithfulTracialState (Algebra M)}

/-- Trace convex hulls of uniformly bounded operators retain norm bounds
relative to an arbitrary ambient operator. -/
theorem traceHull_mem_external_ball (J : Algebra M →ₗ[ℂ] E)
    (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x) (hτ : FiniteVectorTrace τ)
    {s : Set (Algebra M)} {C r : ℝ} (hC : 0 ≤ C) (hr : 0 ≤ r)
    (a : H →L[ℂ] H) (hsC : ∀ x ∈ s, ‖x‖ ≤ C)
    (hsr : ∀ x ∈ s, ‖(x : H →L[ℂ] H) - a‖ ≤ r)
    {z : E} (hz : z ∈ diagonalTraceHull J s) :
    ∃ b : Algebra M, J b = z ∧ ‖(b : H →L[ℂ] H) - a‖ ≤ r := by
  have hcC : ∀ x ∈ convexHull ℝ s, ‖x‖ ≤ C := by
    have h := convexHull_min (t := Metric.closedBall (0 : Algebra M) C)
      (fun x hx => by simpa only [Metric.mem_closedBall, dist_zero_right] using hsC x hx)
      (convex_closedBall _ _)
    intro x hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using h hx
  have hcr : ∀ x ∈ convexHull ℝ s, ‖(x : H →L[ℂ] H) - a‖ ≤ r := by
    have hv : Convex ℝ {x : Algebra M | ‖(x : H →L[ℂ] H) - a‖ ≤ r} := by
      have he := (convex_closedBall a r).linear_preimage
        (M.toStarSubalgebra.subtype.toLinearMap.restrictScalars ℝ)
      have heq : {x : Algebra M | ‖(x : H →L[ℂ] H) - a‖ ≤ r} =
          (fun x : Algebra M => (x : H →L[ℂ] H)) ⁻¹' Metric.closedBall a r := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
      rw [heq]
      exact he
    exact convexHull_min hsr hv
  obtain ⟨v, hv, hvlim⟩ := mem_closure_iff_seq_limit.mp hz
  choose x hxmem hx using hv
  have hxc : ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      traceTwoNorm τ (x m - x n) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hvlim.cauchySeq ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    simpa only [← hJ, map_sub, hx, dist_eq_norm] using hN m hm n hn
  obtain ⟨b, _, hstrong, htwo⟩ := hτ.bounded_complete x hC
    (fun n => hcC _ (hxmem n)) hxc
  have hJb : Tendsto v atTop (𝓝 (J b)) := by
    rw [← tendsto_sub_nhds_zero_iff]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [← hx, ← map_sub, hJ] using htwo
  refine ⟨b, tendsto_nhds_unique hJb hvlim, ?_⟩
  apply ContinuousLinearMap.opNorm_le_bound _ hr
  intro ξ
  have hs := (hstrong ξ).sub (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => a ξ) atTop (𝓝 (a ξ)))
  exact le_of_tendsto hs.norm (Eventually.of_forall fun n =>
    ((x n : H →L[ℂ] H) - a).le_of_opNorm_le (hcr _ (hxmem n)) ξ)

/-- A bounded unitary orbit in a finite factor has a scalar in its trace
closed convex hull. -/
theorem exists_scalar_in_traceOrbit [CompleteSpace E]
    (J : Algebra M →ₗ[ℂ] E) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (hτ : FiniteVectorTrace τ)
    (hfactor : ∀ b : Algebra M, (∀ x : Algebra M, x * b = b * x) →
      ∃ c : ℂ, b = c • (1 : Algebra M))
    (a : Algebra M) (ha : ‖a‖ ≤ 1) :
    ∃ c : ℂ, J (c • (1 : Algebra M)) ∈ diagonalTraceHull J (unitaryConjugacyOrbit a) := by
  have horbit : ∀ x ∈ unitaryConjugacyOrbit a, ‖x‖ ≤ 1 := by
    rintro _ ⟨u, rfl⟩
    simpa only [CStarRing.norm_coe_unitary_mul, CStarRing.norm_mul_coe_unitary,
      ← Unitary.coe_star] using ha
  obtain ⟨b, hb, _⟩ := exists_unique_diagonal_least J hJ hτ
    (show (unitaryConjugacyOrbit a).Nonempty from ⟨a, ⟨1, by simp⟩⟩)
    (r := 2) (by norm_num) horbit (fun x hx => by
      have h := (norm_sub_le x 1).trans (add_le_add (horbit x hx)
        (norm_unitary_le_one (1 : unitary (Algebra M))))
      exact h.trans (by norm_num))
  have hfix (u : unitary (Algebra M)) : b = (u : Algebra M) * b * star (u : Algebra M) := by
    apply diagonal_least_covariance J hJ u u
      (s := unitaryConjugacyOrbit a) (t := unitaryConjugacyOrbit a)
      ?_ ?_ hb.1 hb.1 hb.2.2.2 hb.2.2.2
    · rintro _ ⟨v, rfl⟩
      exact ⟨u * v, by simp only [Submonoid.coe_mul, star_mul, mul_assoc]⟩
    · rintro _ ⟨v, rfl⟩
      exact ⟨star u * v, by simp only [Submonoid.coe_mul, Unitary.coe_star, star_mul,
        star_star, mul_assoc]⟩
  have hcomm (u : unitary (Algebra M)) : (u : Algebra M) * b = b * u := by
    have he := congrArg (fun x : Algebra M => x * (u : Algebra M)) (hfix u)
    simpa only [mul_assoc, Unitary.star_mul_self_of_mem u.property, mul_one] using he.symm
  let T : Algebra M →ₗ[ℂ] Algebra M := LinearMap.mulRight ℂ b - LinearMap.mulLeft ℂ b
  have hcentral (x : Algebra M) : x * b = b * x := by
    have hn := norm_le_twice_unitary_bound T (C := 0) (fun u => by
      change ‖(u : Algebra M) * b - b * u‖ ≤ 0
      rw [hcomm, sub_self, norm_zero]) x
    have hz : T x = 0 := norm_eq_zero.mp (le_antisymm (by simpa using hn) (norm_nonneg _))
    exact sub_eq_zero.mp hz
  obtain ⟨c, rfl⟩ := hfactor b hcentral
  exact ⟨c, hb.1⟩

/-- A contraction all of whose conjugates stay near an ambient operator
has a scalar near that same operator. -/
theorem exists_scalar_near_of_unitary_orbit [CompleteSpace E]
    (J : Algebra M →ₗ[ℂ] E) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (hτ : FiniteVectorTrace τ)
    (hfactor : ∀ b : Algebra M, (∀ x : Algebra M, x * b = b * x) →
      ∃ c : ℂ, b = c • (1 : Algebra M))
    (a : Algebra M) (ha : ‖a‖ ≤ 1) (q : H →L[ℂ] H) {r : ℝ} (hr : 0 ≤ r)
    (hclose : ∀ u : unitary (Algebra M),
      ‖((u : Algebra M) * a * star (u : Algebra M) : Algebra M).val - q‖ ≤ r) :
    ∃ c : ℂ, ‖c • (1 : H →L[ℂ] H) - q‖ ≤ r := by
  obtain ⟨c, hc⟩ := exists_scalar_in_traceOrbit J hJ hτ hfactor a ha
  obtain ⟨b, hb, hbq⟩ := traceHull_mem_external_ball J hJ hτ (by norm_num : (0 : ℝ) ≤ 1)
    hr q (s := unitaryConjugacyOrbit a) (by
      rintro _ ⟨u, rfl⟩
      simpa only [CStarRing.norm_coe_unitary_mul, CStarRing.norm_mul_coe_unitary,
        ← Unitary.coe_star] using ha) (by rintro _ ⟨u, rfl⟩; exact hclose u) hc
  have he : b = c • (1 : Algebra M) := traceHilbert_injective J hJ hb
  refine ⟨c, ?_⟩
  rw [he] at hbq
  exact hbq


/-- A projection within one half of a scalar is trivial. -/
theorem projection_eq_zero_or_one_of_near_scalar {A : Type*} [CStarAlgebra A]
    (q : A) (hq : IsStarProjection q) (c : ℂ)
    (hclose : ‖c • (1 : A) - q‖ < 1 / 2) : q = 0 ∨ q = 1 := by
  by_contra hn
  push Not at hn
  have hnq : ‖q‖ = 1 := by
    have hh := (CStarRing.norm_star_mul_self (x := q))
    rw [hq.isSelfAdjoint.star_eq, hq.isIdempotentElem.eq] at hh
    nlinarith [norm_pos_iff.mpr hn.1]
  have hcomp : ‖1 - q‖ = 1 := by
    have hh := (CStarRing.norm_star_mul_self (x := 1 - q))
    rw [hq.one_sub.isSelfAdjoint.star_eq, hq.one_sub.isIdempotentElem.eq] at hh
    have hne : (1 : A) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hn.2)
    nlinarith [norm_pos_iff.mpr hne]
  have hmul : (c • (1 : A) - q) * q = (c - 1) • q := by
    simp only [sub_mul, smul_mul_assoc, one_mul, hq.isIdempotentElem.eq,
      sub_smul, one_smul]
  have hmul' : (c • (1 : A) - q) * (1 - q) = c • (1 - q) := by
    rw [sub_mul, smul_mul_assoc, one_mul, hq.mul_one_sub_self, sub_zero]
  have hc : ‖c‖ < 1 / 2 := by
    have h := norm_mul_le (c • (1 : A) - q) (1 - q)
    rw [hmul', norm_smul, hcomp, mul_one, mul_one] at h
    exact h.trans_lt hclose
  have hc1 : ‖c - 1‖ < 1 / 2 := by
    have h := norm_mul_le (c • (1 : A) - q) q
    rw [hmul, norm_smul, hnq, mul_one, mul_one] at h
    exact h.trans_lt hclose
  have htri := norm_sub_le c (c - 1)
  rw [sub_sub_cancel, norm_one] at htri
  linarith

/-- A central projection in an algebra within one tenth of a finite
factor is zero or one. The trace data are supplied separately. -/
theorem central_projection_trivial_of_near [CompleteSpace E]
    (J : Algebra M →ₗ[ℂ] E) (hJ : ∀ x, ‖J x‖ = traceTwoNorm τ x)
    (hτ : FiniteVectorTrace τ)
    (hfactor : ∀ b : Algebra M, (∀ x : Algebra M, x * b = b * x) →
      ∃ c : ℂ, b = c • (1 : Algebra M))
    {N : VonNeumannAlgebra H} (hgap : kkDistance M N < 1 / 10)
    (q : Algebra N) (hq : IsStarProjection q)
    (hcentral : ∀ b : Algebra N, b * q = q * b) : q = 0 ∨ q = 1 := by
  have hqa : IsStarProjection (q : H →L[ℂ] H) := by
    exact ⟨congrArg Subtype.val hq.isIdempotentElem.eq,
      congrArg Subtype.val hq.isSelfAdjoint.star_eq⟩
  obtain ⟨a, ha, haq⟩ := exists_unitBall_approx (M := N) (N := M)
    ⟨q.property, hqa.norm_le⟩ (by simpa only [kkDistance_comm N M] using hgap)
  let aM : Algebra M := ⟨a, ha.1⟩
  have horbit (u : unitary (Algebra M)) :
      ‖((u : Algebra M) * aM * star (u : Algebra M) : Algebra M).val - q.val‖ ≤ 3 / 10 := by
    let U : unitary (H →L[ℂ] H) :=
      Unitary.map (StarMonoidHom.ofClass M.toStarSubalgebra.subtype) u
    obtain ⟨b, hb, hub⟩ := exists_unitBall_approx (M := M) (N := N)
      ⟨u.val.property, norm_unitary_le_one U⟩ hgap
    change ‖(U : H →L[ℂ] H) - b‖ < 1 / 10 at hub
    have hbq : b * q.val = q.val * b := congrArg Subtype.val (hcentral ⟨b, hb.1⟩)
    have hdecomp : (U : H →L[ℂ] H) * q.val - q.val * U =
        ((U : H →L[ℂ] H) - b) * q.val - q.val * ((U : H →L[ℂ] H) - b) := by
      rw [sub_mul, mul_sub, hbq]
      abel
    have hcomm : ‖(U : H →L[ℂ] H) * q.val - q.val * U‖ < 2 * (1 / 10 : ℝ) := by
      calc
        _ ≤ ‖((U : H →L[ℂ] H) - b) * q.val‖ +
            ‖q.val * ((U : H →L[ℂ] H) - b)‖ := hdecomp ▸ norm_sub_le _ _
        _ ≤ ‖(U : H →L[ℂ] H) - b‖ * ‖q.val‖ +
            ‖q.val‖ * ‖(U : H →L[ℂ] H) - b‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ 2 * ‖(U : H →L[ℂ] H) - b‖ := by
          nlinarith [mul_le_mul_of_nonneg_left hqa.norm_le (norm_nonneg ((U : H →L[ℂ] H) - b))]
        _ < _ := by nlinarith
    have he : (U : H →L[ℂ] H) * a * star (U : H →L[ℂ] H) - q.val =
        (U : H →L[ℂ] H) * (a - q.val) * star (U : H →L[ℂ] H) +
          ((U : H →L[ℂ] H) * q.val - q.val * U) * star (U : H →L[ℂ] H) := by
      rw [sub_mul, mul_assoc q.val, Unitary.mul_star_self_of_mem U.property, mul_one]
      noncomm_ring
    change ‖(U : H →L[ℂ] H) * a * star (U : H →L[ℂ] H) - q.val‖ ≤ _
    rw [he]
    have htri := norm_add_le ((U : H →L[ℂ] H) * (a - q.val) * star (U : H →L[ℂ] H))
      (((U : H →L[ℂ] H) * q.val - q.val * U) * star (U : H →L[ℂ] H))
    rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
      CStarRing.norm_coe_unitary_mul, CStarRing.norm_mul_coe_unitary] at htri
    rw [norm_sub_rev] at haq
    simp only [Unitary.coe_star] at htri
    linarith
  obtain ⟨c, hc⟩ := exists_scalar_near_of_unitary_orbit J hJ hτ hfactor aM ha.2 q.val
    (by norm_num : (0 : ℝ) ≤ 3 / 10) horbit
  have htriv := projection_eq_zero_or_one_of_near_scalar q.val hqa c (hc.trans_lt (by norm_num))
  exact htriv.imp (fun h => Subtype.ext h) (fun h => Subtype.ext h)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CenterAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Recovering scalar centre from central projections

The centre is represented as the intersection with the concrete commutant.
Spectral approximation in this von Neumann algebra reduces scalarity of its
whole algebra to triviality of its projections.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Spectral approximation upgrades trivial central projections to scalar
centre. No finiteness or trace is needed for this upgrade. -/
theorem scalar_center_of_trivial_central_projections (N : VonNeumannAlgebra H)
    (hproj : ∀ q : Algebra N, IsStarProjection q →
      (∀ a : Algebra N, a * q = q * a) → q = 0 ∨ q = 1)
    (c : Algebra N) (hc : ∀ a : Algebra N, a * c = c * a) :
    ∃ z : ℂ, c = z • (1 : Algebra N) := by
  let C := concreteCenter N
  let inc : Algebra C →⋆ₐ[ℂ] Algebra N := StarSubalgebra.inclusion (show
      C.toStarSubalgebra ≤ N.toStarSubalgebra from fun _ hx => hx.1)
  have hinj : Function.Injective inc := StarSubalgebra.inclusion_injective _
  let cC : Algebra C := ⟨c.val, c.property, by
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro a ha
    exact congrArg Subtype.val (hc ⟨a, ha⟩)⟩
  let p : Generator.Tracial.AlgebraProjection C := ⟨1, IsStarProjection.one _⟩
  have hmin : ∀ q : Generator.Tracial.AlgebraProjection C, q ≤ p → q.val = 0 ∨ q.val = p.val := by
    intro q _
    have hq : IsStarProjection (inc q.val) := q.property.map inc
    have hqc : ∀ a : Algebra N, a * inc q.val = inc q.val * a := by
      intro a
      apply Subtype.ext
      exact VonNeumannAlgebra.mem_commutant_iff.mp q.val.property.2 a.val a.property
    rcases hproj (inc q.val) hq hqc with h | h
    · left
      apply hinj
      change inc q.val = inc 0
      rw [map_zero]
      exact h
    · right
      apply hinj
      change inc q.val = inc 1
      rw [map_one]
      exact h
  obtain ⟨z, hz⟩ := Generator.Tracial.corner_scalar_of_projections p hmin cC
    (by change 1 * cC = cC; exact one_mul _) (by change cC * 1 = cC; exact mul_one _)
  refine ⟨z, ?_⟩
  have he := congrArg (fun x : Algebra C => (x : H →L[ℂ] H)) hz
  exact Subtype.ext he

/-- The nearby algebra has scalar centre; the faithful trace is constructed
from the given concrete II₁ factor. -/
theorem scalar_center_of_near_II1_oai {M N : VonNeumannAlgebra H}
    (hM : Generator.IsII1Factor M.toStarSubalgebra)
    (hgap : kkDistance M N < 1 / 10) :
    ∀ c : Algebra N, (∀ a : Algebra N, a * c = c * a) →
      ∃ z : ℂ, c = z • (1 : Algebra N) := by
  apply scalar_center_of_trivial_central_projections
  intro q hq hqc
  exact central_projection_trivial_of_near (concreteTraceEmbedding hM)
    (concreteTraceEmbedding_norm hM) (concreteFactorTrace_finiteVector hM)
    (fun b hb => by
      obtain ⟨c, hc⟩ := hM.factor b hb
      exact ⟨c, by simpa only [Algebra.algebraMap_eq_smul_one] using hc⟩)
    hgap q hq hqc


end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.scalar_center_of_near_II1_oai.{u_1} := @OAI.KadisonKastler.scalar_center_of_near_II1_oai.{u_1}
