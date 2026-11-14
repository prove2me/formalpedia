-- Prove2me | solution 1 for OAI.KadisonKastler.hasFixedRowFactorization_of_mem_orbitClosure
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:11:08.969985+00:00
-- url     : https://prove2.me/submissions/3c9fb4bf-a8b9-42e1-a9cb-1b6cfb6378d8

import Mathlib
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
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
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
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
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
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
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Sequences
import Definitions.Def_Q260K066
import Theorems.Thm_OAI_KadisonKastler_representationRowAverage_norm_le

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RectangularWeakCompact
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Weak operator compactness for the rectangular operators in a fixed
factorization. The source and target Hilbert spaces may differ. -/

namespace KadisonKastler

noncomputable section

open Filter
open scoped Topology InnerProductSpace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace H] in
theorem exists_weak_rectangular_operator_ultralimit {ι : Type*} (ω : Ultrafilter ι)
    (R : ι → H →L[ℂ] K) (d : ℝ) (hd : 0 ≤ d) (hR : ∀ i, ‖R i‖ ≤ d) :
    ∃ T : H →L[ℂ] K, ‖T‖ ≤ d ∧ ∀ ξ η,
      Tendsto (fun i => inner ℂ η (R i ξ)) (ω : Filter ι) (𝓝 (inner ℂ η (T ξ))) := by
  have h (ξ : H) := Generator.Tracial.exists_weak_vector_ultralimit ω
    (fun i => R i ξ) (d * ‖ξ‖) (fun i => (R i).le_of_opNorm_le (hR i) ξ)
  choose v hv ht using h
  have ha (ξ ζ : H) : v (ξ + ζ) = v ξ + v ζ := by
    apply ext_inner_left ℂ
    intro η
    apply tendsto_nhds_unique (ht (ξ + ζ) η)
    simpa only [map_add, inner_add_right] using (ht ξ η).add (ht ζ η)
  have hs (z : ℂ) (ξ : H) : v (z • ξ) = z • v ξ := by
    apply ext_inner_left ℂ
    intro η
    apply tendsto_nhds_unique (ht (z • ξ) η)
    simpa only [map_smul, inner_smul_right] using (ht ξ η).const_mul z
  let T : H →L[ℂ] K := LinearMap.mkContinuous
    { toFun := v, map_add' := ha, map_smul' := hs } d hv
  exact ⟨T, T.opNorm_le_bound hd hv, ht⟩

omit [CompleteSpace H] in
theorem isCompact_weakRectangularBall {d : ℝ} (hd : 0 ≤ d) :
    IsCompact (weakRectangularBall H K d) := by
  classical
  apply isCompact_iff_ultrafilter_le_nhds'.mpr
  intro ω hω
  let R : (H →WOT[ℂ] K) → H →L[ℂ] K := fun T =>
    if ‖T.toCLM‖ ≤ d then T.toCLM else 0
  have hR (T : H →WOT[ℂ] K) : ‖R T‖ ≤ d := by
    dsimp [R]
    split_ifs with h
    · exact h
    · simpa only [norm_zero] using hd
  obtain ⟨T, hT, ht⟩ := exists_weak_rectangular_operator_ultralimit ω R d hd hR
  refine ⟨ContinuousLinearMapWOT.ofCLM T, hT, ?_⟩
  have hl : Tendsto (fun U => ContinuousLinearMapWOT.ofCLM (R U))
      (ω : Filter (H →WOT[ℂ] K)) (𝓝 (ContinuousLinearMapWOT.ofCLM T)) :=
    ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto.mpr ht
  have he : (fun U => ContinuousLinearMapWOT.ofCLM (R U)) =ᶠ[ω] id := by
    filter_upwards [show ∀ᶠ U in (ω : Filter (H →WOT[ℂ] K)),
      U ∈ weakRectangularBall H K d from hω] with U hU
    simp only [weakRectangularBall, Set.mem_ofPred_eq] at hU
    simp only [R, ite_eq_left hU, ContinuousLinearMapWOT.ofCLM_toCLM, id_eq]
  exact hl.congr' he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RowOperatorFactorization
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.traceFreeCopy_inner _root_.OAI.Generator.Tracial.traceFreeHilbertCoefficient_apply _root_.OAI.Generator.Tracial.traceFreeInclusion_inner _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Operator factorizations and their exact behavior under finite row averages.
The representation is supplied by the proved Paulsen--Stinespring construction.
-/

namespace KadisonKastler

noncomputable section

open scoped InnerProductSpace
open BoundedHochschild.KadisonRingrose

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

attribute [local instance] OAI.KadisonKastler.rowFactorOrder
attribute [local instance] OAI.KadisonKastler.rowFactorStarOrder
attribute [local instance] OAI.KadisonKastler.rowFactorOperatorOrder
local instance rowFactorOperatorStarOrder_rbe34c9_1 : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _
theorem finiteRightAverage_operator_factorization {M : VonNeumannAlgebra H}
    (F : Algebra M →ₗ[ℂ] Algebra M)
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L R : H →L[ℂ] K)
    (hF : ∀ a, (F a : H →L[ℂ] H) = L.adjoint.comp ((π a).comp R))
    {ι : Type*} [Fintype ι] (r : ι → Algebra M) (a : Algebra M) :
    (finiteRightAverage r F a : H →L[ℂ] H) =
      L.adjoint.comp ((π a).comp (representationRowAverage π r R)) := by
  ext ξ
  have hsum : (finiteRightAverage r F a : H →L[ℂ] H) =
      ∑ i, (F (a * r i) : H →L[ℂ] H) * (star (r i) : H →L[ℂ] H) := by
    simp [finiteRightAverage_apply]
  rw [hsum]
  simp only [representationRowAverage, sum_apply, ContinuousLinearMap.comp_apply, map_sum,
    mul_apply_eq_comp]
  change (∑ i, (F (a * r i) : H →L[ℂ] H) ((star (r i) : H →L[ℂ] H) ξ)) = _
  simp_rw [hF, map_mul, ContinuousLinearMap.comp_apply, mul_apply_eq_comp]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakRowFactorization
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! A single operator representation factors the entire weak row-orbit closure.
Only its bounded right-hand operator varies at cluster points. -/

namespace KadisonKastler

noncomputable section

open scoped Topology InnerProductSpace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

private theorem factorization_inner {M : VonNeumannAlgebra H}
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L R : H →L[ℂ] K)
    (a : Algebra M) (ξ η : H) :
    inner ℂ η (L.adjoint ((π a) (R ξ))) =
      inner ℂ ((π a).adjoint (L η)) (R ξ) := by
  rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_left]

theorem isClosed_hasFixedRowFactorization {M : VonNeumannAlgebra H} {c d : ℝ}
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L : H →L[ℂ] K) (hd : 0 ≤ d) :
    IsClosed {F : BoundedWeakAlgebraMap M c | HasFixedRowFactorization π L d F} := by
  let B := ↥(weakRectangularBall H K d)
  let : CompactSpace B := isCompact_iff_compactSpace.mp
    (isCompact_weakRectangularBall (H := H) (K := K) hd)
  let S : Set (BoundedWeakAlgebraMap M c × B) := {p | ∀ a ξ η,
    boundedWeakAlgebraCoefficients p.1 (a, ξ, η) =
      inner ℂ ((π a).adjoint (L η)) (p.2.val.toCLM ξ)}
  have hS : IsClosed S := by
    dsimp only [S]
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro a
    apply isClosed_iInter
    intro ξ
    apply isClosed_iInter
    intro η
    have hcoeff : Continuous (boundedWeakAlgebraCoefficients (M := M) (c := c)) :=
      continuous_induced_dom
    exact isClosed_eq (((continuous_apply (a, ξ, η)).comp hcoeff).comp continuous_fst)
      (ContinuousLinearMapWOT.continuous_inner_apply
        (continuous_subtype_val.comp continuous_snd) ξ ((π a).adjoint (L η)))
  have he : Prod.fst '' S =
      {F : BoundedWeakAlgebraMap M c | HasFixedRowFactorization π L d F} := by
    ext F
    constructor
    · rintro ⟨⟨G, R⟩, h, rfl⟩
      refine ⟨R.val.toCLM, R.property, ?_⟩
      intro a
      apply ContinuousLinearMap.ext
      intro ξ
      apply ext_inner_left ℂ
      intro η
      exact (h a ξ η).trans (factorization_inner π L R.val.toCLM a ξ η).symm
    · rintro ⟨R, hR, h⟩
      refine ⟨(F, ⟨ContinuousLinearMapWOT.ofCLM R, hR⟩), ?_, rfl⟩
      intro a ξ η
      change inner ℂ η ((F.map a : H →L[ℂ] H) ξ) = _
      rw [h a]
      exact factorization_inner π L R a ξ η
  rw [← he]
  exact isClosedMap_fst_of_compactSpace S hS

theorem hasFixedRowFactorization_of_mem_orbitClosure_oai {M : VonNeumannAlgebra H}
    {c d : ℝ} (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L : H →L[ℂ] K)
    (hd : 0 ≤ d) {F G : BoundedWeakAlgebraMap M c}
    (hF : HasFixedRowFactorization π L d F) (hG : G ∈ closure (boundedWeakRowOrbit F)) :
    HasFixedRowFactorization π L d G := by
  apply closure_minimal (t := {T | HasFixedRowFactorization π L d T}) ?_
    (isClosed_hasFixedRowFactorization π L hd) hG
  rintro T ⟨n, r, hr, he⟩
  obtain ⟨R, hR, hf⟩ := hF
  refine ⟨representationRowAverage π r R, (representationRowAverage_norm_le π r hr R).trans hR, ?_⟩
  intro a
  rw [he]
  exact finiteRightAverage_operator_factorization F.map π L R hf r a

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.hasFixedRowFactorization_of_mem_orbitClosure_oai.{u_1, u_2} := @OAI.KadisonKastler.hasFixedRowFactorization_of_mem_orbitClosure_oai.{u_1, u_2}
