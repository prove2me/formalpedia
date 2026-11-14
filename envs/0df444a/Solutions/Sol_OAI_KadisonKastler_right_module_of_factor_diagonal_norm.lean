-- Prove2me | solution 1 for OAI.KadisonKastler.right_module_of_factor_diagonal_norm
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:07:39.436198+00:00
-- url     : https://prove2.me/submissions/cb6fa5e9-1d65-432c-95d8-54051e880212

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

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CornerSpectralWitness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.traceFreeCopy_inner _root_.OAI.Generator.Tracial.traceFreeHilbertCoefficient_apply _root_.OAI.Generator.Tracial.traceFreeInclusion_inner _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! A nonzero operator supported on a projection has a nonzero spectral
subprojection on which its square is uniformly bounded below. -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

attribute [local instance] OAI.KadisonKastler.cornerWitnessOrder
attribute [local instance] OAI.KadisonKastler.cornerWitnessPreorder
attribute [local instance] OAI.KadisonKastler.cornerWitnessLE
local instance cornerWitnessStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

theorem exists_corner_spectral_lower_bound (e : AlgebraProjection M)
    (b : Algebra M) (hb : b * e.val = b) (hbn : b ≠ 0) :
    ∃ (p : AlgebraProjection M) (t : ℝ), p ≤ e ∧ p.val ≠ 0 ∧ 0 < t ∧
      t • p.val ≤ p.val * (star b * b) * p.val := by
  let a : Algebra M := star b * b
  let t : ℝ := ‖a‖ / 2
  have ha : 0 ≤ a := star_mul_self_nonneg b
  have han : 0 < ‖a‖ := norm_pos_iff.mpr (fun h =>
    hbn ((CStarRing.star_mul_self_eq_zero_iff b).mp h))
  have ht : 0 < t := by dsimp [t] <;> positivity
  have hea : e.val * a * e.val = a := by
    have hs : e.val * star b = star b := by
      simpa only [star_mul, e.property.isSelfAdjoint.star_eq] using congrArg star hb
    dsimp [a]
    rw [← mul_assoc, hs, mul_assoc, hb]
  let p := cornerSpectralCut e a t
  have hp : p ≤ e := cornerSpectralCut_le e a (IsSelfAdjoint.star_mul_self b) t
  have hpn : p.val ≠ 0 := by
    intro hz
    have hu := cornerSpectralCut_upper e a (IsSelfAdjoint.star_mul_self b) t
    change (e.val - p.val) * a * (e.val - p.val) - (t : ℂ) • (e.val - p.val) ≤ 0 at hu
    rw [hz, sub_zero, hea] at hu
    have hle : a ≤ t • e.val := by
      simpa only [Complex.coe_smul] using sub_nonpos.mp hu
    have het : t • e.val ≤ t • (1 : Algebra M) :=
      smul_le_smul_of_nonneg_left e.property.le_one ht.le
    have hbound : a ≤ algebraMap ℝ (Algebra M) t := by
      simpa only [Algebra.algebraMap_eq_smul_one] using hle.trans het
    have hn := (CStarAlgebra.norm_le_iff_le_algebraMap a ht.le ha).mpr hbound
    dsimp [t] at hn
    change ‖a‖ ≤ ‖a‖ / 2 at hn
    linarith
  refine ⟨p, t, hp, hpn, ht, ?_⟩
  have hl := cornerSpectralCut_lower e a (IsSelfAdjoint.star_mul_self b) t
  exact sub_nonneg.mp (by simpa only [Complex.coe_smul] using hl)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionModuleMaps
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Norm spectral approximation reduces right modularity to projection tests. -/

namespace KadisonKastler

noncomputable section

open Generator.Tracial
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.projectionSpanOrder
local instance projectionSpanStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

theorem selfAdjoint_mem_closed_algebra_projection_span (M : VonNeumannAlgebra H)
    (x : Algebra M) (hx : IsSelfAdjoint x) :
    x ∈ (Submodule.span ℂ {p : Algebra M | IsStarProjection p}).topologicalClosure := by
  classical
  change x ∈ closure (Submodule.span ℂ {p : Algebra M | IsStarProjection p} : Set _)
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  let p : AlgebraProjection M := ⟨1, IsStarProjection.one _⟩
  obtain ⟨Q, c, _, hc⟩ := exists_finite_spectral_approximation p x hx ε hε
  refine ⟨∑ i, (c i : ℂ) • (Q.piece i).val, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Q.piece i).property)
  · simpa only [p, one_mul, mul_one, dist_eq_norm] using hc

theorem algebra_closed_projection_span_eq_top (M : VonNeumannAlgebra H) :
    (Submodule.span ℂ {p : Algebra M | IsStarProjection p}).topologicalClosure = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨a, ha, _, hsum⟩ := CStarAlgebra.exists_sum_four_nonneg x
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
    (selfAdjoint_mem_closed_algebra_projection_span M (a i) (ha i).isSelfAdjoint)

/-- A bounded map is right modular as soon as it is fixed by each projection
pinching. No continuity in the weak topology is required. -/
theorem right_module_of_projection_tests (M : VonNeumannAlgebra H)
    (F : Algebra M →L[ℂ] Algebra M)
    (hF : ∀ p : Algebra M, IsStarProjection p → ∀ x, F (x * p) = F x * p) :
    ∀ x y, F (x * y) = F x * y := by
  intro x y
  have hs : (Submodule.span ℂ {p : Algebra M | IsStarProjection p} : Set _) ⊆
      {b | F (x * b) = F x * b} := by
    intro b hb
    induction hb using Submodule.span_induction with
    | mem p hp => exact hF p hp x
    | zero =>
      change F (x * 0) = F x * 0
      simp only [mul_zero, map_zero]
    | add a b ha hb hia hib =>
      change F (x * a) = F x * a at hia
      change F (x * b) = F x * b at hib
      change F (x * (a + b)) = F x * (a + b)
      simp only [mul_add, map_add, hia, hib]
    | smul z a ha hia =>
      change F (x * a) = F x * a at hia
      change F (x * (z • a)) = F x * (z • a)
      simp only [mul_smul_comm, map_smul, hia]
  have hc : IsClosed {b : Algebra M | F (x * b) = F x * b} :=
    isClosed_eq (F.continuous.comp (continuous_const.mul continuous_id))
      (continuous_const.mul continuous_id)
  apply closure_minimal hs hc
  rw [← Submodule.topologicalClosure_coe, algebra_closed_projection_span_eq_top]
  trivial

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HilbertNormGap
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Scalar Hilbert-space norm estimates for the spectral-cut step in
Paulsen's averaging proof (JFA157 (1998), proof of Theorem5.8, pp379–380).
-/

namespace KadisonKastler

noncomputable section

open scoped InnerProductSpace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem opNorm_sq_le_of_pointwise_sq_le (T : H →L[ℂ] K) {c : ℝ} (hc : 0 ≤ c)
    (hT : ∀ ξ, ‖T ξ‖ ^ 2 ≤ c * ‖ξ‖ ^ 2) : ‖T‖ ^ 2 ≤ c := by
  have hb : ‖T‖ ≤ Real.sqrt c := by
    apply T.opNorm_le_bound (Real.sqrt_nonneg c)
    intro ξ
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg ξ))).mp
    rw [mul_pow, Real.sq_sqrt hc]
    exact hT ξ
  nlinarith [Real.sq_sqrt hc, Real.sqrt_nonneg c, norm_nonneg T]

theorem not_uniform_positive_norm_gap [Nontrivial H] (T : H →L[ℂ] K)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ ξ, ‖T ξ‖ ^ 2 + δ * ‖ξ‖ ^ 2 ≤ ‖T‖ ^ 2 * ‖ξ‖ ^ 2) : False := by
  let : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H
  obtain ⟨ξ, hξ⟩ := exists_norm_eq H (show (0 : ℝ) ≤ 1 by norm_num)
  have hpoint := hgap ξ
  rw [hξ, one_pow, mul_one, mul_one] at hpoint
  have hc : 0 ≤ ‖T‖ ^ 2 - δ := by nlinarith [sq_nonneg ‖T ξ‖]
  have hn := opNorm_sq_le_of_pointwise_sq_le T hc (fun η => by
    have h := hgap η
    nlinarith)
  linarith

theorem projection_complement_norm_sq [CompleteSpace K]
    (P : K →L[ℂ] K) (hP : IsStarProjection P) (v : K) :
    ‖P v‖ ^ 2 + ‖v - P v‖ ^ 2 = ‖v‖ ^ 2 := by
  have hs : P.adjoint = P := hP.isSelfAdjoint.star_eq
  have hi : P (P v) = P v := congrArg (fun T : K →L[ℂ] K => T v) hP.isIdempotentElem.eq
  have ho : inner ℂ (P v) (v - P v) = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_right, hs, map_sub, hi, sub_self, inner_zero_right]
  have he : P v + (v - P v) = v := by abel
  have hn := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P v) (v - P v) ho
  rw [he] at hn
  simpa only [pow_two] using hn.symm

theorem norm_preserving_projection_no_coercive_complement
    [Nontrivial H] [CompleteSpace K]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : H →L[ℂ] K) (P : K →L[ℂ] K) (hP : IsStarProjection P)
    (A : K →L[ℂ] E) (hnorm : ‖P.comp T‖ = ‖T‖)
    {t : ℝ} (ht : 0 < t)
    (hlower : ∀ ξ, t * ‖ξ‖ ^ 2 ≤ ‖A (T ξ - P (T ξ))‖ ^ 2) : False := by
  let d : ℝ := max 1 ‖A‖
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hd2 : 0 < d ^ 2 := sq_pos_of_pos hd
  have hAd : ‖A‖ ≤ d := le_max_right _ _
  have hg : 0 < t / d ^ 2 := div_pos ht hd2
  apply not_uniform_positive_norm_gap (P.comp T) hg
  intro ξ
  have hb : ‖A (T ξ - P (T ξ))‖ ^ 2 ≤ d ^ 2 * ‖T ξ - P (T ξ)‖ ^ 2 := by
    have hn := (A.le_opNorm (T ξ - P (T ξ))).trans
      (mul_le_mul_of_nonneg_right hAd (norm_nonneg _))
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hsmall : (t / d ^ 2) * ‖ξ‖ ^ 2 ≤ ‖T ξ - P (T ξ)‖ ^ 2 := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hd2).mpr ((hlower ξ).trans (by simpa only [mul_comm] using hb))
  have hp := projection_complement_norm_sq P hP (T ξ)
  have hT : ‖T ξ‖ ^ 2 ≤ ‖T‖ ^ 2 * ‖ξ‖ ^ 2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm ξ) 2
  change ‖P (T ξ)‖ ^ 2 + _ ≤ _
  rw [hnorm]
  linarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionNormGap
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Localizing the Hilbert-space norm-gap argument to a projection range. -/

namespace KadisonKastler

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem projection_fixed_on_range (P : H →L[ℂ] H) (hP : IsStarProjection P)
    (x : P.range) : P (x : H) = x := by
  obtain ⟨y, hy⟩ := x.property
  rw [← hy]
  exact congrArg (fun T : H →L[ℂ] H => T y) hP.isIdempotentElem.eq

omit [CompleteSpace K] in
theorem norm_comp_projection_eq_norm_restrict
    (P : H →L[ℂ] H) (hP : IsStarProjection P) (S : H →L[ℂ] K) :
    ‖S.comp P‖ = ‖S.comp P.range.subtypeL‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound (S.comp P)
      (norm_nonneg (S.comp P.range.subtypeL))
    intro ξ
    let x : P.range := ⟨P ξ, ⟨ξ, rfl⟩⟩
    have hb := (S.comp P.range.subtypeL).le_opNorm x
    have hp : ‖P ξ‖ ≤ ‖ξ‖ := by
      simpa only [one_mul] using P.le_of_opNorm_le hP.norm_le ξ
    exact hb.trans (mul_le_mul_of_nonneg_left hp (norm_nonneg _))
  · apply ContinuousLinearMap.opNorm_le_bound (S.comp P.range.subtypeL)
      (norm_nonneg (S.comp P))
    intro ξ
    have hb := (S.comp P).le_opNorm (ξ : H)
    simpa only [ContinuousLinearMap.comp_apply, projection_fixed_on_range P hP,
      Submodule.subtypeL_apply, Submodule.norm_coe] using hb

theorem projection_norm_equality_no_spectral_gap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P : H →L[ℂ] H) (hP : IsStarProjection P) (hPn : P ≠ 0)
    (Q : K →L[ℂ] K) (hQ : IsStarProjection Q)
    (R : H →L[ℂ] K) (A : K →L[ℂ] E)
    (hnorm : ‖Q.comp (R.comp P)‖ = ‖R.comp P‖)
    {t : ℝ} (ht : 0 < t)
    (hlower : ∀ ξ, t * ‖P ξ‖ ^ 2 ≤ ‖A (R (P ξ) - Q (R (P ξ)))‖ ^ 2) : False := by
  have hex : ∃ ξ, P ξ ≠ 0 := by
    by_contra h
    apply hPn
    ext ξ
    simpa using not_exists.mp h ξ
  obtain ⟨ξ, hξ⟩ := hex
  let x : P.range := ⟨P ξ, ⟨ξ, rfl⟩⟩
  let : Nontrivial P.range := nontrivial_of_ne x 0 (fun he => hξ (congrArg Subtype.val he))
  have he : ‖Q.comp (R.comp P.range.subtypeL)‖ = ‖R.comp P.range.subtypeL‖ := by
    have h := norm_comp_projection_eq_norm_restrict P hP (Q.comp R)
    have hg := norm_comp_projection_eq_norm_restrict P hP R
    rw [ContinuousLinearMap.comp_assoc] at h
    exact h.symm.trans (hnorm.trans hg)
  apply norm_preserving_projection_no_coercive_complement
    (R.comp P.range.subtypeL) Q hQ A he ht
  intro η
  have h := hlower (η : H)
  simpa only [projection_fixed_on_range P hP, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, Submodule.norm_coe] using h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpectralCoefficientBound
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! Turning the positive spectral-cut inequality into a lower bound on
the actual represented vectors. -/

namespace KadisonKastler

noncomputable section

open scoped InnerProductSpace
open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

attribute [local instance] OAI.KadisonKastler.spectralCoefficientOrder
attribute [local instance] OAI.KadisonKastler.spectralCoefficientPreorder
attribute [local instance] OAI.KadisonKastler.spectralCoefficientLE
local instance spectralCoefficientStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

theorem projection_inner_eq_norm_sq (P : H →L[ℂ] H) (hP : IsStarProjection P) (ξ : H) :
    inner ℂ ξ (P ξ) = (‖P ξ‖ ^ 2 : ℝ) := by
  have hs : P.adjoint = P := hP.isSelfAdjoint.star_eq
  have hi : P (P ξ) = P ξ := congrArg (fun T : H →L[ℂ] H => T ξ) hP.isIdempotentElem.eq
  have he := P.adjoint_inner_right ξ (P ξ)
  rw [hs, hi, inner_self_eq_norm_sq_to_K] at he
  simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow] using he

theorem spectral_lower_bound_on_vectors (p : AlgebraProjection M) (b : Algebra M)
    {t : ℝ} (ht : t • p.val ≤ p.val * (star b * b) * p.val) (ξ : H) :
    t * ‖(p.val : H →L[ℂ] H) ξ‖ ^ 2 ≤
      ‖(b : H →L[ℂ] H) ((p.val : H →L[ℂ] H) ξ)‖ ^ 2 := by
  let P : H →L[ℂ] H := p.val
  let B : H →L[ℂ] H := b
  have hP : IsStarProjection P := p.property.map M.toStarSubalgebra.subtype
  have hs : P.adjoint = P := hP.isSelfAdjoint.star_eq
  have hp : 0 ≤ P * (star B * B) * P - t • P := by
    have h := map_nonneg M.toStarSubalgebra.subtype (sub_nonneg.mpr ht)
    exact h
  have htest := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hp).re_inner_nonneg_right ξ
  have hfirst : inner ℂ ξ ((P * (star B * B) * P) ξ) =
      (‖B (P ξ)‖ ^ 2 : ℝ) := by
    change inner ℂ ξ (P (B.adjoint (B (P ξ)))) = _
    calc
      _ = inner ℂ (P.adjoint ξ) (B.adjoint (B (P ξ))) :=
        (P.adjoint_inner_left _ _).symm
      _ = inner ℂ (P ξ) (B.adjoint (B (P ξ))) := by rw [hs]
      _ = inner ℂ (B (P ξ)) (B (P ξ)) := B.adjoint_inner_right _ _
      _ = _ := by
        simp only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
          Complex.ofReal_pow]
  have he : inner ℂ ξ ((P * (star B * B) * P - t • P) ξ) =
      (‖B (P ξ)‖ ^ 2 : ℝ) - (t : ℂ) * (‖P ξ‖ ^ 2 : ℝ) := by
    rw [sub_apply, inner_sub_right, hfirst]
    change _ - inner ℂ ξ ((t : ℂ) • P ξ) = _
    rw [inner_smul_right, projection_inner_eq_norm_sq P hP ξ]
  change 0 ≤ (inner ℂ ξ ((P * (star B * B) * P - t • P) ξ)).re at htest
  rw [he] at htest
  have hreal : 0 ≤ ‖B (P ξ)‖ ^ 2 - t * ‖P ξ‖ ^ 2 := by
    simpa only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero] using htest
  exact sub_nonneg.mp hreal

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FactorOffDiagonal
attribute [-instance] _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.Tracial.cyclicCoefficient_apply _root_.OAI.Generator.Tracial.cyclicPredualEvaluation_apply _root_.OAI.Generator.Tracial.traceFreeCopy_inner _root_.OAI.Generator.Tracial.traceFreeHilbertCoefficient_apply _root_.OAI.Generator.Tracial.traceFreeInclusion_inner _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! The spectral-cut step of Paulsen's localized row-averaging argument.
If every diagonal compression preserves the norm of a right factor, then
every off-diagonal coefficient vanishes and the factored map is right modular.
-/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H}

local instance offDiagonalOrder_rf7c5e8_1 : PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance offDiagonalPreorder_rf7c5e8_1 : Preorder (Algebra M) :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance offDiagonalLE_rf7c5e8_1 : LE (Algebra M) := (CStarAlgebra.spectralOrder _).toLE
local instance offDiagonalStarOrder_rf7c5e8_1 : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
omit [CompleteSpace H] in
theorem norm_preserved_by_larger_projection
    (P Q : K →L[ℂ] K) (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hPQ : P.comp Q = P) (T : H →L[ℂ] K)
    (hT : ‖P.comp T‖ = ‖T‖) : ‖Q.comp T‖ = ‖T‖ := by
  have hb (A : K →L[ℂ] K) (hA : IsStarProjection A) (B : H →L[ℂ] K) :
      ‖A.comp B‖ ≤ ‖B‖ :=
    (A.opNorm_comp_le B).trans ((mul_le_mul_of_nonneg_right hA.norm_le (norm_nonneg B)).trans_eq
      (one_mul _))
  apply le_antisymm (hb Q hQ T)
  calc
    ‖T‖ = ‖P.comp T‖ := hT.symm
    _ = ‖P.comp (Q.comp T)‖ := by rw [← ContinuousLinearMap.comp_assoc, hPQ]
    _ ≤ ‖Q.comp T‖ := hb P hP _

theorem factor_offDiagonal_eq_zero
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L R : H →L[ℂ] K)
    (F : Algebra M →L[ℂ] Algebra M)
    (hF : ∀ a, (F a : H →L[ℂ] H) = L.adjoint.comp ((π a).comp R))
    (hdiag : ∀ p : AlgebraProjection M,
      ‖(π p.val).comp (R.comp (p.val : H →L[ℂ] H))‖ =
        ‖R.comp (p.val : H →L[ℂ] H)‖)
    (e : AlgebraProjection M) (a : Algebra M) :
    F (a * (1 - e.val)) * e.val = 0 := by
  by_contra hn
  let b := F (a * (1 - e.val)) * e.val
  have hb : b * e.val = b := by
    dsimp [b]
    rw [mul_assoc, e.property.isIdempotentElem.eq]
  obtain ⟨p, t, hpe, hpn, ht, hbound⟩ := exists_corner_spectral_lower_bound e b hb hn
  let P : H →L[ℂ] H := p.val
  let Q : K →L[ℂ] K := π e.val
  have hP : IsStarProjection P := p.property.map M.toStarSubalgebra.subtype
  have hQ : IsStarProjection Q := e.property.map π
  have hPn : P ≠ 0 := by
    intro he
    exact hpn (Subtype.ext he)
  have hep : e.val * p.val = p.val := hpe
  have hnorm : ‖Q.comp (R.comp P)‖ = ‖R.comp P‖ := by
    apply norm_preserved_by_larger_projection (π p.val) Q (p.property.map π) hQ
      (T := R.comp P) (hT := hdiag p)
    change π p.val * π e.val = π p.val
    rw [← map_mul, projection_mul_of_le hpe]
  let A : K →L[ℂ] H := L.adjoint.comp (π a)
  apply projection_norm_equality_no_spectral_gap P hP hPn Q hQ R A hnorm ht
  intro ξ
  have heval : (b : H →L[ℂ] H) (P ξ) = A (R (P ξ) - Q (R (P ξ))) := by
    have hepξ : (e.val : H →L[ℂ] H) (P ξ) = P ξ :=
      congrArg (fun c : Algebra M => (c : H →L[ℂ] H) ξ) hep
    change (F (a * (1 - e.val)) : H →L[ℂ] H)
      ((e.val : H →L[ℂ] H) (P ξ)) = _
    rw [hepξ, hF, map_mul, map_sub, map_one]
    rfl
  have hl := spectral_lower_bound_on_vectors p b hbound ξ
  rw [heval] at hl
  exact hl

theorem right_module_of_no_offDiagonal (F : Algebra M →L[ℂ] Algebra M)
    (hF : ∀ (e : AlgebraProjection M) a, F (a * (1 - e.val)) * e.val = 0) :
    ∀ a b, F (a * b) = F a * b := by
  apply right_module_of_projection_tests M F
  intro e he a
  let p : AlgebraProjection M := ⟨e, he⟩
  let q : AlgebraProjection M := ⟨1 - e, he.one_sub⟩
  have hq := hF q a
  change F (a * (1 - (1 - e))) * (1 - e) = 0 at hq
  rw [sub_sub_cancel] at hq
  have hp := hF p a
  change F (a * (1 - e)) * e = 0 at hp
  have hqe : F (a * e) * e = F (a * e) := by
    rw [mul_sub, mul_one] at hq
    exact (sub_eq_zero.mp hq).symm
  have hs : F a = F (a * e) + F (a * (1 - e)) := by
    rw [← map_add, ← mul_add, add_sub_cancel, mul_one]
  rw [hs, add_mul, hqe, hp, add_zero]

theorem right_module_of_factor_diagonal_norm_oai
    (π : Algebra M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L R : H →L[ℂ] K)
    (F : Algebra M →L[ℂ] Algebra M)
    (hF : ∀ a, (F a : H →L[ℂ] H) = L.adjoint.comp ((π a).comp R))
    (hdiag : ∀ p : AlgebraProjection M,
      ‖(π p.val).comp (R.comp (p.val : H →L[ℂ] H))‖ =
        ‖R.comp (p.val : H →L[ℂ] H)‖) :
    ∀ a b, F (a * b) = F a * b :=
  right_module_of_no_offDiagonal F (factor_offDiagonal_eq_zero π L R F hF hdiag)

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.right_module_of_factor_diagonal_norm_oai.{u_1, u_2} := @OAI.KadisonKastler.right_module_of_factor_diagonal_norm_oai.{u_1, u_2}
