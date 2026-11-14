-- Prove2me | solution 1 for OAI.KadisonKastler.TypeIIIFactor.exists_matrixUnits_prescribed_projection_rank
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:54:11.147587+00:00
-- url     : https://prove2.me/submissions/0aaabe85-938e-4610-8296-81d915575419

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
import Definitions.Def_Q260K064
import Theorems.Thm_OAI_KadisonKastler_TypeIIIFactor_exists_isometry_onto_projection

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIIISpectralMatrix
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.MatrixUnitSystem.adaptedBasis_apply _root_.OAI.Generator.MatrixUnitSystem.initialColumn_apply _root_.OAI.Generator.orthonormalMatrixUnits_entry_apply _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.MatrixSiteWord.eval_append _root_.OAI.KadisonKastler.MatrixSiteWord.eval_cons _root_.OAI.KadisonKastler.MatrixSiteWord.eval_nil _root_.OAI.KadisonKastler.MatrixSiteWord.eval_reindex _root_.OAI.KadisonKastler.MatrixSiteWord.eval_star _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.conjugation_algebraVector _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.conjugatedMatrixUnits_entry _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrixPermutationValue_one _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.spatialMatrixUnits_entry _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite spectral partitions in a type III factor are matrix diagonals -/

namespace KadisonKastler

open Generator Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
  [Fintype ι] [DecidableEq ι] {M : VonNeumannAlgebra H}

/-- Nonzero orthogonal spectral pieces summing to one are the diagonal of
an actual full matrix system in the original type III factor. -/
theorem TypeIIIFactor.exists_matrixUnits_of_partition (hM : TypeIIIFactor M)
    (q : ι → AlgebraProjection M) (hne : ∀ i, (q i).val ≠ 0)
    (horth : ∀ i j, i ≠ j → (q i).val * (q j).val = 0)
    (htotal : ∑ i, (q i).val = 1) :
    ∃ E : MatrixUnitSystem ι (Algebra M), ∀ i, E.entry i i = (q i).val := by
  choose v hv hq using fun i => hM.exists_isometry_onto_projection
    (q i).val (q i).property (hne i)
  have hright (i : ι) : (q i).val * v i = v i := by
    rw [← hq i, mul_assoc, hv i, mul_one]
  have hleft (i : ι) : star (v i) * (q i).val = star (v i) := by
    have h := congrArg star (hright i)
    simpa only [star_mul, (q i).property.isSelfAdjoint.star_eq] using h
  have hcross (i j : ι) : star (v i) * v j = if i = j then 1 else 0 := by
    split_ifs with hij
    · subst j
      exact hv i
    · calc
        star (v i) * v j = (star (v i) * (q i).val) * ((q j).val * v j) := by
          rw [hleft, hright]
        _ = star (v i) * ((q i).val * (q j).val) * v j := by simp only [mul_assoc]
        _ = 0 := by rw [horth i j hij, mul_zero, zero_mul]
  let E : MatrixUnitSystem ι (Algebra M) := {
    entry := fun i j => v i * star (v j)
    star_entry := by intro i j; simp only [star_mul, star_star]
    mul_entry := by
      intro i j k l
      rw [show (v i * star (v j)) * (v k * star (v l)) =
        v i * (star (v j) * v k) * star (v l) by simp only [mul_assoc], hcross]
      split_ifs <;> simp
    total := by simpa only [hq] using htotal }
  exact ⟨E, hq⟩



end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIIIPrescribedRank
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Prescribed finite matrix ranks for type III projections

Every nonzero projection splits into any positive finite number of
nonzero pieces. Consequently a nontrivial projection can occupy either
chosen positive block size in a unital full matrix algebra.
-/

namespace KadisonKastler

open Generator Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem TypeIIIFactor.exists_proper_subprojection (hM : TypeIIIFactor M)
    (p : AlgebraProjection M) (hp : p.val ≠ 0) :
    ∃ q : AlgebraProjection M, q ≤ p ∧ q.val ≠ 0 ∧ q.val ≠ p.val := by
  have hn : ¬ FiniteProjectionIn M p.val := fun h => hp (hM.purelyInfinite p.val p.property h)
  simp only [FiniteProjectionIn] at hn
  push Not at hn
  obtain ⟨v,hv,hpv,hproper⟩ := hn
  let w : PartialIsometry M := ⟨p,v,hv⟩
  refine ⟨w.target,?_,?_,hproper⟩
  · change p.val * (v * star v) = v * star v
    rw [← mul_assoc,hpv]
  · intro hz
    have hv0 : v = 0 := by
      have he := w.target_mul
      change (v * star v) * v = v at he
      rw [show v * star v = 0 from hz,zero_mul] at he
      exact he.symm
    apply hp
    rw [← hv,hv0,star_zero,zero_mul]

theorem TypeIIIFactor.exists_nonzero_fin_partition (hM : TypeIIIFactor M)
    (p : AlgebraProjection M) (hp : p.val ≠ 0) (n : ℕ) :
    ∃ q : Fin (n+1) → AlgebraProjection M,
      (∀ i, (q i).val ≠ 0) ∧
      (∀ i j, i ≠ j → (q i).val * (q j).val = 0) ∧
      (∑ i, (q i).val) = p.val ∧ (∀ i, q i ≤ p) := by
  induction n generalizing p with
  | zero =>
    refine ⟨fun _ => p,fun _ => hp,?_,?_,fun _ => le_rfl⟩
    · intro i j hij
      exact (hij (Fin.ext (by omega))).elim
    · simp
  | succ n ih =>
    obtain ⟨q,hqp,hq0,hqpne⟩ := hM.exists_proper_subprojection p hp
    let r : AlgebraProjection M := ⟨p.val-q.val,q.property.sub_of_mul_eq_right p.property hqp⟩
    have hr0 : r.val ≠ 0 := fun h => hqpne (sub_eq_zero.mp h).symm
    have hrp : r ≤ p := by
      change p.val * (p.val-q.val) = p.val-q.val
      rw [mul_sub,p.property.isIdempotentElem.eq,hqp]
    have hqr : q.val*r.val = 0 := by
      change q.val * (p.val-q.val) = 0
      rw [mul_sub,projection_mul_of_le hqp,q.property.isIdempotentElem.eq,sub_self]
    obtain ⟨f,hf0,hforth,hft,hfr⟩ := ih r hr0
    refine ⟨Fin.cons q f,?_,?_,?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hq0
      · exact hf0 j
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j => exact orthogonal_subprojections hqr le_rfl (hfr j)
      | succ i =>
        cases j using Fin.cases with
        | zero =>
          exact PartialIsometry.orthogonal_reverse _ _
            (orthogonal_subprojections hqr le_rfl (hfr i))
        | succ j => exact hforth i j (fun he => hij (congrArg Fin.succ he))
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero,Fin.cons_succ]
      rw [hft]
      change q.val + (p.val-q.val) = p.val
      abel
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hqp
      · exact (hfr j).trans hrp

theorem TypeIIIFactor.exists_matrixUnits_prescribed_projection_rank_oai
    [TopologicalSpace.SeparableSpace H] (hM : TypeIIIFactor M)
    (p : AlgebraProjection M) (hp0 : p.val ≠ 0) (hp1 : p.val ≠ 1)
    (r s : ℕ) :
    ∃ E : MatrixUnitSystem (Fin (r+1) ⊕ Fin (s+1)) (Algebra M),
      (∑ i, E.entry (Sum.inl i) (Sum.inl i)) = p.val := by
  let q : AlgebraProjection M := ⟨1-p.val,p.property.one_sub⟩
  have hq0 : q.val ≠ 0 := fun h => hp1 (sub_eq_zero.mp h).symm
  obtain ⟨a,ha0,haorth,hat,hap⟩ := hM.exists_nonzero_fin_partition p hp0 r
  obtain ⟨b,hb0,hborth,hbt,hbq⟩ := hM.exists_nonzero_fin_partition q hq0 s
  let f : Fin (r+1) ⊕ Fin (s+1) → AlgebraProjection M := Sum.elim a b
  have hpq : p.val * q.val = 0 := p.property.mul_one_sub_self
  have horth : ∀ i j, i ≠ j → (f i).val * (f j).val = 0 := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact haorth i j (fun he => hij (congrArg Sum.inl he))
      | inr j => exact orthogonal_subprojections hpq (hap i) (hbq j)
    | inr i =>
      cases j with
      | inl j =>
        exact PartialIsometry.orthogonal_reverse _ _
          (orthogonal_subprojections hpq (hap j) (hbq i))
      | inr j => exact hborth i j (fun he => hij (congrArg Sum.inr he))
  have htotal : (∑ i, (f i).val) = 1 := by
    rw [Fintype.sum_sum_type]
    change (∑ i, (a i).val) + (∑ i, (b i).val) = 1
    rw [hat,hbt]
    change p.val+(1-p.val) = 1
    abel
  obtain ⟨E,hE⟩ := hM.exists_matrixUnits_of_partition f
    (fun i => by cases i with | inl i => exact ha0 i | inr i => exact hb0 i)
    horth htotal
  exact ⟨E,(Finset.sum_congr rfl (fun i _ => hE (Sum.inl i))).trans hat⟩

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.TypeIIIFactor.exists_matrixUnits_prescribed_projection_rank_oai.{u_1} := @OAI.KadisonKastler.TypeIIIFactor.exists_matrixUnits_prescribed_projection_rank_oai.{u_1}
