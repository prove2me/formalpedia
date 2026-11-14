-- Prove2me | solution 1 for OAI.KadisonKastler.publishedSimpleDerivationInner
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:16:50.43981+00:00
-- url     : https://prove2.me/submissions/5d1b409d-5ebd-4c27-896c-3513a5b00f87

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.Module
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
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
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
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fin.Tuple.Basic
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
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Pairwise.Chain
import Mathlib.Data.Sym.Card
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Nat
import Mathlib.Logic.Equiv.Option
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Sum
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
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Filter.AtTopBot.Finset
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
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.Star
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
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
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K029
import Theorems.Thm_OAI_KadisonKastler_exists_selfAdjoint_split_of_factor_commutant
import Theorems.Thm_OAI_KadisonKastler_exists_signed_cyclic_functional
import Theorems.Thm_OAI_KadisonKastler_exists_simple_spatial_derivation
import Theorems.Thm_OAI_KadisonKastler_extension_implementer_mem_of_spatial_split
import Theorems.Thm_OAI_KadisonKastler_factor_of_extreme_signed_derivation_extension

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CountableProjectionFamilies
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.Generator.Tracial.CornerPartition.single_pinch _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_projectionFamilyCommutationSpace _root_.OAI.KadisonKastler.mem_projectionFamilyRemainderSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Countable projection families from separating vectors

The spatial derivation argument needs countable decomposability of the
algebra, rather than separability of the ambient Hilbert space. A
countable family of separating vectors supplies exactly this property.
-/

namespace KadisonKastler

noncomputable section

open Generator.Tracial
open scoped BigOperators

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem projection_norm_apply_sq (p : AlgebraProjection M) (ξ : H) :
    ‖p.val.val ξ‖ ^ 2 = (inner ℂ (p.val.val ξ) ξ).re := by
  have hp : IsStarProjection p.val.val := p.property.map M.toStarSubalgebra.subtype
  have h := ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_left p.val.val ξ
  change ‖p.val.val ξ‖ ^ 2 = (inner ℂ ((star p.val.val * p.val.val) ξ) ξ).re at h
  simpa only [hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq] using h

theorem countable_projection_vector_support {ι : Type*}
    (p : ι → AlgebraProjection M)
    (ho : Pairwise (fun i j => (p i).val * (p j).val = 0)) (ξ : H) :
    {i | (p i).val.val ξ ≠ 0}.Countable := by
  classical
  have hsum (s : Finset ι) : ∑ i ∈ s, ‖(p i).val.val ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by
    let q := AlgebraProjection.finsetSum p s (fun _ _ _ _ hij => ho hij)
    have hqsum : q.val.val ξ = ∑ i ∈ s, (p i).val.val ξ := by
      change (M.toStarSubalgebra.subtype (∑ i ∈ s, (p i).val)) ξ = _
      rw [map_sum]
      simp only [sum_apply]
      rfl
    have he : ∑ i ∈ s, ‖(p i).val.val ξ‖ ^ 2 = ‖q.val.val ξ‖ ^ 2 := by
      calc
        _ = ∑ i ∈ s, (inner ℂ ((p i).val.val ξ) ξ).re := by
          simp only [projection_norm_apply_sq]
        _ = (inner ℂ (∑ i ∈ s, (p i).val.val ξ) ξ).re := by
          simp only [sum_inner, Complex.re_sum]
        _ = (inner ℂ (q.val.val ξ) ξ).re := by rw [hqsum]
        _ = ‖q.val.val ξ‖ ^ 2 := (projection_norm_apply_sq q ξ).symm
    have hqn : ‖q.val.val ξ‖ ≤ ‖ξ‖ := by
      calc
        ‖q.val.val ξ‖ ≤ ‖q.val.val‖ * ‖ξ‖ := q.val.val.le_opNorm ξ
        _ ≤ 1 * ‖ξ‖ := mul_le_mul_of_nonneg_right
          (IsStarProjection.norm_le _ (q.property.map M.toStarSubalgebra.subtype)) (norm_nonneg ξ)
        _ = ‖ξ‖ := one_mul _
    rw [he]
    exact pow_le_pow_left₀ (norm_nonneg _) hqn 2
  have hs : Summable (fun i => ‖(p i).val.val ξ‖ ^ 2) :=
    summable_of_sum_le (fun _ => sq_nonneg _) hsum
  have he : Function.support (fun i => ‖(p i).val.val ξ‖ ^ 2) =
      {i | (p i).val.val ξ ≠ 0} := by
    ext i
    simp [Function.support]
  rw [← he]
  exact hs.countable_support

theorem countableProjectionFamilies_of_separating_vectors
    (ξ : ℕ → H)
    (hξ : ∀ a : Algebra M, (∀ n, a.val (ξ n) = 0) → a = 0) :
    HasCountableProjectionFamilies M := by
  intro ι p hp ho
  have hcover : (Set.univ : Set ι) ⊆ ⋃ n, {i | (p i).val.val (ξ n) ≠ 0} := by
    intro i _
    have hn : ∃ n, (p i).val.val (ξ n) ≠ 0 := by
      by_contra h
      push Not at h
      exact hp i (hξ (p i).val h)
    obtain ⟨n, hn⟩ := hn
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  exact Set.countable_univ_iff.mp
    ((Set.countable_iUnion (fun n => countable_projection_vector_support p ho (ξ n))).mono hcover)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.TracialSplitting_FullProjections
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uA uD

open Filter Topology

namespace CurrentMain

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

section SmallFullSupport

variable {A : Type uA} {D : Type uD} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
lemma simple_starAlgHom_injective [Nontrivial D] (hsimple : TopologicallySimple A)
    (ι : A →⋆ₐ[ℂ] D) : Function.Injective ι := by
  have hι : Continuous ι := (ι.toLinearMap.mkContinuous 1 (fun a => by
    change ‖ι a‖ ≤ 1 * ‖a‖
    simpa only [one_mul] using (NonUnitalStarAlgHom.norm_apply_le ι a))).continuous
  have hc : IsClosed (TwoSidedIdeal.ker ι : Set A) := by
    have he : (TwoSidedIdeal.ker ι : Set A) = {a : A | ι a = 0} := by
      ext a; exact TwoSidedIdeal.mem_ker ι
    rw [he]
    exact isClosed_eq hι continuous_const
  rcases hsimple (TwoSidedIdeal.ker ι) hc with hb | ht
  · exact (TwoSidedIdeal.ker_eq_bot ι).mp hb
  · have : (1 : A) ∈ TwoSidedIdeal.ker ι := by rw [ht]; exact Set.mem_univ _
    have hz := (TwoSidedIdeal.mem_ker ι).mp this
    simp at hz

end SmallFullSupport

end CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MaximalClosedStarIdeal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.NonsingularAction.operatorAction_constant _root_.OAI.KadisonKastler.NonsingularAction.operatorEquiv_apply _root_.OAI.KadisonKastler.NonsingularAction.restrictedOperatorAction_coe _root_.OAI.KadisonKastler.ScalarBoundaryMean.operatorMean_apply _root_.OAI.KadisonKastler.WeakOperatorField.pullback_constant _root_.OAI.KadisonKastler.WeakOperatorField.pullback_id _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.operatorFieldFamilyInclusion_apply _root_.OAI.KadisonKastler.tracialQuotientLinear_map _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A maximal proper closed star ideal in a unital C-star algebra

This supplies the quotient step in the unital specialization of Sakai's
ideal-extension argument. The closure of a proper ideal remains proper:
otherwise the original ideal meets the open set of invertible elements.
-/

namespace KadisonKastler

noncomputable section

open Filter Topology CuntzPureness

variable {B : Type*} [CStarAlgebra B]

theorem twoSidedIdeal_eq_top_of_isUnit_mem (I : TwoSidedIdeal B)
    {x : B} (hx : x ∈ I) (hu : IsUnit x) : I = ⊤ := by
  obtain ⟨u, rfl⟩ := hu
  apply I.eq_top
  simpa using I.mul_mem_left (↑(u⁻¹) : B) (u : B) hx

theorem closedTwoSidedIdeal_ne_top {I : TwoSidedIdeal B} (hI : I ≠ ⊤) :
    Pureness.closedTwoSidedIdeal I ≠ ⊤ := by
  intro h
  have h1 : (1 : B) ∈ closure (I : Set B) := by
    rw [← Pureness.coe_closedTwoSidedIdeal]
    change (1 : B) ∈ Pureness.closedTwoSidedIdeal I
    rw [h]
    exact TwoSidedIdeal.mem_top B
  obtain ⟨x, hxunit, hx⟩ := mem_closure_iff_nhds.mp h1 _
    (Units.isOpen.mem_nhds isUnit_one)
  exact hI (twoSidedIdeal_eq_top_of_isUnit_mem I hx hxunit)

theorem mem_idealChainUnion (c : Set (TwoSidedIdeal B))
    (hc : IsChain (· ≤ ·) c) (hne : c.Nonempty) (x : B) :
    x ∈ idealChainUnion c hc hne ↔ ∃ I ∈ c, x ∈ I := by
  simp only [idealChainUnion, TwoSidedIdeal.mem_mk', Set.mem_ofPred_eq]

theorem closedTwoSidedIdeal_star {I : TwoSidedIdeal B}
    (hstar : ∀ {x : B}, x ∈ I → star x ∈ I) {x : B}
    (hx : x ∈ Pureness.closedTwoSidedIdeal I) :
    star x ∈ Pureness.closedTwoSidedIdeal I := by
  rw [← SetLike.mem_coe, Pureness.coe_closedTwoSidedIdeal] at hx ⊢
  obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.mp hx
  exact isClosed_closure.mem_of_tendsto hux.star
    (Eventually.of_forall fun n => subset_closure (hstar (hu n)))

theorem exists_maximal_proper_closedStarIdeal [Nontrivial B] :
    ∃ J : ClosedStarIdeal B, J.ideal ≠ ⊤ ∧
      ∀ K : ClosedStarIdeal B, K.ideal ≠ ⊤ → J.ideal ≤ K.ideal → K.ideal = J.ideal := by
  let S : Set (TwoSidedIdeal B) :=
    {I | IsClosed (I : Set B) ∧ (∀ {x : B}, x ∈ I → star x ∈ I) ∧ I ≠ ⊤}
  have hchain : ∀ c ⊆ S, IsChain (· ≤ ·) c →
      ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
    intro c hcs hc
    rcases c.eq_empty_or_nonempty with rfl | hne
    · refine ⟨⊥, ?_, by simp⟩
      refine ⟨?_, ?_, bot_ne_top⟩
      · simpa only [TwoSidedIdeal.coe_bot] using (isClosed_singleton : IsClosed ({0} : Set B))
      · intro x hx
        rw [TwoSidedIdeal.mem_bot] at hx ⊢
        rw [hx, star_zero]
    · let I := idealChainUnion c hc hne
      have hproper : I ≠ ⊤ := by
        intro h
        have hone : (1 : B) ∈ I := by rw [h]; exact TwoSidedIdeal.mem_top B
        obtain ⟨K, hK, h1⟩ := (mem_idealChainUnion c hc hne 1).mp hone
        exact (hcs hK).2.2 (K.eq_top h1)
      have hstar : ∀ {x : B}, x ∈ I → star x ∈ I := by
        intro x hx
        obtain ⟨K, hK, hxK⟩ := (mem_idealChainUnion c hc hne x).mp hx
        exact (mem_idealChainUnion c hc hne (star x)).mpr ⟨K, hK, (hcs hK).2.1 hxK⟩
      refine ⟨Pureness.closedTwoSidedIdeal I,
        ⟨?_, closedTwoSidedIdeal_star hstar, closedTwoSidedIdeal_ne_top hproper⟩, ?_⟩
      · simpa only [Pureness.coe_closedTwoSidedIdeal] using
          (isClosed_closure : IsClosed (closure (I : Set B)))
      · intro K hK x hx
        rw [← SetLike.mem_coe, Pureness.coe_closedTwoSidedIdeal]
        exact subset_closure ((mem_idealChainUnion c hc hne x).mpr ⟨K, hK, hx⟩)
  obtain ⟨J, hJ, hmax⟩ := zorn_le₀ S hchain
  refine ⟨⟨J, hJ.2.1, hJ.1⟩, hJ.2.2, ?_⟩
  intro K hK hJK
  exact le_antisymm (hmax ⟨K.isClosed, K.star_mem, hK⟩ hJK) hJK

local instance maximalClosedStarIdealInstance1_r0b686c_1 : PartialOrder B := CStarAlgebra.spectralOrder B
local instance maximalClosedStarIdealInstance2_r0b686c_1 : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
/-- Every unital representation of the maximal quotient is faithful. The
preimage of its kernel is a closed star ideal, so maximality applies directly. -/
theorem maximal_closedStarIdeal_quotient_injective
    (J : ClosedStarIdeal B)
    (hmax : ∀ K : ClosedStarIdeal B, K.ideal ≠ ⊤ →
      J.ideal ≤ K.ideal → K.ideal = J.ideal)
    {C : Type*} [CStarAlgebra C] [Nontrivial C]
    (ψ : J.Quotient →⋆ₐ[ℂ] C) : Function.Injective ψ := by
  let θ : B →⋆ₐ[ℂ] C := ψ.comp J.quotientStarHom
  let K : ClosedStarIdeal B := {
    ideal := TwoSidedIdeal.ker θ
    star_mem := by
      intro x hx
      apply (TwoSidedIdeal.mem_ker θ).mpr
      rw [map_star, (TwoSidedIdeal.mem_ker θ).mp hx, star_zero]
    isClosed := by
      have hc : Continuous θ :=
        (θ.toLinearMap.mkContinuous 1 (fun x => by
          change ‖θ x‖ ≤ 1 * ‖x‖
          simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le θ x)).continuous
      have he : (TwoSidedIdeal.ker θ : Set B) = {x | θ x = 0} := by
        ext x
        exact TwoSidedIdeal.mem_ker θ
      rw [he]
      exact isClosed_eq hc continuous_const }
  have hK : K.ideal ≠ ⊤ := by
    intro h
    have h1 : (1 : B) ∈ K.ideal := by rw [h]; exact TwoSidedIdeal.mem_top B
    have hzero := (TwoSidedIdeal.mem_ker θ).mp h1
    exact _root_.one_ne_zero (by simpa only [map_one] using hzero)
  have hJK : J.ideal ≤ K.ideal := by
    intro x hx
    apply (TwoSidedIdeal.mem_ker θ).mpr
    change ψ (J.quotientStarHom x) = 0
    have hzero : J.quotientStarHom x = 0 := Quotient.sound hx
    rw [hzero, map_zero]
  have heq := hmax K hK hJK
  intro x y hxy
  obtain ⟨a, rfl⟩ := J.quotientMap_surjective x
  obtain ⟨b, rfl⟩ := J.quotientMap_surjective y
  change ψ (J.quotientStarHom a) = ψ (J.quotientStarHom b) at hxy
  have hab : a - b ∈ K.ideal := by
    apply (TwoSidedIdeal.mem_ker θ).mpr
    change ψ (J.quotientStarHom (a - b)) = 0
    simpa only [map_sub, sub_eq_zero] using hxy
  rw [heq] at hab
  have hzero : J.quotientStarHom (a - b) = 0 := Quotient.sound hab
  change J.quotientStarHom a = J.quotientStarHom b
  exact sub_eq_zero.mp (by simpa only [map_sub] using hzero)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SimpleAlgebraIdealSeparation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Separating a simple unital algebra from ideals in an extension

These are the norm-separation steps used in the maximal-ideal construction
in Sakai, *Derivations of simple C*-algebras II*, p.260. A proper closed
star ideal in a unital extension has an isometric quotient map on the
simple unital subalgebra. In particular it cannot approach a nonzero
element of that subalgebra more closely than its norm.
-/

namespace KadisonKastler

noncomputable section

open CuntzPureness

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem closedStarIdeal_quotient_nontrivial (J : ClosedStarIdeal B)
    (hJ : J.ideal ≠ ⊤) : Nontrivial J.Quotient := by
  apply (RingCon.nontrivial_quotient (c := J.ideal.ringCon)).mpr
  intro h
  apply hJ
  apply TwoSidedIdeal.ringCon_injective
  simpa only [TwoSidedIdeal.top_ringCon] using h

theorem simple_quotient_composition_injective (hA : CStarSimple A)
    (φ : A →⋆ₐ[ℂ] B) (J : ClosedStarIdeal B) (hJ : J.ideal ≠ ⊤) :
    Function.Injective (J.quotientStarHom.comp φ) := by
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  let : Nontrivial J.Quotient := closedStarIdeal_quotient_nontrivial J hJ
  exact CurrentMain.simple_starAlgHom_injective hA (J.quotientStarHom.comp φ)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DerivationStarReduction
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Reduction to anti-star derivations

Sakai's spatial construction treats derivations satisfying
`D (star x) = -star (D x)`. Every bounded complex derivation is a complex
linear combination of two such derivations. That decomposition transfers innerness from anti-star derivations
to arbitrary bounded complex derivations.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

theorem starConjugateMap_leibniz (D : A →L[ℂ] A)
    (hD : ∀ x y, D (x * y) = D x * y + x * D y) :
    ∀ x y, starConjugateMap D (x * y) =
      starConjugateMap D x * y + x * starConjugateMap D y := by
  intro x y
  simp only [starConjugateMap_apply, star_mul, hD, star_add, star_star]
  exact add_comm _ _

private theorem leibniz_combination (D E : A →L[ℂ] A)
    (hD : ∀ x y, D (x * y) = D x * y + x * D y)
    (hE : ∀ x y, E (x * y) = E x * y + x * E y) (c d : ℂ) :
    ∀ x y, (c • D + d • E) (x * y) =
      (c • D + d • E) x * y + x * (c • D + d • E) y := by
  intro x y
  simp only [add_apply, smul_apply,
    hD, hE, smul_add, add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  abel

theorem exists_antiStar_derivation_decomposition (D : A →L[ℂ] A)
    (hD : ∀ x y, D (x * y) = D x * y + x * D y) :
    ∃ F G : A →L[ℂ] A,
      (∀ x y, F (x * y) = F x * y + x * F y) ∧
      (∀ x, F (star x) = -star (F x)) ∧
      (∀ x y, G (x * y) = G x * y + x * G y) ∧
      (∀ x, G (star x) = -star (G x)) ∧
      ∀ x, D x = F x + Complex.I • G x := by
  let E := starConjugateMap D
  let F : A →L[ℂ] A := (1 / 2 : ℂ) • D + (-1 / 2 : ℂ) • E
  let G : A →L[ℂ] A := (-Complex.I / 2 : ℂ) • D + (-Complex.I / 2 : ℂ) • E
  have hE := starConjugateMap_leibniz D hD
  refine ⟨F, G, leibniz_combination D E hD hE _ _, ?_,
    leibniz_combination D E hD hE _ _, ?_, ?_⟩
  · intro x
    simp [F, E, star_smul, star_add, star_star]
    module
  · intro x
    simp [G, E, star_smul, star_add, star_star]
    module
  · intro x
    simp only [F, G, add_apply, smul_apply,
      smul_add, smul_smul]
    have hi : Complex.I * (-Complex.I / 2) = (1 / 2 : ℂ) := by
      calc
        Complex.I * (-Complex.I / 2) = -(Complex.I ^ 2) / 2 := by ring
        _ = 1 / 2 := by rw [Complex.I_sq]; norm_num
    simp only [hi]
    module

theorem inner_derivation_of_antiStar_inner
    (hInner : ∀ F : A →L[ℂ] A,
      (∀ x y, F (x * y) = F x * y + x * F y) →
      (∀ x, F (star x) = -star (F x)) →
      ∃ a : A, ∀ x, F x = a * x - x * a)
    (D : A →L[ℂ] A) (hD : ∀ x y, D (x * y) = D x * y + x * D y) :
    ∃ a : A, ∀ x, D x = a * x - x * a := by
  obtain ⟨F, G, hF, hFs, hG, hGs, hsum⟩ := exists_antiStar_derivation_decomposition D hD
  obtain ⟨a, ha⟩ := hInner F hF hFs
  obtain ⟨b, hb⟩ := hInner G hG hGs
  refine ⟨a + Complex.I • b, fun x => ?_⟩
  rw [hsum, ha, hb]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_sub]
  abel

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialDerivationClosure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spatial derivations pass to the bicommutant

Kaplansky's constructed bounded net transfers commutator membership to
the represented closure. Central projections in that closure therefore
commute with the spatial implementer.
-/

namespace KadisonKastler

noncomputable section

open Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem spatial_commutator_mem_generated_contraction
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hS : ∀ a : S, T * a.val - a.val * T ∈ generatedVonNeumannAlgebra S)
    (b : H →L[ℂ] H) (hb : b ∈ generatedVonNeumannAlgebra S) (hbn : ‖b‖ ≤ 1) :
    T * b - b * T ∈ generatedVonNeumannAlgebra S := by
  classical
  have hb' : b ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
    rwa [← generatedVonNeumannAlgebra_coe]
  obtain ⟨a, _, ht⟩ := publishedKaplanskyDensity.exists_strong_contraction_net S b hb' hbn
  let c (d : Finset H × ℕ) : Algebra (generatedVonNeumannAlgebra S) :=
    ⟨T * (a d).val - (a d).val * T, hS (a d)⟩
  apply Generator.Tracial.weak_operator_limit_mem (ι := Finset H × ℕ) (l := atTop)
    (generatedVonNeumannAlgebra S) c
    (T * b - b * T)
  intro ξ η
  have hlim : Tendsto (fun d => T ((a d).val ξ) - (a d).val (T ξ)) atTop
      (𝓝 (T (b ξ) - b (T ξ))) :=
    (T.continuous.tendsto _ |>.comp (ht ξ)).sub (ht (T ξ))
  exact (tendsto_const_nhds : Tendsto (fun _ : Finset H × ℕ => η) atTop (𝓝 η)).inner
    (𝕜 := ℂ) hlim

theorem spatial_commutator_mem_generated
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hS : ∀ a : S, T * a.val - a.val * T ∈ generatedVonNeumannAlgebra S)
    (b : H →L[ℂ] H) (hb : b ∈ generatedVonNeumannAlgebra S) :
    T * b - b * T ∈ generatedVonNeumannAlgebra S := by
  let c : ℝ := ‖b‖ + 1
  have hc : 0 < c := by dsimp [c] <;> positivity
  let V := (generatedVonNeumannAlgebra S).toStarSubalgebra.toSubalgebra.toSubmodule.restrictScalars ℝ
  have hb' : (c⁻¹ : ℝ) • b ∈ generatedVonNeumannAlgebra S := V.smul_mem c⁻¹ hb
  have hn : ‖(c⁻¹ : ℝ) • b‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le), ← div_eq_inv_mul]
    exact (div_le_one hc).mpr (by dsimp [c] <;> linarith)
  have h := spatial_commutator_mem_generated_contraction S T hS _ hb' hn
  have he : T * (c⁻¹ • b) - (c⁻¹ • b) * T = c⁻¹ • (T * b - b * T) := by
    rw [mul_smul_comm, smul_mul_assoc, smul_sub]
  rw [he] at h
  exact (V.smul_mem_iff (inv_ne_zero hc.ne')).mp h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DerivationExtensionFactor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Factoriality in Sakai's one-implementer extension

In an irreducible representation of the algebra generated by the source
and its self-adjoint spatial implementer, every central projection of the
source bicommutant commutes with all generators. It is therefore trivial.
-/

namespace KadisonKastler

noncomputable section

variable {A B H : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.derivationExtensionFactorInstance1
local instance derivationExtensionFactorInstance2 : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B

theorem commutes_of_normGeneratedExtension
    (φ : A →⋆ₐ[ℂ] B) (d : B) (hgen : NormGeneratedExtension φ d)
    (ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (p : H →L[ℂ] H)
    (hp : IsSelfAdjoint p)
    (hA : ∀ a, Commute p (ρ (φ a))) (hd : Commute p (ρ d)) :
    ∀ b, Commute p (ρ b) := by
  let C := (StarSubalgebra.centralizer ℂ ({p} : Set (H →L[ℂ] H))).comap ρ
  have hmem (b : B) : b ∈ C ↔ Commute p (ρ b) := by
    change ρ b ∈ StarSubalgebra.centralizer ℂ ({p} : Set (H →L[ℂ] H)) ↔ _
    simp only [StarSubalgebra.mem_centralizer_iff, Set.mem_singleton_iff,
      forall_eq, hp.star_eq]
    exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩
  have hclosed : IsClosed (C : Set B) := by
    have he : (C : Set B) = {b | p * ρ b = ρ b * p} := by
      ext b
      exact (hmem b).trans Iff.rfl
    rw [he]
    exact isClosed_eq (continuous_const.mul (show Continuous ρ by fun_prop))
      ((show Continuous ρ by fun_prop).mul continuous_const)
  have htop := hgen C hclosed (fun a => (hmem _).mpr (hA a)) ((hmem _).mpr hd)
  intro b
  apply (hmem b).mp
  rw [htop]
  trivial

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DerivationCyclicPowers
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Countable cyclic multiplicity of a one-implementer extension

If a cyclic representation is generated by a source algebra and a
self-adjoint derivation implementer, powers of that implementer applied
to the cyclic vector generate the representation as a source module.
Consequently the source commutant has countable projection families.
-/

namespace KadisonKastler

noncomputable section

variable {A B H : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem denseRange_derivation_power_span
    (φ : A →⋆ₐ[ℂ] B) (d : B) (hdsa : IsSelfAdjoint d)
    (hgen : NormGeneratedExtension φ d)
    (D : A →L[ℂ] A) (hd : ∀ a, φ (D a) = d * φ a - φ a * d)
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcyc : DenseRange (fun b => π b ξ)) :
    DenseRange (Finsupp.linearCombination ℂ
      (fun i : A × ℕ => π (φ i.1) ((π d ^ i.2) ξ))) := by
  let v : A × ℕ → H := fun i => π (φ i.1) ((π d ^ i.2) ξ)
  let W := LinearMap.range (Finsupp.linearCombination ℂ v)
  let V := W.topologicalClosure
  have hv (a : A) (n : ℕ) : v (a, n) ∈ W := by
    change v (a, n) ∈ LinearMap.range (Finsupp.linearCombination ℂ v)
    rw [Finsupp.range_linearCombination]
    exact Submodule.subset_span ⟨(a, n), rfl⟩
  have hA (a : A) (i : A × ℕ) : π (φ a) (v i) ∈ W := by
    have he : π (φ a) (v i) = v (a * i.1, i.2) := by
      simp only [v, map_mul, mul_apply_eq_comp]
    rw [he]
    exact hv _ _
  have hT (i : A × ℕ) : π d (v i) ∈ W := by
    have hcomm : π d * π (φ i.1) = π (φ (D i.1)) + π (φ i.1) * π d := by
      have hh := congrArg π (hd i.1)
      simp only [map_sub, map_mul] at hh
      exact (eq_sub_iff_add_eq.mp hh).symm
    have he : π d (v i) = v (D i.1, i.2) + v (i.1, i.2 + 1) := by
      change (π d * π (φ i.1)) ((π d ^ i.2) ξ) = _
      rw [hcomm]
      simp only [v, add_apply, mul_apply_eq_comp,
        pow_succ', mul_apply_eq_comp]
    rw [he]
    exact W.add_mem (hv _ _) (hv _ _)
  have hQA (a : A) : V.starProjection * π (φ a) = π (φ a) * V.starProjection := by
    apply Generator.starProjection_commutes_of_invariant
    · exact invariant_closed_linearCombination_range v _ (hA a)
    · rw [← map_star, ← map_star]
      exact invariant_closed_linearCombination_range v _ (hA (star a))
  have hQT : V.starProjection * π d = π d * V.starProjection := by
    apply Generator.starProjection_commutes_of_invariant
    · exact invariant_closed_linearCombination_range v _ hT
    · rw [← map_star, hdsa.star_eq]
      exact invariant_closed_linearCombination_range v _ hT
  have hQB := commutes_of_normGeneratedExtension φ d hgen π V.starProjection
    (isStarProjection_starProjection (U := V)).isSelfAdjoint hQA hQT
  have hξ : ξ ∈ V := by
    have h := Submodule.le_topologicalClosure W (hv 1 0)
    simpa only [v, map_one, pow_zero, one_apply_eq_self] using h
  have hQξ : V.starProjection ξ = ξ := Submodule.starProjection_eq_self_iff.mpr hξ
  have hB (b : B) : π b ξ ∈ V := by
    apply Submodule.starProjection_eq_self_iff.mp
    calc
      V.starProjection (π b ξ) = π b (V.starProjection ξ) :=
        congrArg (fun T : H →L[ℂ] H => T ξ) (hQB b)
      _ = π b ξ := by rw [hQξ]
  intro x
  change x ∈ V
  exact hcyc.induction_on x (Submodule.isClosed_topologicalClosure W) hB

/-- Countability needed by the spatial splitting proof, even when the source
or its cyclic representation is nonseparable. -/
theorem derivation_extension_commutant_countable
    (φ : A →⋆ₐ[ℂ] B) (d : B) (hdsa : IsSelfAdjoint d)
    (hgen : NormGeneratedExtension φ d)
    (D : A →L[ℂ] A) (hd : ∀ a, φ (D a) = d * φ a - φ a * d)
    (π : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcyc : DenseRange (fun b => π b ξ)) :
    HasCountableProjectionFamilies
      (generatedVonNeumannAlgebra (π.comp φ).range).commutant := by
  let N := generatedVonNeumannAlgebra (π.comp φ).range
  apply countableProjectionFamilies_of_separating_vectors (fun n => (π d ^ n) ξ)
  intro b hb
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  have hdense := denseRange_derivation_power_span φ d hdsa hgen D hd π ξ hcyc
  have hv (i : A × ℕ) : b.val (π (φ i.1) ((π d ^ i.2) ξ)) = 0 := by
    have ha : π (φ i.1) ∈ N :=
      subset_generatedVonNeumannAlgebra (π.comp φ).range ⟨i.1, rfl⟩
    have hc := (VonNeumannAlgebra.mem_commutant_iff.mp b.property _ ha).symm
    change (b.val * π (φ i.1)) ((π d ^ i.2) ξ) = 0
    rw [hc, mul_apply_eq_comp, hb, map_zero]
  have hzero (c : (A × ℕ) →₀ ℂ) :
      b.val (Finsupp.linearCombination ℂ
        (fun i : A × ℕ => π (φ i.1) ((π d ^ i.2) ξ)) c) = 0 := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, hv, smul_zero,
      Finset.sum_const_zero]
  exact hdense.induction_on x (isClosed_eq b.val.continuous continuous_const) hzero

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FactorSpatialSplit
attribute [-instance] _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spatial splitting for factors with countably decomposable commutant -/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_selfAdjoint_split_of_factor
    [Nontrivial H] (M : VonNeumannAlgebra H) (hM : ScalarCenter M)
    (hFamilies : HasCountableProjectionFamilies M.commutant)
    (T : H →L[ℂ] H) (hTsa : IsSelfAdjoint T)
    (hT : ∀ a ∈ M, T * a - a * T ∈ M) :
    ∃ a : H →L[ℂ] H, a ∈ M ∧ IsSelfAdjoint a ∧ ‖a‖ ≤ ‖T‖ ∧
      T - a ∈ M.commutant :=
  exists_selfAdjoint_split_of_factor_commutant M (scalarCenter_commutant M hM)
    hFamilies T hTsa hT

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GeneratedDerivationExtension
attribute [-instance] _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The concrete generated algebra and its faithful maximal quotient

This constructs the one-implementer extension used in the unital case of
Sakai's argument. Its generation property is retained through the quotient.
No innerness or ideal membership of the implementer is assumed here.
-/

namespace KadisonKastler

noncomputable section

open CuntzPureness

universe u v

variable {A : Type u} {B : Type v} [CStarAlgebra A] [CStarAlgebra B]

theorem generatedExtension_normGenerated (φ : A →⋆ₐ[ℂ] B) (d : B) :
    NormGeneratedExtension (generatedExtensionEmbedding φ d) (generatedExtensionElement φ d) := by
  intro C hC hsource hd
  let S := generatedExtensionAlgebra φ d
  let E : StarSubalgebra ℂ B := C.map S.subtype
  have hEclosed : IsClosed (E : Set B) :=
    (StarSubalgebra.isClosed_topologicalClosure _).isClosedMap_subtype_val _ hC
  have hSE : S ≤ E := by
    apply StarSubalgebra.topologicalClosure_minimal _ hEclosed
    apply StarAlgebra.adjoin_le
    rintro x (⟨a, rfl⟩ | hx)
    · exact ⟨generatedExtensionEmbedding φ d a, hsource a, rfl⟩
    · have hx' : x = d := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨generatedExtensionElement φ d, hd, rfl⟩
  apply top_unique
  intro x _
  obtain ⟨y, hy, he⟩ := hSE x.property
  have hxy : y = x := Subtype.ext he
  rwa [← hxy]

theorem NormGeneratedExtension.map_surjective
    (φ : A →⋆ₐ[ℂ] B) (d : B) (hgen : NormGeneratedExtension φ d)
    {C : Type*} [CStarAlgebra C] (ψ : B →⋆ₐ[ℂ] C)
    (hψ : Function.Surjective ψ) : NormGeneratedExtension (ψ.comp φ) (ψ d) := by
  intro E hE hsource hd
  have hc : Continuous ψ :=
    (ψ.toLinearMap.mkContinuous 1 (fun x => by
      change ‖ψ x‖ ≤ 1 * ‖x‖
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le ψ x)).continuous
  have htop : E.comap ψ = ⊤ :=
    hgen (E.comap ψ) (hE.preimage hc) hsource hd
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := hψ y
  change x ∈ E.comap ψ
  rw [htop]
  trivial

theorem exists_generated_derivation_extension
    [Nontrivial A] (hA : CStarSimple A) (D : A →L[ℂ] A)
    (hD : ∀ x y, D (x * y) = D x * y + x * D y)
    (hstar : ∀ x, D (star x) = -star (D x)) :
    ∃ (B : Type u) (_ : CStarAlgebra B) (_ : Nontrivial B)
      (φ : A →⋆ₐ[ℂ] B) (d : B),
      Function.Injective φ ∧ IsSelfAdjoint d ∧
      (∀ a, φ (D a) = d * φ a - φ a * d) ∧
      NormGeneratedExtension φ d ∧
      (∀ (C : Type u) [CStarAlgebra C] [Nontrivial C]
        (ψ : B →⋆ₐ[ℂ] C), Function.Injective ψ) := by
  obtain ⟨H, _, _, _, _, π, hπ, _, T, hT, hTD⟩ :=
    exists_simple_spatial_derivation hA D hD hstar
  let S := generatedExtensionAlgebra π T
  let φ := generatedExtensionEmbedding π T
  let d := generatedExtensionElement π T
  let : CompleteSpace S := inferInstanceAs
    (CompleteSpace (StarAlgebra.adjoin ℂ (Set.range π ∪ {T})).topologicalClosure)
  let : CStarAlgebra S := inferInstance
  let : Nontrivial S := inferInstance
  let : PartialOrder S := CStarAlgebra.spectralOrder S
  let : StarOrderedRing S := CStarAlgebra.spectralOrderedRing S
  have hd : ∀ a, φ (D a) = d * φ a - φ a * d := fun a => Subtype.ext (hTD a)
  have hdsa : IsSelfAdjoint d := Subtype.ext hT.star_eq
  obtain ⟨J, hJ, hmax⟩ := exists_maximal_proper_closedStarIdeal (B := S)
  let : Nontrivial J.Quotient := closedStarIdeal_quotient_nontrivial J hJ
  let ψ := J.quotientStarHom
  refine ⟨J.Quotient, inferInstance, inferInstance, ψ.comp φ, ψ d,
    simple_quotient_composition_injective hA φ J hJ, hdsa.map ψ, ?_, ?_, ?_⟩
  · intro a
    change ψ (φ (D a)) = ψ d * ψ (φ a) - ψ (φ a) * ψ d
    rw [hd, map_sub, map_mul, map_mul]
  · exact NormGeneratedExtension.map_surjective φ d (generatedExtension_normGenerated π T) ψ
      J.quotientMap_surjective
  · intro C _ _ χ
    exact maximal_closedStarIdeal_quotient_injective J hmax χ

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HermitianAnnihilatorBall
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The compact annihilator ball for Sakai's separation argument -/

namespace KadisonKastler

noncomputable section

open scoped Topology

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem hermitianAnnihilatorBall_isCompact (φ : A →⋆ₐ[ℂ] B) :
    IsCompact (hermitianAnnihilatorBall φ) := by
  have hstar : IsClosed {f : WeakDual ℂ B | ∀ b : B, f (star b) = star (f b)} := by
    simpa only [Set.ofPred_forall] using isClosed_iInter (fun b : B =>
      (isClosed_eq (WeakDual.eval_continuous (star b))
        (continuous_star.comp (WeakDual.eval_continuous b)) :
          IsClosed {f : WeakDual ℂ B | f (star b) = star (f b)}))
  have hann : IsClosed {f : WeakDual ℂ B | ∀ a : A, f (φ a) = 0} := by
    simpa only [Set.ofPred_forall] using isClosed_iInter (fun a : A =>
      (isClosed_eq (WeakDual.eval_continuous (φ a)) continuous_const :
        IsClosed {f : WeakDual ℂ B | f (φ a) = (0 : ℂ)}))
  have he : hermitianAnnihilatorBall φ =
      WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : B →L[ℂ] ℂ) 1 ∩
        {f | ∀ b, f (star b) = star (f b)} ∩ {f | ∀ a, f (φ a) = 0} := by
    ext f
    simp only [hermitianAnnihilatorBall, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, and_assoc]
  rw [he]
  exact ((WeakDual.isCompact_closedBall (0 : B →L[ℂ] ℂ) 1).inter_right hstar).inter_right hann

theorem hermitianAnnihilatorBall_convex (φ : A →⋆ₐ[ℂ] B) :
    Convex ℝ (hermitianAnnihilatorBall φ) := by
  intro f hf g hg a b ha hb hab
  refine ⟨?_, ?_, ?_⟩
  · change ‖a • f.toStrongDual + b • g.toStrongDual‖ ≤ 1
    calc
      _ ≤ ‖a • f.toStrongDual‖ + ‖b • g.toStrongDual‖ := norm_add_le _ _
      _ = a * ‖f.toStrongDual‖ + b * ‖g.toStrongDual‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left hf.1 ha)
        (mul_le_mul_of_nonneg_left hg.1 hb)
      _ = 1 := by simpa using hab
  · intro x
    change a • f (star x) + b • g (star x) = star (a • f x + b • g x)
    rw [hf.2.1, hg.2.1]
    simp only [star_add, star_smul, star_trivial]
  · intro x
    change a • f (φ x) + b • g (φ x) = 0
    rw [hf.2.2, hg.2.2]
    simp

theorem hermitianAnnihilatorBall_zero (φ : A →⋆ₐ[ℂ] B) :
    (0 : WeakDual ℂ B) ∈ hermitianAnnihilatorBall φ := by
  refine ⟨?_, ?_, ?_⟩
  · change ‖(0 : B →L[ℂ] ℂ)‖ ≤ 1
    norm_num
  · intro x
    change (0 : ℂ) = star 0
    rw [star_zero]
  · intro x
    rfl

theorem hermitianAnnihilatorBall_extreme_norm
    (φ : A →⋆ₐ[ℂ] B) (f : WeakDual ℂ B)
    (hf : f ∈ (hermitianAnnihilatorBall φ).extremePoints ℝ) (hne : f ≠ 0) :
    ‖f.toStrongDual‖ = 1 := by
  have hmem := (mem_extremePoints.mp hf).1
  have hn0 : f.toStrongDual ≠ 0 := by
    intro h
    apply hne
    exact WeakDual.toStrongDual.injective h
  have hn : 0 < ‖f.toStrongDual‖ := norm_pos_iff.mpr hn0
  apply le_antisymm hmem.1
  by_contra h
  have hlt : ‖f.toStrongDual‖ < 1 := lt_of_not_ge h
  let g : WeakDual ℂ B := ‖f.toStrongDual‖⁻¹ • f
  have hg : g ∈ hermitianAnnihilatorBall φ := by
    refine ⟨?_, ?_, ?_⟩
    · change ‖‖f.toStrongDual‖⁻¹ • f.toStrongDual‖ ≤ 1
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_cancel₀ hn.ne']
    · intro x
      change ‖f.toStrongDual‖⁻¹ • f (star x) = star (‖f.toStrongDual‖⁻¹ • f x)
      rw [hmem.2.1]
      simp only [star_smul, star_trivial]
    · intro x
      change ‖f.toStrongDual‖⁻¹ • f (φ x) = 0
      rw [hmem.2.2, smul_zero]
  have hseg : f ∈ openSegment ℝ (0 : WeakDual ℂ B) g := by
    refine ⟨1 - ‖f.toStrongDual‖, ‖f.toStrongDual‖, sub_pos.mpr hlt, hn, by ring, ?_⟩
    rw [smul_zero, zero_add]
    apply DFunLike.ext
    intro x
    change ‖f.toStrongDual‖ • (‖f.toStrongDual‖⁻¹ • f x) = f x
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  exact hne ((mem_extremePoints.mp hf).2 0 (hermitianAnnihilatorBall_zero φ) g hg hseg).1.symm

theorem exists_extreme_hermitian_annihilator
    (φ : A →⋆ₐ[ℂ] B) (b : B)
    (hsep : ∃ f ∈ hermitianAnnihilatorBall φ, f b ≠ 0) :
    ∃ g ∈ (hermitianAnnihilatorBall φ).extremePoints ℝ,
      ‖g.toStrongDual‖ = 1 ∧ g b ≠ 0 := by
  let : IsScalarTower ℝ ℂ (WeakDual ℂ B) :=
    inferInstanceAs (IsScalarTower ℝ ℂ (B →L[ℂ] ℂ))
  let : ContinuousSMul ℝ (WeakDual ℂ B) := IsScalarTower.continuousSMul ℂ
  let : LocallyConvexSpace ℝ (WeakDual ℂ B) :=
    (WeakDual.withSeminorms ℂ B).toLocallyConvexSpace
  have hex : ∃ g ∈ (hermitianAnnihilatorBall φ).extremePoints ℝ, g b ≠ 0 := by
    by_contra h
    push Not at h
    let L : WeakDual ℂ B →ₗ[ℝ] ℂ :=
      { toFun := fun f => f b
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
    have hclosed : IsClosed (L.ker : Set (WeakDual ℂ B)) :=
      isClosed_eq (WeakDual.eval_continuous b) continuous_const
    have hsub : convexHull ℝ ((hermitianAnnihilatorBall φ).extremePoints ℝ) ⊆ L.ker :=
      convexHull_min h L.ker.convex
    have hc := closure_minimal hsub hclosed
    have hKM : closure (convexHull ℝ ((hermitianAnnihilatorBall φ).extremePoints ℝ)) =
        hermitianAnnihilatorBall φ :=
      closure_convexHull_extremePoints (E := WeakDual ℂ B)
        (hermitianAnnihilatorBall_isCompact φ) (hermitianAnnihilatorBall_convex φ)
    rw [hKM] at hc
    obtain ⟨f, hf, hb⟩ := hsep
    exact hb (hc hf)
  obtain ⟨g, hg, hgb⟩ := hex
  refine ⟨g, hg, hermitianAnnihilatorBall_extreme_norm φ g hg ?_, hgb⟩
  intro hz
  apply hgb
  rw [hz]
  rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HermitianSeparation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Separating a self-adjoint element from a closed star subalgebra

Hahn–Banach on the Banach-space quotient gives a norm-one functional
annihilating the source. Its Hermitian part still separates a self-adjoint
element. The compact annihilator ball then supplies an extreme separator.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem conjugateFunctional_norm_le (f : B →L[ℂ] ℂ) : ‖conjugateFunctional f‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg f)
  intro b
  change ‖star (f (star b))‖ ≤ ‖f‖ * ‖b‖
  rw [norm_star, ← norm_star b]
  exact f.le_opNorm (star b)

theorem exists_hermitian_separator (φ : A →⋆ₐ[ℂ] B)
    (hφ : Function.Injective φ) (b : B) (hb : IsSelfAdjoint b)
    (hnot : b ∉ Set.range φ) :
    ∃ f ∈ hermitianAnnihilatorBall φ, f b ≠ 0 := by
  let P := φ.range.toSubalgebra.toSubmodule
  have hclosed : IsClosed (P : Set B) :=
    (NonUnitalStarAlgHom.isometry φ hφ).isClosedEmbedding.isClosed_range
  let : IsClosed (P : Set B) := hclosed
  let q : B →L[ℂ] (B ⧸ P) := P.mkQ.mkContinuous 1 (fun x => by
    change ‖(Submodule.Quotient.mk x : B ⧸ P)‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using Submodule.Quotient.norm_mk_le P x)
  have hqb : q b ≠ 0 := by
    intro hz
    apply hnot
    exact (Submodule.Quotient.mk_eq_zero P).mp hz
  obtain ⟨g, hgn, hgb⟩ := exists_dual_vector ℂ (q b) (norm_ne_zero_iff.mpr hqb)
  let f₀ := g.comp q
  have hf₀ : ‖f₀‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖g (q x)‖ ≤ 1 * ‖x‖
    calc
      _ ≤ ‖g‖ * ‖q x‖ := g.le_opNorm _
      _ ≤ 1 * ‖x‖ := by
        rw [hgn, one_mul, one_mul]
        exact Submodule.Quotient.norm_mk_le P x
  have hann (a : A) : f₀ (φ a) = 0 := by
    have hz : q (φ a) = 0 := (Submodule.Quotient.mk_eq_zero P).mpr ⟨a, rfl⟩
    change g (q (φ a)) = 0
    rw [hz, map_zero]
  let F : B →L[ℂ] ℂ := (1 / 2 : ℂ) • (f₀ + conjugateFunctional f₀)
  have hF : ‖F‖ ≤ 1 := by
    calc
      ‖F‖ = (1 / 2 : ℝ) * ‖f₀ + conjugateFunctional f₀‖ := by
        dsimp only [F]
        rw [norm_smul]
        norm_num
      _ ≤ (1 / 2 : ℝ) * (‖f₀‖ + ‖conjugateFunctional f₀‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
      _ ≤ 1 := by linarith [conjugateFunctional_norm_le f₀]
  refine ⟨StrongDual.toWeakDual F, ⟨hF, ?_, ?_⟩, ?_⟩
  · intro x
    change (1 / 2 : ℂ) • (f₀ (star x) + star (f₀ (star (star x)))) =
      star ((1 / 2 : ℂ) • (f₀ x + star (f₀ (star x))))
    simp only [star_smul, star_add, star_star]
    norm_num
    ring
  · intro a
    change (1 / 2 : ℂ) • (f₀ (φ a) + star (f₀ (star (φ a)))) = 0
    rw [← map_star φ, hann, hann, star_zero, zero_add, smul_zero]
  · have hval : F b = (‖q b‖ : ℂ) := by
      change (1 / 2 : ℂ) • (f₀ b + star (f₀ (star b))) = _
      rw [hb.star_eq]
      change (1 / 2 : ℂ) • (g (q b) + star (g (q b))) = _
      rw [hgb]
      rw [RCLike.star_def, RCLike.conj_ofReal]
      change (1 / 2 : ℂ) * ((‖q b‖ : ℂ) + (‖q b‖ : ℂ)) = _
      ring
    change F b ≠ 0
    rw [hval]
    exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hqb)

theorem exists_extreme_hermitian_separator (φ : A →⋆ₐ[ℂ] B)
    (hφ : Function.Injective φ) (b : B) (hb : IsSelfAdjoint b)
    (hnot : b ∉ Set.range φ) :
    ∃ f ∈ (hermitianAnnihilatorBall φ).extremePoints ℝ,
      ‖f.toStrongDual‖ = 1 ∧ f b ≠ 0 :=
  exists_extreme_hermitian_annihilator φ b (exists_hermitian_separator φ hφ b hb hnot)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SpatialCoefficientClosure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Vanishing vector coefficients pass to the bicommutant -/

namespace KadisonKastler

noncomputable section

open Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem coefficient_zero_generated_contraction
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ η : H)
    (hzero : ∀ a : S, inner ℂ η (a.val ξ) = 0)
    (b : H →L[ℂ] H) (hb : b ∈ generatedVonNeumannAlgebra S) (hbn : ‖b‖ ≤ 1) :
    inner ℂ η (b ξ) = 0 := by
  classical
  have hb' : b ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) := by
    rwa [← generatedVonNeumannAlgebra_coe]
  obtain ⟨a, _, ht⟩ := publishedKaplanskyDensity.exists_strong_contraction_net S b hb' hbn
  have hlim := (tendsto_const_nhds : Tendsto (fun _ : Finset H × ℕ => η) atTop (𝓝 η)).inner
    (𝕜 := ℂ) (ht ξ)
  have he : (fun d : Finset H × ℕ => inner ℂ η ((a d).val ξ)) = fun _ => 0 :=
    funext (fun d => hzero (a d))
  rw [he] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

theorem coefficient_zero_generated
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (ξ η : H)
    (hzero : ∀ a : S, inner ℂ η (a.val ξ) = 0)
    (b : H →L[ℂ] H) (hb : b ∈ generatedVonNeumannAlgebra S) :
    inner ℂ η (b ξ) = 0 := by
  let c : ℝ := ‖b‖ + 1
  have hc : 0 < c := by dsimp [c] <;> positivity
  have hb' : (c⁻¹ : ℝ) • b ∈ generatedVonNeumannAlgebra S :=
    ((generatedVonNeumannAlgebra S).toStarSubalgebra.toSubalgebra.toSubmodule.restrictScalars
      ℝ).smul_mem c⁻¹ hb
  have hn : ‖(c⁻¹ : ℝ) • b‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le)]
    rw [← div_eq_inv_mul]
    exact (div_le_one hc).mpr (by dsimp [c] <;> linarith)
  have hz := coefficient_zero_generated_contraction S ξ η hzero _ hb' hn
  change inner ℂ η ((c⁻¹ : ℝ) • b ξ) = 0 at hz
  rw [inner_smul_right_eq_smul] at hz
  exact (smul_eq_zero.mp hz).resolve_left (inv_ne_zero hc.ne')

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SimpleDerivationConstruction
attribute [-instance] _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Innerness of bounded derivations of simple unital C-star algebras

The maximal simple extension, extreme Hermitian separator, spatial factor
splitting and faithful-corner norm argument together prove the precise
unital input used in the stability application.
-/

namespace KadisonKastler

noncomputable section

open Generator Generator.Tracial
open scoped InnerProductSpace

universe u

variable {A B : Type u} [CStarAlgebra A] [CStarAlgebra B] [Nontrivial B]

theorem simple_extension_implementer_mem_range
    (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ)
    (d : B) (hdsa : IsSelfAdjoint d) (hgen : NormGeneratedExtension φ d)
    (hB : ∀ (C : Type u) [CStarAlgebra C] [Nontrivial C]
      (ψ : B →⋆ₐ[ℂ] C), Function.Injective ψ)
    (D : A →L[ℂ] A) (hd : ∀ a, φ (D a) = d * φ a - φ a * d) :
    d ∈ Set.range φ := by
  by_contra hnot
  obtain ⟨F, hF, hFn, hFd⟩ := exists_extreme_hermitian_separator φ hφ d hdsa hnot
  have hFm := (mem_extremePoints.mp hF).1
  obtain ⟨H, hHn, hHi, hHc, π, ξ, S, hξ, hcyc, hS, hSS, hSπ, hcoeff⟩ :=
    exists_signed_cyclic_functional F.toStrongDual hFm.2.1 hFn
  let : NormedAddCommGroup H := hHn
  let : InnerProductSpace ℂ H := hHi
  let : CompleteSpace H := hHc
  let : Nontrivial H := by
    by_contra h
    have : Subsingleton H := not_nontrivial_iff_subsingleton.mp h
    have he : ξ = 0 := Subsingleton.elim _ _
    simp only [he, norm_zero] at hξ
    norm_num at hξ
  have hrep : F.toStrongDual = signedVectorFunctional π S ξ := by
    ext b
    exact hcoeff b
  let N := generatedVonNeumannAlgebra (π.comp φ).range
  have hN : ScalarCenter N := factor_of_extreme_signed_derivation_extension
    φ d hgen D hd F hF π ξ hξ hcyc S hS hSS hSπ hrep
  have hfamilies := derivation_extension_commutant_countable φ d hdsa hgen D hd π ξ hcyc
  have hsource : ∀ a : (π.comp φ).range,
      π d * a.val - a.val * π d ∈ N := by
    intro a
    obtain ⟨b, hb⟩ := a.property
    change π (φ b) = a.val at hb
    rw [← hb, ← map_mul, ← map_mul, ← map_sub, ← hd]
    exact subset_generatedVonNeumannAlgebra (π.comp φ).range ⟨D b, rfl⟩
  have hnorm : ∀ a ∈ N, π d * a - a * π d ∈ N :=
    spatial_commutator_mem_generated (π.comp φ).range (π d) hsource
  obtain ⟨a, ha, hasa, _, hb⟩ := exists_selfAdjoint_split_of_factor N hN hfamilies
    (π d) (hdsa.map π) hnorm
  have hdN := extension_implementer_mem_of_spatial_split φ d hdsa hgen hB π hN a ha hasa hb
  have hann : ∀ a : (π.comp φ).range, inner ℂ (S ξ) (a.val ξ) = 0 := by
    intro a
    obtain ⟨b, hb⟩ := a.property
    change π (φ b) = a.val at hb
    rw [← hb, ← hcoeff]
    exact hFm.2.2 b
  have hz := coefficient_zero_generated (π.comp φ).range ξ (S ξ) hann (π d) hdN
  exact hFd ((hcoeff d).trans hz)

theorem antiStar_derivation_inner_of_simple [Nontrivial A]
    (hA : CStarSimple A) (D : A →L[ℂ] A)
    (hD : ∀ x y, D (x * y) = D x * y + x * D y)
    (hstar : ∀ x, D (star x) = -star (D x)) :
    ∃ a : A, ∀ x, D x = a * x - x * a := by
  obtain ⟨B, hBc, hBn, φ, d, hφ, hdsa, hd, hgen, hB⟩ :=
    exists_generated_derivation_extension hA D hD hstar
  let : CStarAlgebra B := hBc
  let : Nontrivial B := hBn
  obtain ⟨a, ha⟩ := simple_extension_implementer_mem_range φ hφ d hdsa hgen hB D hd
  refine ⟨a, fun x => hφ ?_⟩
  rw [hd, map_sub, map_mul, map_mul, ha]

theorem publishedSimpleDerivationInner_oai : PublishedSimpleDerivationInner.{u} := by
  intro A _ _ hA D hD
  exact inner_derivation_of_antiStar_inner
    (fun F hF hFs => antiStar_derivation_inner_of_simple hA F hF hFs) D hD

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.publishedSimpleDerivationInner_oai.{u} := @OAI.KadisonKastler.publishedSimpleDerivationInner_oai.{u}
