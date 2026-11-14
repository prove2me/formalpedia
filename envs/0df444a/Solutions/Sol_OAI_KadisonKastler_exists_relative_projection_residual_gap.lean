-- Prove2me | solution 1 for OAI.KadisonKastler.exists_relative_projection_residual_gap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:15:47.803137+00:00
-- url     : https://prove2.me/submissions/acaffeb1-f53b-4a97-9bd4-15b5c39228c7

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.QuadraticDiscriminant
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Cone.Closure
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.PiL2
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
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.RCLike.Real
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
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
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
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Moments.ComplexMGF
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
import Mathlib.Topology.Bases
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
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K034
import Theorems.Thm_OAI_KadisonKastler_exists_relative_unitary_residual_gap

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SupportBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Square sums over orthogonal supports

These are the Hilbert-space estimates converting bounds through each
diagonal label into the uniform coefficient-column drift in §3.
-/

namespace KadisonKastler

open Finset

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem norm_sum_sq_of_pairwise_orthogonal {ι : Type*} (s : Finset ι) (v : ι → H)
    (hv : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℂ (v i) (v j) = 0) :
    ‖∑ i ∈ s, v i‖ ^ 2 = ∑ i ∈ s, ‖v i‖ ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have horth : inner ℂ (v a) (∑ i ∈ s, v i) = 0 := by
      rw [inner_sum]
      apply sum_eq_zero
      intro i hi
      exact hv a (by simp) i (by simp [hi]) (by aesop)
    rw [sum_insert ha, norm_add_sq (𝕜 := ℂ), horth]
    rw [ih (by intro i hi j hj hij; exact hv i (by simp [hi]) j (by simp [hj]) hij),
      sum_insert ha]
    simp only [map_zero, mul_zero, add_zero]

variable [CompleteSpace H]

theorem orthogonal_projection_vectors {ι : Type*} (P : ι → H →L[ℂ] H)
    (hself : ∀ i, IsSelfAdjoint (P i))
    (horth : ∀ i j, i ≠ j → P i * P j = 0) (x : H) :
    Pairwise (fun i j => inner ℂ (P i x) (P j x) = 0) := by
  intro i j hij
  have hstar : (P i).adjoint = P i := (hself i).star_eq
  rw [← ContinuousLinearMap.adjoint_inner_right, hstar]
  have hz : P i (P j x) = 0 := by
    change (P i * P j) x = 0
    rw [horth i j hij]
    rfl
  rw [hz, inner_zero_right]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_BoundedSpectralApproximation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded coefficients in the constructed finite spectral approximations

The dyadic spectral intervals remain inside their initial norm bounds.
This records the coefficient bound needed by the threshold-cut argument.
-/

namespace Generator.Tracial

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem SpectralInterval.level_nested {x : M.toStarSubalgebra} (I : SpectralInterval x)
    (hx : IsSelfAdjoint x) (hI : I.lo ≤ I.hi) :
    ∀ n i, I.lo ≤ (I.level hx n i).lo ∧
      (I.level hx n i).lo ≤ (I.level hx n i).hi ∧ (I.level hx n i).hi ≤ I.hi := by
  intro n
  induction n with
  | zero => intro i; exact ⟨le_rfl,hI,le_rfl⟩
  | succ n ih =>
    rintro ⟨i,b⟩
    obtain ⟨hlo,hw,hhi⟩ := ih i
    change I.lo ≤ ((I.level hx n i).child hx b).lo ∧
      ((I.level hx n i).child hx b).lo ≤ ((I.level hx n i).child hx b).hi ∧
      ((I.level hx n i).child hx b).hi ≤ I.hi
    cases b <;> simp only [SpectralInterval.child,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,
      SpectralInterval.low,SpectralInterval.high,SpectralInterval.midpoint] <;>
      (refine ⟨?_,?_,?_⟩ <;> linarith)

theorem exists_bounded_spectral_approximation (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x)
    (hn : ‖x‖ ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ (Q : CornerPartition (identityProjection M)) (c : Fin Q.size → ℝ),
      (∀ i, c i ∈ Set.Icc (-1 : ℝ) 1) ∧
      ‖x - ∑ i, (c i : ℂ) • (Q.piece i).val‖ < ε := by
  let I := initialSpectralInterval (identityProjection M) x hx
  have hI : I.lo ≤ I.hi := neg_le_self (norm_nonneg _)
  obtain ⟨n,happrox⟩ := I.exists_approximant hx hI ε hε
  let e := (Fintype.equivFin (DyadicIndex n)).symm
  refine ⟨I.partition hx n,fun i => (I.level hx n (e i)).lo,?_,?_⟩
  · intro i
    obtain ⟨hlo,hw,hhi⟩ := I.level_nested hx hI n (e i)
    have hl : -‖x‖ ≤ (I.level hx n (e i)).lo := hlo
    have hh : (I.level hx n (e i)).hi ≤ ‖x‖ := hhi
    exact ⟨by linarith,by linarith⟩
  · have he := Equiv.sum_comp e (fun i => ((I.level hx n i).lo : ℂ) •
        (I.level hx n i).proj.val)
    change ‖x - ∑ i, ((I.level hx n (e i)).lo : ℂ) •
      (I.level hx n (e i)).proj.val‖ < ε
    rw [he]
    change ‖(1 : M.toStarSubalgebra) * x * 1 - ∑ i : DyadicIndex n,
      ((I.level hx n i).lo : ℂ) • (I.level hx n i).proj.val‖ < ε at happrox
    simpa only [one_mul,mul_one] using happrox

end

end Generator.Tracial

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_JointProjectionEnergy
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Vector energy in two commuting finite spectral partitions -/

namespace KadisonKastler

open Finset
open scoped BigOperators

noncomputable section

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [Fintype κ]

omit [CompleteSpace H] in
theorem jointProjection_total (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
    (hP : ∑ i, P i = 1) (hQ : ∑ j, Q j = 1) :
    (∑ a : ι × κ, P a.1 * Q a.2) = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum,hQ,mul_one]
  exact hP

omit [CompleteSpace H] [Fintype ι] [Fintype κ] in
theorem jointProjection_orthogonal
    (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
    (hP : ∀ i k, i ≠ k → P i * P k = 0)
    (hQ : ∀ j l, j ≠ l → Q j * Q l = 0)
    (hc : ∀ i j, Commute (P i) (Q j)) :
    ∀ a b : ι × κ, a ≠ b → (P a.1 * Q a.2) * (P b.1 * Q b.2) = 0 := by
  intro a b hab
  have he : (P a.1 * Q a.2) * (P b.1 * Q b.2) =
      (P a.1 * P b.1) * (Q a.2 * Q b.2) := by
    rw [mul_assoc,← mul_assoc (Q a.2),(hc b.1 a.2).eq.symm]
    simp only [mul_assoc]
  rw [he]
  by_cases hi : a.1 = b.1
  · have hj : a.2 ≠ b.2 := fun hj => hab (Prod.ext hi hj)
    rw [hQ _ _ hj,mul_zero]
  · rw [hP _ _ hi,zero_mul]

omit [CompleteSpace H] in
theorem jointProjection_weighted_sum
    (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
    (hP : ∑ i, P i = 1) (hQ : ∑ j, Q j = 1)
    (c : ι → ℂ) (d : κ → ℂ) :
    (∑ a : ι × κ, (c a.1-d a.2) • (P a.1 * Q a.2)) =
      (∑ i, c i • P i) - (∑ j, d j • Q j) := by
  simp_rw [sub_smul]
  rw [Finset.sum_sub_distrib,Fintype.sum_prod_type,Fintype.sum_prod_type]
  have hl : (∑ i, ∑ j, c i • (P i * Q j)) = ∑ i, c i • P i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.smul_sum,← Finset.mul_sum,hQ,mul_one]
  have hr : (∑ i, ∑ j, d j • (P i * Q j)) = ∑ j, d j • Q j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.smul_sum,← Finset.sum_mul,hP,one_mul]
  rw [hl,hr]

theorem norm_jointProjection_weighted_sum_sq
    (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i)) (hQ : ∀ j, IsStarProjection (Q j))
    (hPo : ∀ i k, i ≠ k → P i * P k = 0)
    (hQo : ∀ j l, j ≠ l → Q j * Q l = 0)
    (hc : ∀ i j, Commute (P i) (Q j)) (c : ι × κ → ℂ) (ξ : H) :
    ‖(∑ a : ι × κ, c a • (P a.1 * Q a.2)) ξ‖ ^ 2 =
      ∑ a : ι × κ, ‖c a‖ ^ 2 * ‖(P a.1 * Q a.2) ξ‖ ^ 2 := by
  classical
  have ho := orthogonal_projection_vectors (fun a : ι × κ => P a.1 * Q a.2)
    (fun a => ((hP a.1).mul (hQ a.2) (hc a.1 a.2)).isSelfAdjoint)
    (jointProjection_orthogonal P Q hPo hQo hc) ξ
  have horth : ∀ a ∈ (univ : Finset (ι × κ)), ∀ b ∈ (univ : Finset (ι × κ)),
      a ≠ b → inner ℂ (c a • (P a.1 * Q a.2) ξ) (c b • (P b.1 * Q b.2) ξ) = 0 := by
    intro a _ b _ hab
    rw [inner_smul_left,inner_smul_right,ho hab,mul_zero,mul_zero]
  have he := norm_sum_sq_of_pairwise_orthogonal univ
    (fun a : ι × κ => c a • (P a.1 * Q a.2) ξ) horth
  simpa only [_root_.sum_apply,smul_apply,norm_smul,mul_pow] using he

theorem jointProjection_gap_energy
    (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i)) (hQ : ∀ j, IsStarProjection (Q j))
    (hPo : ∀ i k, i ≠ k → P i * P k = 0)
    (hQo : ∀ j l, j ≠ l → Q j * Q l = 0)
    (hPt : ∑ i, P i = 1) (hQt : ∑ j, Q j = 1)
    (hc : ∀ i j, Commute (P i) (Q j)) (c : ι → ℂ) (d : κ → ℂ) (ξ : H) :
    ‖((∑ i, c i • P i) - (∑ j, d j • Q j)) ξ‖ ^ 2 =
      ∑ a : ι × κ, ‖c a.1-d a.2‖ ^ 2 * ‖(P a.1 * Q a.2) ξ‖ ^ 2 := by
  rw [← jointProjection_weighted_sum P Q hPt hQt c d]
  exact norm_jointProjection_weighted_sum_sq P Q hP hQ hPo hQo hc _ ξ

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ThresholdCutIntegral
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Averaging finite spectral threshold cuts

Two spectral values are separated by a threshold on an interval of
length equal to their distance. Finite weighted sums give the exact
average cut energy and its Cauchy--Schwarz bound.
-/

namespace KadisonKastler

open MeasureTheory
open scoped BigOperators

noncomputable section

theorem thresholdDifference_sq (x y t : ℝ) :
    thresholdDifference x y t ^ 2 =
      (Set.Ico (min x y) (max x y)).indicator (fun _ => (1 : ℝ)) t := by
  by_cases hxy : x ≤ y
  · rw [min_eq_left hxy,max_eq_right hxy]
    by_cases htx : t < x
    · have hty : t < y := htx.trans_le hxy
      simp [thresholdDifference,htx,hty,Set.mem_Ico,not_le.mpr htx]
    · by_cases hty : t < y
      · simp [thresholdDifference,htx,hty,Set.mem_Ico,le_of_not_gt htx]
      · simp [thresholdDifference,htx,hty,Set.mem_Ico]
  · have hyx : y ≤ x := le_of_not_ge hxy
    rw [min_eq_right hyx,max_eq_left hyx]
    by_cases hty : t < y
    · have htx : t < x := hty.trans_le hyx
      simp [thresholdDifference,htx,hty,Set.mem_Ico,not_le.mpr hty]
    · by_cases htx : t < x
      · simp [thresholdDifference,htx,hty,Set.mem_Ico,le_of_not_gt hty]
      · simp [thresholdDifference,htx,hty,Set.mem_Ico]

theorem thresholdDifference_sq_integrable (x y : ℝ) :
    Integrable (fun t => thresholdDifference x y t ^ 2) := by
  simp_rw [thresholdDifference_sq]
  exact (integrable_indicator_iff measurableSet_Ico).mpr
    (integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top))

theorem integral_thresholdDifference_sq (x y : ℝ) :
    (∫ t, thresholdDifference x y t ^ 2) = |x - y| := by
  simp_rw [thresholdDifference_sq]
  rw [integral_indicator_const (1 : ℝ) measurableSet_Ico]
  simp only [smul_eq_mul,mul_one,Measure.real,Real.volume_Ico,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (min_le_max))]
  exact (max_sub_min_eq_abs x y).trans (abs_sub_comm y x)

theorem integral_weighted_thresholdDifference_sq {ι : Type*} (s : Finset ι)
    (x y w : ι → ℝ) :
    (∫ t, ∑ i ∈ s, w i * thresholdDifference (x i) (y i) t ^ 2) =
      ∑ i ∈ s, w i * |x i - y i| := by
  rw [integral_finsetSum s (fun i _ => (thresholdDifference_sq_integrable (x i) (y i)).const_mul _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul,integral_thresholdDifference_sq]

theorem weighted_threshold_energy_le {ι : Type*} (s : Finset ι)
    (x y w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∫ t, ∑ i ∈ s, w i * thresholdDifference (x i) (y i) t ^ 2) ≤
      Real.sqrt (∑ i ∈ s, w i * (x i - y i) ^ 2) * Real.sqrt (∑ i ∈ s, w i) := by
  rw [integral_weighted_thresholdDifference_sq]
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s
    (fun i => Real.sqrt (w i) * |x i-y i|) (fun i => Real.sqrt (w i))
  have hleft (i : ι) (hi : i ∈ s) :
      (Real.sqrt (w i) * |x i-y i|) * Real.sqrt (w i) = w i * |x i-y i| := by
    calc
      _ = Real.sqrt (w i) ^ 2 * |x i-y i| := by ring
      _ = _ := by rw [Real.sq_sqrt (hw i hi)]
  have hsq (i : ι) (hi : i ∈ s) :
      (Real.sqrt (w i) * |x i-y i|) ^ 2 = w i * (x i-y i) ^ 2 := by
    rw [mul_pow,Real.sq_sqrt (hw i hi),sq_abs]
  have hw' : (∑ i ∈ s, Real.sqrt (w i) ^ 2) = ∑ i ∈ s, w i :=
    Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (hw i hi))
  rw [Finset.sum_congr rfl hleft,Finset.sum_congr rfl hsq,hw'] at hcs
  exact hcs

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteThresholdProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Projection-valued threshold cuts of finite spectral sums -/

namespace KadisonKastler

open Finset MeasureTheory
open scoped BigOperators

noncomputable section

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [Fintype κ]

theorem finiteThresholdProjection_gap_energy
    (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i)) (hQ : ∀ j, IsStarProjection (Q j))
    (hPo : ∀ i k, i ≠ k → P i * P k = 0)
    (hQo : ∀ j l, j ≠ l → Q j * Q l = 0)
    (hPt : ∑ i, P i = 1) (hQt : ∑ j, Q j = 1)
    (hc : ∀ i j, Commute (P i) (Q j)) (c : ι → ℝ) (d : κ → ℝ) (t : ℝ) (ξ : H) :
    ‖(finiteThresholdProjection P c t - finiteThresholdProjection Q d t) ξ‖ ^ 2 =
      ∑ a : ι × κ, ‖(P a.1 * Q a.2) ξ‖ ^ 2 *
        thresholdDifference (c a.1) (d a.2) t ^ 2 := by
  rw [finiteThresholdProjection,finiteThresholdProjection,
    jointProjection_gap_energy P Q hP hQ hPo hQo hPt hQt hc]
  apply Finset.sum_congr rfl
  intro a _
  have he : ‖((if t < c a.1 then 1 else 0 : ℝ) : ℂ) -
      ((if t < d a.2 then 1 else 0 : ℝ) : ℂ)‖ ^ 2 =
      thresholdDifference (c a.1) (d a.2) t ^ 2 := by
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    rfl
  rw [he,mul_comm]

theorem finiteThresholdProjection_integrated_energy
    (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i)) (hQ : ∀ j, IsStarProjection (Q j))
    (hPo : ∀ i k, i ≠ k → P i * P k = 0)
    (hQo : ∀ j l, j ≠ l → Q j * Q l = 0)
    (hPt : ∑ i, P i = 1) (hQt : ∑ j, Q j = 1)
    (hc : ∀ i j, Commute (P i) (Q j)) (c : ι → ℝ) (d : κ → ℝ) (ξ : H) :
    (∫ t, ‖(finiteThresholdProjection P c t - finiteThresholdProjection Q d t) ξ‖ ^ 2) =
      ∑ a : ι × κ, ‖(P a.1 * Q a.2) ξ‖ ^ 2 * |c a.1-d a.2| := by
  simp_rw [finiteThresholdProjection_gap_energy P Q hP hQ hPo hQo hPt hQt hc]
  exact integral_weighted_thresholdDifference_sq univ _ _ _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteThresholdEstimate
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Upper and lower energy bounds for finite spectral threshold cuts -/

namespace KadisonKastler

open Finset MeasureTheory
open scoped BigOperators

noncomputable section

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [Fintype κ]
  (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
  (hP : ∀ i, IsStarProjection (P i)) (hQ : ∀ j, IsStarProjection (Q j))
  (hPo : ∀ i k, i ≠ k → P i * P k = 0)
  (hQo : ∀ j l, j ≠ l → Q j * Q l = 0)
  (hPt : ∑ i, P i = 1) (hQt : ∑ j, Q j = 1)
  (hc : ∀ i j, Commute (P i) (Q j))

include hP hQ hPo hQo hPt hQt hc

theorem jointProjection_vector_mass (ξ : H) :
    (∑ a : ι × κ, ‖(P a.1 * Q a.2) ξ‖ ^ 2) = ‖ξ‖ ^ 2 := by
  have he := norm_jointProjection_weighted_sum_sq P Q hP hQ hPo hQo hc (fun _ => 1) ξ
  simpa only [one_smul,jointProjection_total P Q hPt hQt,one_apply_eq_self,
    norm_one,one_pow,one_mul] using he.symm

theorem jointProjection_real_gap (c : ι → ℝ) (d : κ → ℝ) (ξ : H) :
    (∑ a : ι × κ, ‖(P a.1 * Q a.2) ξ‖ ^ 2 * (c a.1-d a.2) ^ 2) =
      ‖((∑ i, (c i : ℂ) • P i) - (∑ j, (d j : ℂ) • Q j)) ξ‖ ^ 2 := by
  have he := jointProjection_gap_energy P Q hP hQ hPo hQo hPt hQt hc
    (fun i => (c i : ℂ)) (fun j => (d j : ℂ)) ξ
  rw [he]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_comm]

theorem finiteThresholdProjection_integral_le (c : ι → ℝ) (d : κ → ℝ) (ξ : H) :
    (∫ t, ‖(finiteThresholdProjection P c t - finiteThresholdProjection Q d t) ξ‖ ^ 2) ≤
      ‖((∑ i, (c i : ℂ) • P i) - (∑ j, (d j : ℂ) • Q j)) ξ‖ * ‖ξ‖ := by
  rw [finiteThresholdProjection_integrated_energy P Q hP hQ hPo hQo hPt hQt hc]
  have he := weighted_threshold_energy_le (univ : Finset (ι × κ))
    (fun a => c a.1) (fun a => d a.2) (fun a => ‖(P a.1 * Q a.2) ξ‖ ^ 2)
    (fun _ _ => sq_nonneg _)
  rw [integral_weighted_thresholdDifference_sq,
    jointProjection_real_gap P Q hP hQ hPo hQo hPt hQt hc,
    jointProjection_vector_mass P Q hP hQ hPo hQo hPt hQt hc] at he
  simpa only [Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)] using he

theorem finiteThresholdProjection_integral_lower (c : ι → ℝ) (d : κ → ℝ) (ξ : H)
    (hrange : ∀ i j, |c i-d j| ≤ 2) :
    ‖((∑ i, (c i : ℂ) • P i) - (∑ j, (d j : ℂ) • Q j)) ξ‖ ^ 2 ≤
      2 * (∫ t, ‖(finiteThresholdProjection P c t - finiteThresholdProjection Q d t) ξ‖ ^ 2) := by
  rw [finiteThresholdProjection_integrated_energy P Q hP hQ hPo hQo hPt hQt hc,
    ← jointProjection_real_gap P Q hP hQ hPo hQo hPt hQt hc,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have h := mul_le_mul_of_nonneg_right (hrange a.1 a.2) (abs_nonneg (c a.1-d a.2))
  rw [← sq, sq_abs] at h
  nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg ‖(P a.1 * Q a.2) ξ‖)]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConjugateFiniteThreshold
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite spectral cuts and the conjugate right action -/

namespace KadisonKastler

open Generator Generator.Tracial Finset
open scoped BigOperators

noncomputable section

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι]

omit [CompleteSpace H] [Fintype ι] in
theorem conjugationOperator_finsetSum (J : H ≃ₗᵢ⋆[ℂ] H)
    (s : Finset ι) (P : ι → H →L[ℂ] H) :
    conjugationOperator J (∑ i ∈ s, P i) = ∑ i ∈ s, conjugationOperator J (P i) := by
  ext ξ
  simp only [conjugationOperator_apply,_root_.sum_apply,map_sum]

omit [CompleteSpace H] in
theorem conjugationOperator_real_sum (J : H ≃ₗᵢ⋆[ℂ] H)
    (P : ι → H →L[ℂ] H) (c : ι → ℝ) :
    conjugationOperator J (∑ i, (c i : ℂ) • P i) =
      ∑ i, (c i : ℂ) • conjugationOperator J (P i) := by
  rw [conjugationOperator_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [conjugationOperator_smul]
  simp only [Complex.star_def,Complex.conj_ofReal]

omit [CompleteSpace H] in
theorem conjugationOperator_finiteThreshold (J : H ≃ₗᵢ⋆[ℂ] H)
    (P : ι → H →L[ℂ] H) (c : ι → ℝ) (t : ℝ) :
    conjugationOperator J (finiteThresholdProjection P c t) =
      finiteThresholdProjection (fun i => conjugationOperator J (P i)) c t :=
  conjugationOperator_real_sum J P _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionNormDecomposition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Squared-norm decompositions for nested projections -/

namespace KadisonKastler

open scoped InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem projection_complement_inner {P : H →L[ℂ] H} (hP : IsStarProjection P) (x : H) :
    inner ℂ (P x) ((1 - P) x) = 0 := by
  have hs : P.adjoint = P := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using hP.isSelfAdjoint.star_eq
  have hz : P * (1 - P) = 0 := by
    rw [mul_sub, mul_one, hP.isIdempotentElem.eq, sub_self]
  rw [← P.adjoint_inner_right, hs]
  change inner ℂ x ((P * (1 - P)) x) = 0
  rw [hz, zero_apply, inner_zero_right]

theorem projection_norm_sq_decomposition {P : H →L[ℂ] H}
    (hP : IsStarProjection P) (x : H) :
    ‖P x‖ ^ 2 + ‖(1 - P) x‖ ^ 2 = ‖x‖ ^ 2 := by
  calc
    _ = ‖P x + (1 - P) x‖ ^ 2 := by
      simpa only [pow_two] using
        (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
          (projection_complement_inner hP x)).symm
    _ = ‖x‖ ^ 2 := by simp

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionCommutatorEnergy
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The energy removed by a two-sided projection cut

For commuting left and right projections, the diagonal cut is an
orthogonal projection. Its discarded squared norm is exactly the
squared norm of their difference acting on the vector.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem pairedProjectionCut_isProjection {p q : H →L[ℂ] H}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hc : Commute p q) :
    IsStarProjection (pairedProjectionCut p q) := by
  have hc₁ : Commute (1 - p) q := (Commute.one_left q).sub_left hc
  have hc₂ : Commute (1 - p) (1 - q) := (Commute.one_right _).sub_right hc₁
  apply (hp.mul hq hc).add (hp.one_sub.mul hq.one_sub hc₂)
  calc
    (p * q) * ((1 - p) * (1 - q)) =
        p * (q * (1 - p)) * (1 - q) := by simp only [mul_assoc]
    _ = (p * (1 - p)) * (q * (1 - q)) := by rw [← hc₁.eq]; simp only [mul_assoc]
    _ = 0 := by rw [hp.mul_one_sub_self,zero_mul]

theorem pairedProjectionCut_complement {p q : H →L[ℂ] H}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hc : Commute p q) :
    (p - q) * (p - q) = 1 - pairedProjectionCut p q := by
  simp only [pairedProjectionCut,mul_sub,sub_mul,mul_one,one_mul,
    hp.isIdempotentElem.eq,hq.isIdempotentElem.eq,← hc.eq]
  abel

theorem pairedProjectionCut_discarded_norm {p q : H →L[ℂ] H}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hc : Commute p q) (ξ : H) :
    ‖(1 - pairedProjectionCut p q) ξ‖ = ‖(p - q) ξ‖ := by
  let C := 1 - pairedProjectionCut p q
  let D := p - q
  have hC : IsStarProjection C := (pairedProjectionCut_isProjection hp hq hc).one_sub
  have hD : IsSelfAdjoint D := hp.isSelfAdjoint.sub hq.isSelfAdjoint
  have hsC : C.adjoint = C := hC.isSelfAdjoint.star_eq
  have hsD : D.adjoint = D := hD.star_eq
  have hsq : ‖C ξ‖ ^ 2 = ‖D ξ‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ),norm_sq_eq_re_inner (𝕜 := ℂ),← C.adjoint_inner_right,
      ← D.adjoint_inner_right,hsC,hsD]
    change (inner ℂ ξ ((C * C) ξ)).re = (inner ℂ ξ ((D * D) ξ)).re
    rw [hC.isIdempotentElem.eq]
    exact congrArg (fun T : H →L[ℂ] H => (inner ℂ ξ (T ξ)).re)
      (pairedProjectionCut_complement hp hq hc).symm
  change ‖C ξ‖ = ‖D ξ‖
  nlinarith [norm_nonneg (C ξ),norm_nonneg (D ξ)]

theorem pairedProjectionCut_energy {p q : H →L[ℂ] H}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hc : Commute p q) (ξ : H) :
    ‖pairedProjectionCut p q ξ‖ ^ 2 + ‖(p - q) ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
  have h := projection_norm_sq_decomposition (pairedProjectionCut_isProjection hp hq hc) ξ
  rwa [pairedProjectionCut_discarded_norm hp hq hc] at h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GoodProjectionCut
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Selecting one projection cut from averaged estimates

A small mean displacement and a strictly larger mean commutator gap
give one cut satisfying both pointwise requirements. This is the scalar
selection step in Haagerup's projection-cut argument.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem exists_good_projection_cut_of_finite_measure [IsFiniteMeasure μ] (f g : X → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hf₀ : ∀ x, 0 ≤ f x) (hg₁ : ∀ x, g x ≤ 1)
    (δ c : ℝ) (hδ : 0 < δ) (hc : 0 < c)
    (hmean : (∫ x, f x ∂μ) < δ * ((∫ x, g x ∂μ) - c * μ.real Set.univ)) :
    ∃ x, f x ≤ δ ∧ c ≤ g x := by
  let h : X → ℝ := fun x => g x - f x / δ - c
  have hint : 0 < ∫ x, h x ∂μ := by
    dsimp [h]
    have hs := integral_sub (hg.sub (hf.div_const δ))
      (integrable_const c : Integrable (fun _ : X => c) μ)
    have ht := integral_sub hg (hf.div_const δ)
    simp only [Pi.sub_apply] at hs ht
    rw [hs,ht,integral_div]
    simp only [integral_const,smul_eq_mul]
    have he : (∫ x, f x ∂μ) / δ < (∫ x, g x ∂μ) - c * μ.real Set.univ :=
      (div_lt_iff₀ hδ).mpr (by nlinarith [hmean])
    nlinarith
  have hex : ∃ x, 0 < h x := by
    by_contra hn
    push Not at hn
    exact (not_le_of_gt hint) (integral_nonpos hn)
  obtain ⟨x,hx⟩ := hex
  change 0 < g x - f x / δ - c at hx
  have hfdiv : 0 ≤ f x / δ := div_nonneg (hf₀ x) hδ.le
  have hfd : f x / δ < 1 := by linarith [hg₁ x]
  exact ⟨x,((div_lt_one hδ).mp hfd).le,by linarith⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RealThresholdSelection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Selecting a spectral threshold in the unit interval

The finite spectral cut functions vanish outside [-1,1]. Their global
energy estimates therefore apply to a finite measure of total mass two.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

theorem exists_good_real_threshold (f g : ℝ → ℝ)
    (hf : Integrable f) (hg : Integrable g)
    (hfs : ∀ t, t ∉ Set.Icc (-1 : ℝ) 1 → f t = 0)
    (hgs : ∀ t, t ∉ Set.Icc (-1 : ℝ) 1 → g t = 0)
    (hf₀ : ∀ t, 0 ≤ f t) (hg₁ : ∀ t, g t ≤ 1)
    (A B δ c : ℝ) (hδ : 0 < δ) (hc : 0 < c)
    (hA : (∫ t, f t) ≤ A) (hB : B ≤ ∫ t, g t)
    (hsmall : A < δ * (B - 2 * c)) :
    ∃ t ∈ Set.Icc (-1 : ℝ) 1, f t ≤ δ ∧ c ≤ g t := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (-1 : ℝ) 1)
  let : IsFiniteMeasure μ := ⟨by
    change volume.restrict (Set.Icc (-1 : ℝ) 1) Set.univ < ⊤
    rw [Measure.restrict_apply_univ,Real.volume_Icc]
    exact ENNReal.ofReal_lt_top⟩
  have hmass : μ.real Set.univ = 2 := by
    change (volume.restrict (Set.Icc (-1 : ℝ) 1)).real Set.univ = 2
    rw [measureReal_restrict_apply_univ,measureReal_def,Real.volume_Icc]
    norm_num
  have hfi : (∫ t, f t ∂μ) = ∫ t, f t :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hfs
  have hgi : (∫ t, g t ∂μ) = ∫ t, g t :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hgs
  have hmean : (∫ t, f t ∂μ) < δ * ((∫ t, g t ∂μ) - c * μ.real Set.univ) := by
    rw [hfi,hgi,hmass]
    nlinarith
  obtain ⟨t,htf,htg⟩ := exists_good_projection_cut_of_finite_measure (μ := μ) f g
    hf.integrableOn hg.integrableOn hf₀ hg₁ δ c hδ hc hmean
  refine ⟨t,?_,htf,htg⟩
  by_contra ht
  rw [hgs t ht] at htg
  exact (not_le_of_gt hc) htg

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteCutSelection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Selecting one finite spectral cut with small displacement and a gap -/

namespace KadisonKastler

open MeasureTheory Finset
open scoped BigOperators

noncomputable section

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [Fintype κ]

omit [CompleteSpace H] in
theorem finiteThresholdProjection_commute
    (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
    (hc : ∀ i j, Commute (P i) (Q j)) (c : ι → ℝ) (d : κ → ℝ) (t : ℝ) :
    Commute (finiteThresholdProjection P c t) (finiteThresholdProjection Q d t) := by
  unfold finiteThresholdProjection
  apply Commute.sum_left
  intro i _
  apply Commute.sum_right
  intro j _
  exact ((hc i j).smul_left _).smul_right _

theorem thresholdDifference_zero_outside {x y t : ℝ}
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) (hy : y ∈ Set.Icc (-1 : ℝ) 1)
    (ht : t ∉ Set.Icc (-1 : ℝ) 1) : thresholdDifference x y t = 0 := by
  by_cases hl : t < -1
  · simp [thresholdDifference,hl.trans_le hx.1,hl.trans_le hy.1]
  · have hr : 1 < t := by
      by_contra h
      exact ht ⟨le_of_not_gt hl,le_of_not_gt h⟩
    simp [thresholdDifference,not_lt.mpr (hx.2.trans hr.le),not_lt.mpr (hy.2.trans hr.le)]

theorem exists_finite_spectral_cut
    (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i)) (hQ : ∀ j, IsStarProjection (Q j))
    (hPo : ∀ i k, i ≠ k → P i * P k = 0)
    (hQo : ∀ j l, j ≠ l → Q j * Q l = 0)
    (hPt : ∑ i, P i = 1) (hQt : ∑ j, Q j = 1)
    (hc : ∀ i j, Commute (P i) (Q j)) (c : ι → ℝ) (d : κ → ℝ)
    (hcr : ∀ i, c i ∈ Set.Icc (-1 : ℝ) 1) (hdr : ∀ j, d j ∈ Set.Icc (-1 : ℝ) 1)
    (ξ η : H) (hη : ‖η‖ = 1) (δ b : ℝ) (hδ : 0 < δ) (hb : 0 < b)
    (hsmall : ‖((∑ i, (c i : ℂ) • P i) - (∑ j, (d j : ℂ) • Q j)) ξ‖ * ‖ξ‖ <
      δ * (‖((∑ i, (c i : ℂ) • P i) - (∑ j, (d j : ℂ) • Q j)) η‖ ^ 2 / 2 - 2 * b)) :
    ∃ t ∈ Set.Icc (-1 : ℝ) 1,
      ‖(finiteThresholdProjection P c t - finiteThresholdProjection Q d t) ξ‖ ^ 2 ≤ δ ∧
      b ≤ ‖(finiteThresholdProjection P c t - finiteThresholdProjection Q d t) η‖ ^ 2 := by
  let f (ζ : H) (t : ℝ) :=
    ‖(finiteThresholdProjection P c t - finiteThresholdProjection Q d t) ζ‖ ^ 2
  have hf (ζ : H) : Integrable (f ζ) := by
    have he (t : ℝ) := finiteThresholdProjection_gap_energy P Q hP hQ hPo hQo hPt hQt hc c d t ζ
    simp_rw [show f ζ = fun t => ∑ a : ι × κ, ‖(P a.1 * Q a.2) ζ‖ ^ 2 *
      thresholdDifference (c a.1) (d a.2) t ^ 2 from funext he]
    exact integrable_finsetSum _ (fun a _ =>
      (thresholdDifference_sq_integrable (c a.1) (d a.2)).const_mul _)
  have hs (ζ : H) (t : ℝ) (ht : t ∉ Set.Icc (-1 : ℝ) 1) : f ζ t = 0 := by
    change ‖(finiteThresholdProjection P c t - finiteThresholdProjection Q d t) ζ‖ ^ 2 = 0
    rw [finiteThresholdProjection_gap_energy P Q hP hQ hPo hQo hPt hQt hc]
    apply Finset.sum_eq_zero
    intro a _
    rw [thresholdDifference_zero_outside (hcr a.1) (hdr a.2) ht]
    ring
  have hbound (t : ℝ) : f η t ≤ 1 := by
    have he := pairedProjectionCut_energy (finiteThresholdProjection_isProjection P hP hPo c t)
      (finiteThresholdProjection_isProjection Q hQ hQo d t)
      (finiteThresholdProjection_commute P Q hc c d t) η
    rw [hη] at he
    change ‖(finiteThresholdProjection P c t - finiteThresholdProjection Q d t) η‖ ^ 2 ≤ 1
    nlinarith [sq_nonneg ‖pairedProjectionCut (finiteThresholdProjection P c t)
      (finiteThresholdProjection Q d t) η‖]
  apply exists_good_real_threshold (f ξ) (f η) (hf ξ) (hf η) (hs ξ) (hs η)
    (fun _ => sq_nonneg _) hbound _ _ δ b hδ hb
    (finiteThresholdProjection_integral_le P Q hP hQ hPo hQo hPt hQt hc c d ξ) _ hsmall
  have hrange (i : ι) (j : κ) : |c i-d j| ≤ 2 := by
    apply abs_le.mpr
    constructor <;> linarith [(hcr i).1,(hcr i).2,(hdr j).1,(hdr j).2]
  have he := finiteThresholdProjection_integral_lower P Q hP hQ hPo hQo hPt hQt hc c d η hrange
  change _ ≤ ∫ t, f η t
  dsimp [f]
  simp only [Complex.coe_smul] at he ⊢
  linarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteAlgebraCutSelection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A genuine algebra projection from the finite spectral cut estimates -/

namespace KadisonKastler

open Generator Generator.Tracial Finset
open scoped BigOperators

noncomputable section

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] {M : VonNeumannAlgebra H}

theorem exists_finite_algebra_projection_cut
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (P : ι → AlgebraProjection M)
    (ho : ∀ i j, i ≠ j → (P i).val * (P j).val = 0)
    (ht : ∑ i, (P i).val = 1) (c : ι → ℝ)
    (hcr : ∀ i, c i ∈ Set.Icc (-1 : ℝ) 1)
    (ξ η : H) (hη : ‖η‖ = 1) (δ b : ℝ) (hδ : 0 < δ) (hb : 0 < b)
    (hsmall : ‖((∑ i, (c i : ℂ) • (P i).val.val) -
        conjugationOperator J (∑ i, (c i : ℂ) • (P i).val.val)) ξ‖ * ‖ξ‖ <
      δ * (‖((∑ i, (c i : ℂ) • (P i).val.val) -
        conjugationOperator J (∑ i, (c i : ℂ) • (P i).val.val)) η‖ ^ 2 / 2 - 2 * b)) :
    ∃ p : AlgebraProjection M,
      ‖(p.val.val - conjugationOperator J p.val.val) ξ‖ ^ 2 ≤ δ ∧
      b ≤ ‖(p.val.val - conjugationOperator J p.val.val) η‖ ^ 2 := by
  let A : ι → H →L[ℂ] H := fun i => (P i).val.val
  let B : ι → H →L[ℂ] H := fun i => conjugationOperator J (A i)
  have hA (i : ι) : IsStarProjection (A i) :=
    (P i).property.map M.toStarSubalgebra.subtype
  have hB (i : ι) : IsStarProjection (B i) :=
    (conjugateAlgebraProjection M M.commutant J hJ hright (P i)).property.map
      M.commutant.toStarSubalgebra.subtype
  have hAo (i j : ι) (hij : i ≠ j) : A i * A j = 0 := congrArg Subtype.val (ho i j hij)
  have hBo (i j : ι) (hij : i ≠ j) : B i * B j = 0 := by
    change conjugationOperator J (A i) * conjugationOperator J (A j) = 0
    rw [← conjugationOperator_mul J hJ,hAo i j hij]
    ext ζ
    simp only [conjugationOperator_apply,zero_apply,map_zero]
  have hAt : (∑ i, A i) = 1 := by
    have he := congrArg M.toStarSubalgebra.subtype ht
    simp only [map_sum,map_one] at he
    change (∑ i, A i) = 1 at he
    exact he
  have hBt : (∑ i, B i) = 1 := by
    have he := congrArg (conjugationOperator J) hAt
    rw [conjugationOperator_finsetSum,conjugationOperator_one J hJ] at he
    exact he
  have hcomm (i j : ι) : Commute (A i) (B j) :=
    VonNeumannAlgebra.mem_commutant_iff.mp (hright (P j).val) (A i) (P i).val.property
  have hsmall' : ‖((∑ i, (c i : ℂ) • A i) - (∑ i, (c i : ℂ) • B i)) ξ‖ * ‖ξ‖ <
      δ * (‖((∑ i, (c i : ℂ) • A i) - (∑ i, (c i : ℂ) • B i)) η‖ ^ 2 / 2 - 2 * b) := by
    simpa only [conjugationOperator_real_sum] using hsmall
  obtain ⟨t,_,hξ,hη'⟩ := exists_finite_spectral_cut A B hA hB hAo hBo hAt hBt hcomm
    c c hcr hcr ξ η hη δ b hδ hb hsmall'
  let T := finiteThresholdProjection A c t
  have hTM : T ∈ M := by
    apply M.toStarSubalgebra.sum_mem
    intro i _
    exact M.toStarSubalgebra.smul_mem (P i).val.property _
  have hT : IsStarProjection T := finiteThresholdProjection_isProjection A hA hAo c t
  let p : AlgebraProjection M := ⟨⟨T,hTM⟩,
    ⟨Subtype.ext hT.isIdempotentElem.eq,Subtype.ext hT.isSelfAdjoint.star_eq⟩⟩
  refine ⟨p,?_,?_⟩
  · change ‖(T - conjugationOperator J T) ξ‖ ^ 2 ≤ δ
    simpa only [T,conjugationOperator_finiteThreshold] using hξ
  · change b ≤ ‖(T - conjugationOperator J T) η‖ ^ 2
    simpa only [T,conjugationOperator_finiteThreshold] using hη'

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SelfAdjointProjectionCut
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A projection cut from an almost-central self-adjoint contraction

Finite spectral approximations preserve the strict energy inequality.
The finite threshold selection then supplies a projection in the original
algebra, with both the reference-vector and test-vector bounds.
-/

namespace KadisonKastler

open Generator Generator.Tracial Filter
open scoped BigOperators Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem exists_selfAdjoint_projection_cut
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (a : Algebra M) (ha : IsSelfAdjoint a) (han : ‖a‖ ≤ 1)
    (ξ η : H) (hη : ‖η‖ = 1) (δ b : ℝ) (hδ : 0 < δ) (hb : 0 < b)
    (hsmall : ‖(a.val - conjugationOperator J a.val) ξ‖ * ‖ξ‖ <
      δ * (‖(a.val - conjugationOperator J a.val) η‖ ^ 2 / 2 - 2 * b)) :
    ∃ p : AlgebraProjection M,
      ‖(p.val.val - conjugationOperator J p.val.val) ξ‖ ^ 2 ≤ δ ∧
      b ≤ ‖(p.val.val - conjugationOperator J p.val.val) η‖ ^ 2 := by
  let F (A : H →L[ℂ] H) := ‖(A - conjugationOperator J A) ξ‖ * ‖ξ‖ -
    δ * (‖(A - conjugationOperator J A) η‖ ^ 2 / 2 - 2 * b)
  have hC : Continuous (conjugationOperator J : (H →L[ℂ] H) → (H →L[ℂ] H)) :=
    (conjugationRealStarAlgEquiv_isometry J hJ).continuous
  have hV (ζ : H) : Continuous (fun A : H →L[ℂ] H => (A - conjugationOperator J A) ζ) :=
    (continuous_id.sub hC).clm_apply continuous_const
  have hF : Continuous F := by
    exact ((hV ξ).norm.mul continuous_const).sub
      (continuous_const.mul (((hV η).norm.pow 2).div_const 2 |>.sub continuous_const))
  have hFa : F a.val < 0 := sub_neg.mpr hsmall
  have hnear : ∀ᶠ A in 𝓝 a.val, F A < 0 := hF.continuousAt.eventually_lt_const hFa
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hnear
  obtain ⟨Q,c,hcr,happrox⟩ := exists_bounded_spectral_approximation a ha han ε hε
  let r : Algebra M := ∑ i, (c i : ℂ) • (Q.piece i).val
  change ‖a-r‖ < ε at happrox
  have hdist : dist r.val a.val < ε := by
    rw [dist_eq_norm,norm_sub_rev]
    exact happrox
  have hs := hball hdist
  have hr : r.val = ∑ i, (c i : ℂ) • (Q.piece i).val.val := by
    change M.toStarSubalgebra.subtype (∑ i, (c i : ℂ) • (Q.piece i).val) = _
    simp only [map_sum,map_smul]
    rfl
  have htotal : (∑ i, (Q.piece i).val) = 1 := Q.total
  apply exists_finite_algebra_projection_cut J hJ hright Q.piece Q.orthogonal htotal c hcr
    ξ η hη δ b hδ hb
  rw [← hr]
  exact sub_neg.mp hs

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CentralDefectSelfAdjoint
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Reducing a central-vector defect to a self-adjoint contraction -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem centralVectorDefect_realPart_le (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (ξ : H) (hξ : J ξ = ξ) (a : H →L[ℂ] H) :
    ‖centralVectorDefect J ξ (realPart a : H →L[ℂ] H)‖ ≤ ‖centralVectorDefect J ξ a‖ := by
  let D := centralVectorDefect J ξ
  change ‖D (realPart a : H →L[ℂ] H)‖ ≤ ‖D a‖
  rw [realPart_apply_coe,D.map_smul_of_tower,map_add,norm_smul]
  rw [show ‖(2 : ℝ)⁻¹‖ = (1 / 2 : ℝ) by norm_num]
  have hstar := centralVectorDefect_star_norm J hJ ξ hξ a
  change ‖D (star a)‖ = ‖D a‖ at hstar
  have hn := norm_add_le (D a) (D (star a))
  nlinarith

theorem centralVectorDefect_imaginaryPart_le (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (ξ : H) (hξ : J ξ = ξ) (a : H →L[ℂ] H) :
    ‖centralVectorDefect J ξ (imaginaryPart a : H →L[ℂ] H)‖ ≤ ‖centralVectorDefect J ξ a‖ := by
  let D := centralVectorDefect J ξ
  change ‖D (imaginaryPart a : H →L[ℂ] H)‖ ≤ ‖D a‖
  rw [imaginaryPart_apply_coe,map_smul,D.map_smul_of_tower,map_sub,norm_smul,norm_smul]
  rw [norm_neg,Complex.norm_I,one_mul,
    show ‖(2 : ℝ)⁻¹‖ = (1 / 2 : ℝ) by norm_num]
  have hstar := centralVectorDefect_star_norm J hJ ξ hξ a
  change ‖D (star a)‖ = ‖D a‖ at hstar
  have hn := norm_sub_le (D a) (D (star a))
  nlinarith

theorem centralVectorDefect_re_im_gap (J : H ≃ₗᵢ⋆[ℂ] H) (η : H) (a : H →L[ℂ] H) :
    ‖centralVectorDefect J η a‖ / 2 ≤
        ‖centralVectorDefect J η (realPart a : H →L[ℂ] H)‖ ∨
      ‖centralVectorDefect J η a‖ / 2 ≤
        ‖centralVectorDefect J η (imaginaryPart a : H →L[ℂ] H)‖ := by
  let D := centralVectorDefect J η
  have he : D a = D (realPart a : H →L[ℂ] H) +
      Complex.I • D (imaginaryPart a : H →L[ℂ] H) := by
    rw [← map_smul,← map_add,realPart_add_I_smul_imaginaryPart]
  have hn := norm_add_le (D (realPart a : H →L[ℂ] H))
    (Complex.I • D (imaginaryPart a : H →L[ℂ] H))
  rw [← he,norm_smul,Complex.norm_I,one_mul] at hn
  change ‖D a‖ / 2 ≤ ‖D (realPart a : H →L[ℂ] H)‖ ∨
    ‖D a‖ / 2 ≤ ‖D (imaginaryPart a : H →L[ℂ] H)‖
  by_contra h
  push Not at h
  linarith [h.1,h.2]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularPositiveReal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The modular conjugation fixes the generated positive cone -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem modularPositiveCone_fixed
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ : H) (hξ : J ξ = ξ) {η : H}
    (hη : η ∈ modularPositiveCone (M := M) J ξ) : J η = η := by
  have hgen (a : Algebra M) : J (modularQuadratic J a ξ) = modularQuadratic J a ξ := by
    have he : J (modularQuadratic J a ξ) =
        conjugationOperator J a.val (a.val ξ) := by
      change J (a.val (J (a.val (J ξ)))) = J (a.val (J (a.val ξ)))
      rw [hξ]
    rw [he]
    exact congrArg (fun T : H →L[ℂ] H => T ξ)
      (VonNeumannAlgebra.mem_commutant_iff.mp (hright a) a.val a.property).symm
  have hh : ConvexCone.hull ℝ (Set.range (fun a : Algebra M => modularQuadratic J a ξ)) ≤
      conjugationFixedCone J := by
    apply ConvexCone.hull_min
    rintro _ ⟨a,rfl⟩
    exact hgen a
  exact closure_minimal (fun _ h => hh h)
    (isClosed_eq J.continuous continuous_id) hη

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SelfAdjointApproximation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Self-adjoint approximation by the algebra and its commutant -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem realPart_mem_vonNeumann (M : VonNeumannAlgebra H) {a : H →L[ℂ] H} (ha : a ∈ M) :
    (realPart a : H →L[ℂ] H) ∈ M := by
  rw [realPart_apply_coe, ← Complex.coe_smul]
  exact M.smul_mem (M.add_mem ha (star_mem (s := M.toStarSubalgebra) ha)) _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SelfAdjointCentralGap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A self-adjoint witness for a central-vector gap

One real or imaginary part retains at least half the test-vector defect.
At a conjugation-fixed reference vector both parts have no larger defect
than the original operator.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem exists_selfAdjoint_central_gap
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (ξ η : H) (hξ : J ξ = ξ) (a : Algebra M) :
    ∃ b : Algebra M, IsSelfAdjoint b ∧ ‖b‖ ≤ ‖a‖ ∧
      ‖centralVectorDefect J ξ b.val‖ ≤ ‖centralVectorDefect J ξ a.val‖ ∧
      ‖centralVectorDefect J η a.val‖ / 2 ≤ ‖centralVectorDefect J η b.val‖ := by
  rcases centralVectorDefect_re_im_gap J η a.val with hr | hi
  · let b : Algebra M := ⟨(realPart a.val : H →L[ℂ] H),realPart_mem_vonNeumann M a.property⟩
    refine ⟨b,?_,?_,centralVectorDefect_realPart_le J hJ ξ hξ a.val,hr⟩
    · exact Subtype.ext (realPart a.val).property.star_eq
    · exact realPart.norm_le a.val
  · have hb : (imaginaryPart a.val : H →L[ℂ] H) ∈ M := by
      rw [imaginaryPart_apply_coe,← Complex.coe_smul (2 : ℝ)⁻¹]
      exact M.smul_mem (M.smul_mem (M.sub_mem a.property (M.star_mem' a.property)) _) _
    let b : Algebra M := ⟨(imaginaryPart a.val : H →L[ℂ] H),hb⟩
    refine ⟨b,?_,?_,centralVectorDefect_imaginaryPart_le J hJ ξ hξ a.val,hi⟩
    · exact Subtype.ext (imaginaryPart a.val).property.star_eq
    · exact imaginaryPart.norm_le a.val

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScaledCentralProjectionCut
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.typeIIIInitialSpaceComplete _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_projectionFamilyCommutationSpace _root_.OAI.KadisonKastler.mem_projectionFamilyRemainderSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_apply _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_symm_apply _root_.OAI.KadisonKastler.tomitaPolarCoordinates_root _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Projection cuts for unnormalized central vectors

The reference vector may be a finite-matrix central projection of a unit
vector, and the test vector may be any nonzero residual. The fixed gap
therefore scales with the squared norm of the residual.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem exists_scaled_projection_gap_of_central_defect
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (ξ η : H) (hξ : ‖ξ‖ ≤ 1) (hη : η ≠ 0) (hJξ : J ξ = ξ)
    (a : Algebra M) (ha : ‖a‖ ≤ 1) (δ : ℝ) (hδ : 0 < δ)
    (hsmall : ‖centralVectorDefect J ξ a.val‖ < δ / 64)
    (hgap : ‖η‖ / 2 ≤ ‖centralVectorDefect J η a.val‖) :
    ∃ p : AlgebraProjection M,
      ‖(p.val.val - conjugationOperator J p.val.val) ξ‖ ^ 2 ≤ δ ∧
      (1 / 128 : ℝ) * ‖η‖ ^ 2 ≤
        ‖(p.val.val - conjugationOperator J p.val.val) η‖ ^ 2 := by
  have hn : 0 < ‖η‖ := norm_pos_iff.mpr hη
  let η₀ : H := ‖η‖⁻¹ • η
  have hn₀ : ‖η₀‖ = 1 := by
    dsimp only [η₀]
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hn.le),inv_mul_cancel₀ hn.ne']
  have hD : ‖centralVectorDefect J η₀ a.val‖ =
      ‖η‖⁻¹ * ‖centralVectorDefect J η a.val‖ := by
    change ‖(a.val - conjugationOperator J (star a.val)) (‖η‖⁻¹ • η)‖ = _
    rw [ContinuousLinearMap.map_smul_of_tower,norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hn.le)]
    rfl
  have hgap₀ : (1 / 2 : ℝ) ≤ ‖centralVectorDefect J η₀ a.val‖ := by
    rw [hD]
    have ht := mul_le_mul_of_nonneg_left hgap (inv_nonneg.mpr hn.le)
    simpa only [← mul_div_assoc,inv_mul_cancel₀ hn.ne',one_div] using ht
  obtain ⟨b,hbs,hbn,hbsmall,hbgap⟩ := exists_selfAdjoint_central_gap J hJ ξ η₀ hJξ a
  have hbstar : star b.val = b.val := congrArg Subtype.val hbs.star_eq
  have hbe (ζ : H) : centralVectorDefect J ζ b.val =
      (b.val - conjugationOperator J b.val) ζ := by
    rw [centralVectorDefect_apply,hbstar]
    rfl
  rw [hbe] at hbsmall hbgap
  have hbref : ‖(b.val - conjugationOperator J b.val) ξ‖ * ‖ξ‖ < δ / 64 :=
    (mul_le_of_le_one_right (norm_nonneg _) hξ).trans_lt (hbsmall.trans_lt hsmall)
  have hbtest : (1 / 4 : ℝ) ≤ ‖(b.val - conjugationOperator J b.val) η₀‖ := by
    linarith
  have henergy : ‖(b.val - conjugationOperator J b.val) ξ‖ * ‖ξ‖ <
      δ * (‖(b.val - conjugationOperator J b.val) η₀‖ ^ 2 / 2 - 2 * (1/128:ℝ)) := by
    have ht : (1/64:ℝ) ≤ ‖(b.val - conjugationOperator J b.val) η₀‖ ^ 2 / 2 -
        2 * (1/128:ℝ) := by nlinarith
    have hm := mul_le_mul_of_nonneg_left ht hδ.le
    nlinarith
  obtain ⟨p,hpref,hptest⟩ := exists_selfAdjoint_projection_cut J hJ hright b hbs
    (hbn.trans ha) ξ η₀ hn₀ δ (1/128) hδ (by norm_num) henergy
  refine ⟨p,hpref,?_⟩
  have he : ‖(p.val.val - conjugationOperator J p.val.val) η₀‖ =
      ‖η‖⁻¹ * ‖(p.val.val - conjugationOperator J p.val.val) η‖ := by
    dsimp only [η₀]
    rw [ContinuousLinearMap.map_smul_of_tower,norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hn.le)]
  rw [he,mul_pow] at hptest
  have hm := mul_le_mul_of_nonneg_right hptest (sq_nonneg ‖η‖)
  have hi : ‖η‖⁻¹ ^ 2 * ‖η‖ ^ 2 = 1 := by
    rw [← mul_pow,inv_mul_cancel₀ hn.ne',one_pow]
  calc
    (1/128:ℝ) * ‖η‖ ^ 2 ≤
        (‖η‖⁻¹ ^ 2 * ‖(p.val.val - conjugationOperator J p.val.val) η‖ ^ 2) * ‖η‖ ^ 2 := hm
    _ = ‖(p.val.val - conjugationOperator J p.val.val) η‖ ^ 2 := by
      calc
        _ = (‖η‖⁻¹ ^ 2 * ‖η‖ ^ 2) *
            ‖(p.val.val - conjugationOperator J p.val.val) η‖ ^ 2 := by ring
        _ = _ := by rw [hi,one_mul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RelativeUnitaryStateDefect
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # State commutator bounds in a finite-matrix relative commutant

The relative Powers–Størmer estimate supplies the unitary defect bound
on the central-vector space, without treating the relative algebra as
cyclic on the full ambient Hilbert space.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
theorem relative_conjugation_mem_commutant (E : MatrixUnitSystem ι (Algebra M))
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (a : Algebra E.relativeVonNeumann) :
    conjugationOperator J a.val ∈ E.relativeVonNeumann.commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro T hT
  exact VonNeumannAlgebra.mem_commutant_iff.mp
    (hright ⟨a.val,E.relativeVonNeumann_le a.property⟩) T (E.relativeVonNeumann_le hT)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RelativeBicentralizerGap
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bicentralizer projection gaps in the matrix relative algebra

The residual vector is approximated only in the central-vector space.
The original positive cone supplies the relative state-to-vector bound.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

attribute [local instance] OAI.KadisonKastler.relativeBicentralizerRealInner
theorem exists_relative_projection_residual_gap_oai
    (E : MatrixUnitSystem ι (Algebra M))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hleft : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ=ξ) (hcyc : DenseRange (algebraVectorMap M ξ))
    (hpos : ∀ a : Algebra M, 0 ≤ inner ℝ ξ (modularQuadratic J a ξ))
    (ζ : H) (hζ : ζ ∈ modularPositiveCone (M := M) J ξ) (hunit : ‖ζ‖=1)
    (hsep : Function.Injective (algebraVectorMap M ζ))
    (hζE : ζ ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J)
    (hscalar : ∀ b : Algebra E.relativeVonNeumann, stateBicentralizerMember ζ b →
      ∃ z : ℂ, b=z • 1)
    (η : H) (hη : η≠0) (hηE : η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J)
    (horth : inner ℂ ζ η=0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ p : AlgebraProjection E.relativeVonNeumann,
      ‖(p.val.val-conjugationOperator J p.val.val) ζ‖^2 ≤ δ ∧
      (1/128:ℝ)*‖η‖^2 ≤ ‖(p.val.val-conjugationOperator J p.val.val) η‖^2 := by
  obtain ⟨u,huref,hures⟩ := exists_relative_unitary_residual_gap E J hJ hright hleft
    ξ hξ hcyc hpos ζ hζ hunit hsep hζE hscalar η hη hηE horth (δ/64) (by positivity)
  exact exists_scaled_projection_gap_of_central_defect J hJ
    (relative_conjugation_mem_commutant E J hright) ζ η (by rw [hunit]) hη
    (modularPositiveCone_fixed J hright ξ hξ hζ) u.val (norm_unitary_le_one u)
    δ hδ huref hures

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.exists_relative_projection_residual_gap_oai.{u_1, u_2} := @OAI.KadisonKastler.exists_relative_projection_residual_gap_oai.{u_1, u_2}
