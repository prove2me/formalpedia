-- Prove2me | solution 1 for OAI.KadisonKastler.coreTraceEmbedding_vector_symmetry
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T21:23:42.552525+00:00
-- url     : https://prove2.me/submissions/6d515173-7cad-445d-8735-10c81cea9a4e

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Interval.Set.Group
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
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
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
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
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
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
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.Probability.Moments.ComplexMGF
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
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Bases
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K046
import Theorems.Thm_OAI_KadisonKastler_cyclicRootScalarBalance
import Theorems.Thm_OAI_KadisonKastler_regularCoreEmbedding_symmetry_of_balance

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConstructedCoreConjugation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The constructed modular core has an explicit commutant conjugation -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {M : VonNeumannAlgebra H} (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem modularStrongGroup_polar_commutes (t : Multiplicative ℝ) (x : H) :
    tomitaPolarConjugation J Ω hsep hcyc
      ((modularStrongGroup J Ω hsep hcyc t : H →L[ℂ] H) x) =
    (modularStrongGroup J Ω hsep hcyc t : H →L[ℂ] H)
      (tomitaPolarConjugation J Ω hsep hcyc x) := by
  have h := congrArg (fun A : H →L[ℂ] H => A (tomitaPolarConjugation J Ω hsep hcyc x))
    (modularStrongGroup_polar_conjugation J Ω hsep hcyc t.toAdd)
  simpa only [conjugationOperator_apply, ofAdd_toAdd,
    tomitaPolarConjugation_involutive J Ω hsep hcyc x] using h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreTraceTomitaCoordinates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Common spectral coordinates for the two trace-boundary vectors

The algebra vector and its conjugate adjoint use square-root weights
in one cyclic resolvent model. These coordinates let the clipped
exponential translation law be applied to both sides of a monomial.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

omit [TopologicalSpace.SeparableSpace H] in
theorem coreTraceLeftCoordinate_embedding (a : Algebra M) :
    modularCyclicEmbedding J Ω (tomitaCoreCoordinate J Ω hsep hcyc a)
      (coreTraceLeftCoordinate J Ω hsep hcyc a) = a.val Ω := by
  change resolventCyclicIsometry (graphResolvent M J Ω 1)
    (graphResolvent_positive J Ω 1).isSelfAdjoint _
      (ContinuousMap.toLp 2 _ ℂ (resolventSqrtFunction _)) = _
  rw [resolventCyclicIsometry_continuous,
    resolventContinuousCalculus_sqrt _ _
      ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr (graphResolvent_positive J Ω 1))]
  exact tomitaCoreCoordinate_first J Ω hsep hcyc a

omit [TopologicalSpace.SeparableSpace H] in
theorem coreTraceRightCoordinate_embedding (a : Algebra M) :
    modularCyclicEmbedding J Ω (tomitaCoreCoordinate J Ω hsep hcyc a)
      (coreTraceRightCoordinate J Ω hsep hcyc a) =
      tomitaPolarConjugation J Ω hsep hcyc (star a.val Ω) := by
  have hq : 0 ≤ 1 - graphResolvent M J Ω 1 := by
    rw [← tomitaGraphComplementRoot_square J Ω hsep hcyc]
    have hs := (tomitaGraphComplementRoot_nonneg (M := M) J Ω).isSelfAdjoint
    simpa only [hs.star_eq] using
      (star_mul_self_nonneg (tomitaGraphComplementRoot (M := M) J Ω))
  change resolventCyclicIsometry (graphResolvent M J Ω 1)
    (graphResolvent_positive J Ω 1).isSelfAdjoint _
      (ContinuousMap.toLp 2 _ ℂ (resolventComplementSqrtFunction _)) = _
  rw [resolventCyclicIsometry_continuous, resolventContinuousCalculus_complement_sqrt _ _ hq]
  exact tomitaCoreCoordinate_complement J Ω hsep hcyc a

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreTraceScalarGauge
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Trace balance between the two scalar gauge actions -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem fourier_frequencyWindow (a b : ℝ) (f : RegularCoreHilbert H) :
    (𝓕 (regularFrequencyWindow a b f) : RegularCoreHilbert H) =
      regularIndicatorProjection (Set.Ioc a b) measurableSet_Ioc (𝓕 f) := by
  unfold regularFrequencyWindow
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm]
  exact (Lp.fourierTransformₗᵢ ℝ H).apply_symm_apply _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarGaugeWindowBalance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Scalar-field and gauge lifting of the finite-window trace identity -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularFrequencyWindow_tensor (a b : ℝ)
    (f : Lp ℂ 2 (volume : Measure ℝ)) (v : H) :
    regularFrequencyWindow a b (scalarLpTensor volume f v) =
      scalarLpTensor volume (regularFrequencyWindow a b f) v := by
  apply (Lp.fourierTransformₗᵢ ℝ H).injective
  change (𝓕 (regularFrequencyWindow a b (scalarLpTensor volume f v)) :
    RegularCoreHilbert H) = 𝓕 (scalarLpTensor volume (regularFrequencyWindow a b f) v)
  rw [fourier_frequencyWindow, fourier_scalarLpTensor,
    fourier_scalarLpTensor, fourier_frequencyWindow]
  exact regularIndicatorProjection_tensor (Set.Ioc a b) measurableSet_Ioc (𝓕 f) v

theorem l2ScalarSwap_frequencyWindow {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (a b : ℝ) (F : RegularCoreHilbert (Lp ℂ 2 μ)) :
    l2ScalarSwap volume μ (regularFrequencyWindow a b F) =
      (regularFrequencyWindow (H := ℂ) a b).compLp (l2ScalarSwap volume μ F) := by
  apply l2ScalarSwap_intertwines_of_tensor volume μ
    (regularFrequencyWindow a b) ((regularFrequencyWindow (H := ℂ) a b).compLpL 2 μ)
  intro f v
  rw [regularFrequencyWindow_tensor, l2ScalarSwap_tensor]
  exact (compLp_scalarLpTensor μ (regularFrequencyWindow (H := ℂ) a b) v f).symm

theorem characterField_window_balance {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (l : X → ℝ) (hl : Measurable l)
    (f : RegularCoreHilbert ℂ) (v w : Lp ℂ 2 μ)
    (hbalance : ∀ᵐ s ∂μ,
      v s • regularFrequencyWindow 0 1
        ((star (regularCharacterUnitary (H := ℂ) (l s)) :
          RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) f) =
      w s • (star (regularCharacterUnitary (H := ℂ) (l s)) :
        RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ)
        (regularFrequencyWindow 0 1
          ((regularCharacterUnitary (H := ℂ) (l s) :
            RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) f))) :
    let E := Lp (RegularCoreHilbert ℂ) 2 μ
    let C : E →L[ℂ] E := characterField μ l hl
    let Cs : E →L[ℂ] E := star (characterField μ l hl)
    let P := regularFrequencyWindow (H := ℂ) 0 1
    P.compLp (Cs (scalarLpTensor μ v f)) =
      Cs (P.compLp (C (scalarLpTensor μ w f))) := by
  let C : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 μ :=
    characterField μ l hl
  let Cs : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ] Lp (RegularCoreHilbert ℂ) 2 μ :=
    star (characterField μ l hl)
  let P := regularFrequencyWindow (H := ℂ) 0 1
  have hstar (F : Lp (RegularCoreHilbert ℂ) 2 μ) :=
    regularUnitaryField_star_apply_ae μ (fun s => regularCharacterUnitary (H := ℂ) (l s))
      (characterField_measurable μ l hl) (characterField_star_measurable μ l hl) F
  apply Lp.ext
  filter_upwards [P.coeFn_compLp (Cs (scalarLpTensor μ v f)),
    hstar (scalarLpTensor μ v f), scalarLpTensor_apply_ae μ v f,
    hstar (P.compLp (C (scalarLpTensor μ w f))),
    P.coeFn_compLp (C (scalarLpTensor μ w f)),
    characterField_apply_ae μ l hl (scalarLpTensor μ w f),
    scalarLpTensor_apply_ae μ w f, hbalance]
    with s hp hcl hv hcr hpr hc hw hb
  change (Cs (scalarLpTensor μ v f)) s = _ at hcl
  change (Cs (P.compLp (C (scalarLpTensor μ w f)))) s = _ at hcr
  change (P.compLp (Cs (scalarLpTensor μ v f))) s =
    (Cs (P.compLp (C (scalarLpTensor μ w f)))) s
  rw [hp, hcl, hv, hcr, hpr, hc, hw]
  simpa only [map_smul] using hb


theorem scalarGaugeWindowBalance {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (l : X → ℝ) (hl : Measurable l)
    (G : unitary (RegularCoreHilbert (Lp ℂ 2 μ) →L[ℂ] RegularCoreHilbert (Lp ℂ 2 μ)))
    (hG : ∀ F, l2ScalarSwap volume μ ((G :
      RegularCoreHilbert (Lp ℂ 2 μ) →L[ℂ] RegularCoreHilbert (Lp ℂ 2 μ)) F) =
      (characterField μ l hl : Lp (RegularCoreHilbert ℂ) 2 μ →L[ℂ]
        Lp (RegularCoreHilbert ℂ) 2 μ) (l2ScalarSwap volume μ F))
    (f : RegularCoreHilbert ℂ) (v w : Lp ℂ 2 μ)
    (hbalance : ∀ᵐ s ∂μ,
      v s • regularFrequencyWindow 0 1
        ((star (regularCharacterUnitary (H := ℂ) (l s)) :
          RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) f) =
      w s • (star (regularCharacterUnitary (H := ℂ) (l s)) :
        RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ)
        (regularFrequencyWindow 0 1
          ((regularCharacterUnitary (H := ℂ) (l s) :
            RegularCoreHilbert ℂ →L[ℂ] RegularCoreHilbert ℂ) f))) :
    regularFrequencyWindow 0 1
      ((star G : RegularCoreHilbert (Lp ℂ 2 μ) →L[ℂ] RegularCoreHilbert (Lp ℂ 2 μ))
        (scalarLpTensor volume f v)) =
      (star G : RegularCoreHilbert (Lp ℂ 2 μ) →L[ℂ] RegularCoreHilbert (Lp ℂ 2 μ))
        (regularFrequencyWindow 0 1
          ((G : RegularCoreHilbert (Lp ℂ 2 μ) →L[ℂ] RegularCoreHilbert (Lp ℂ 2 μ))
            (scalarLpTensor volume f w))) := by
  let E := RegularCoreHilbert (Lp ℂ 2 μ)
  let F := Lp (RegularCoreHilbert ℂ) 2 μ
  let S := l2ScalarSwap (volume : Measure ℝ) μ
  let C : F →L[ℂ] F := characterField μ l hl
  let Cs : F →L[ℂ] F := star (characterField μ l hl)
  let P := regularFrequencyWindow (H := ℂ) 0 1
  have hs (u : E) : S ((star G : E →L[ℂ] E) u) = Cs (S u) := by
    exact intertwines_unitary_star S.toContinuousLinearEquiv.toContinuousLinearMap
      G (characterField μ l hl) hG u
  have hleft : S (regularFrequencyWindow 0 1
      ((star G : E →L[ℂ] E) (scalarLpTensor volume f v))) =
      P.compLp (Cs (scalarLpTensor μ v f)) := by
    calc
      _ = P.compLp (S ((star G : E →L[ℂ] E) (scalarLpTensor volume f v))) :=
        l2ScalarSwap_frequencyWindow μ 0 1 _
      _ = P.compLp (Cs (S (scalarLpTensor volume f v))) := congrArg P.compLp (hs _)
      _ = _ := congrArg (fun z => P.compLp (Cs z)) (l2ScalarSwap_tensor volume μ f v)
  have hright : S ((star G : E →L[ℂ] E)
      (regularFrequencyWindow 0 1 ((G : E →L[ℂ] E) (scalarLpTensor volume f w)))) =
      Cs (P.compLp (C (scalarLpTensor μ w f))) := by
    calc
      _ = Cs (S (regularFrequencyWindow 0 1
          ((G : E →L[ℂ] E) (scalarLpTensor volume f w)))) := hs _
      _ = Cs (P.compLp (S ((G : E →L[ℂ] E) (scalarLpTensor volume f w)))) :=
        congrArg Cs (l2ScalarSwap_frequencyWindow μ 0 1 _)
      _ = Cs (P.compLp (C (S (scalarLpTensor volume f w)))) :=
        congrArg (fun z => Cs (P.compLp z)) (hG _)
      _ = _ := congrArg (fun z => Cs (P.compLp (C z))) (l2ScalarSwap_tensor volume μ f w)
  apply S.injective
  exact hleft.trans ((characterField_window_balance μ l hl f v w hbalance).trans hright.symm)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CyclicSqrtGaugeBalance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The two square-root spectral weights in a cyclic gauge model -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω)) (x : H)

theorem cyclicSqrtGaugeBalance :
    let E := ModularCyclicSpace M J Ω x
    let G : unitary (RegularCoreHilbert E →L[ℂ] RegularCoreHilbert E) :=
      modularCyclicGauge J Ω hsep hcyc x
    let f := (Lp.fourierTransformₗᵢ ℝ ℂ).symm coreTraceFrequencyScalar
    regularFrequencyWindow 0 1
      ((star G : RegularCoreHilbert E →L[ℂ] RegularCoreHilbert E)
        (scalarLpTensor volume f (cyclicLeftRootVector (M := M) J Ω x))) =
      (star G : RegularCoreHilbert E →L[ℂ] RegularCoreHilbert E)
        (regularFrequencyWindow 0 1
          ((G : RegularCoreHilbert E →L[ℂ] RegularCoreHilbert E)
            (scalarLpTensor volume f (cyclicRightRootVector (M := M) J Ω x)))) := by
  have h := scalarGaugeWindowBalance (modularCyclicMeasure (M := M) J Ω x)
    (fun s => resolventLogFrequency s.val)
    (resolventLogFrequency_measurable.comp measurable_subtype_coe)
    (modularCyclicGauge J Ω hsep hcyc x) (cyclicGauge_swap J Ω hsep hcyc x)
    ((Lp.fourierTransformₗᵢ ℝ ℂ).symm coreTraceFrequencyScalar)
    (cyclicLeftRootVector (M := M) J Ω x) (cyclicRightRootVector (M := M) J Ω x)
    (cyclicRootScalarBalance J Ω hsep hcyc x)
  exact h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularActionPackets
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spectral action on the packets of an invariant vector -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularFrequencyPacket_eq_tensor (φ : Lp ℂ 2 (volume : Measure ℝ)) (x : H) :
    regularFrequencyPacket φ x =
      regularTensorVector ((Lp.fourierTransformₗᵢ ℝ ℂ).symm φ) x := by
  apply (Lp.fourierTransformₗᵢ ℝ H).injective
  rw [regularFrequencyPacket, LinearIsometryEquiv.apply_symm_apply,
    fourier_regularTensorVector, LinearIsometryEquiv.apply_symm_apply]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FrequencyPacketTensor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Agreement of the two concrete elementary-tensor constructions -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem regularTensorVector_eq_scalarLpTensor
    (f : Lp ℂ 2 (volume : Measure ℝ)) (v : H) :
    regularTensorVector f v = scalarLpTensor volume f v := by
  apply Lp.ext
  filter_upwards [regularTensorVector_apply_ae f v,
    scalarLpTensor_apply_ae volume f v] with t ht hs
  exact ht.trans hs.symm

theorem regularFrequencyPacket_eq_scalarLpTensor
    (f : Lp ℂ 2 (volume : Measure ℝ)) (v : H) :
    regularFrequencyPacket f v =
      scalarLpTensor volume ((Lp.fourierTransformₗᵢ ℝ ℂ).symm f) v :=
  (regularFrequencyPacket_eq_tensor f v).trans (regularTensorVector_eq_scalarLpTensor _ v)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GaugeWindowTransport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Transport of a frequency-window identity along a group intertwiner -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem compLp_regularFrequencyWindow (L : H →L[ℂ] K) (a b : ℝ)
    (f : RegularCoreHilbert H) :
    L.compLp (regularFrequencyWindow a b f) =
      regularFrequencyWindow a b (L.compLp f) := by
  apply (Lp.fourierTransformₗᵢ ℝ K).injective
  change (𝓕 (L.compLp (regularFrequencyWindow a b f)) : RegularCoreHilbert K) =
    𝓕 (regularFrequencyWindow a b (L.compLp f))
  rw [fourier_compLp, fourier_frequencyWindow, fourier_frequencyWindow,
    compLp_regularIndicatorProjection, fourier_compLp]

theorem regularGauge_window_balance_transport (L : H →L[ℂ] K)
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (V : Multiplicative ℝ →* unitary (K →L[ℂ] K))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (hV : ∀ x, Continuous (fun t : ℝ => (V (Multiplicative.ofAdd t) : K →L[ℂ] K) x))
    (hL : ∀ t x, L ((U t : H →L[ℂ] H) x) = (V t : K →L[ℂ] K) (L x))
    (f : Lp ℂ 2 (volume : Measure ℝ)) (v w : H)
    (h : regularFrequencyWindow 0 1
      ((star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        (scalarLpTensor volume f v)) =
      (star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        (regularFrequencyWindow 0 1
          ((regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
            (scalarLpTensor volume f w)))) :
    regularFrequencyWindow 0 1
      ((star (regularGauge V hV) : RegularCoreHilbert K →L[ℂ] RegularCoreHilbert K)
        (scalarLpTensor volume f (L v))) =
      (star (regularGauge V hV) : RegularCoreHilbert K →L[ℂ] RegularCoreHilbert K)
        (regularFrequencyWindow 0 1
          ((regularGauge V hV : RegularCoreHilbert K →L[ℂ] RegularCoreHilbert K)
            (scalarLpTensor volume f (L w)))) := by
  have he := congrArg L.compLp h
  rw [compLp_regularFrequencyWindow L,
    compLp_regularGauge_star L U V hU hV hL,
    compLp_scalarLpTensor volume L,
    compLp_regularGauge_star L U V hU hV hL,
    compLp_regularFrequencyWindow L,
    compLp_regularGauge L U V hU hV hL,
    compLp_scalarLpTensor volume L] at he
  exact he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreTraceOriginalGauge
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The trace balance in the original modular representation -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem coreTraceRoot_gauge_balance (x : H) :
    regularFrequencyWindow 0 1
      ((star (regularGauge (modularStrongGroup J Ω hsep hcyc)
        (modularStrongGroup_continuous J Ω hsep hcyc)) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        (regularFrequencyPacket coreTraceFrequencyScalar ((modularCyclicEmbedding (M := M) J Ω x) (cyclicLeftRootVector (M := M) J Ω x)))) =
    (star (regularGauge (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc)) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularFrequencyWindow 0 1
        ((regularGauge (modularStrongGroup J Ω hsep hcyc)
          (modularStrongGroup_continuous J Ω hsep hcyc) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
          (regularFrequencyPacket coreTraceFrequencyScalar
            ((modularCyclicEmbedding (M := M) J Ω x) (cyclicRightRootVector (M := M) J Ω x))))) := by
  let L := modularCyclicEmbedding (M := M) J Ω x
  have h := regularGauge_window_balance_transport
    (H := ModularCyclicSpace M J Ω x) (K := H) L
    (modularCyclicGroup J Ω hsep hcyc x) (modularStrongGroup J Ω hsep hcyc)
    (modularCyclicGroup_continuous J Ω hsep hcyc x)
    (modularStrongGroup_continuous J Ω hsep hcyc)
    (modularCyclicEmbedding_group J Ω hsep hcyc x)
    ((Lp.fourierTransformₗᵢ ℝ ℂ).symm coreTraceFrequencyScalar)
    (cyclicLeftRootVector (M := M) J Ω x) (cyclicRightRootVector (M := M) J Ω x)
    (cyclicSqrtGaugeBalance (M := M) J Ω hsep hcyc x)
  rw [← regularFrequencyPacket_eq_scalarLpTensor (H := H),
    ← regularFrequencyPacket_eq_scalarLpTensor (H := H)] at h
  exact h

theorem coreTraceOriginal_gauge_balance (a : Algebra M) :
    regularFrequencyWindow 0 1
      ((star (regularGauge (modularStrongGroup J Ω hsep hcyc)
        (modularStrongGroup_continuous J Ω hsep hcyc)) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        (regularFrequencyPacket coreTraceFrequencyScalar (a.val Ω))) =
    (star (regularGauge (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc)) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularFrequencyWindow 0 1
        ((regularGauge (modularStrongGroup J Ω hsep hcyc)
          (modularStrongGroup_continuous J Ω hsep hcyc) :
          RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
          (regularFrequencyPacket coreTraceFrequencyScalar
            (tomitaPolarConjugation J Ω hsep hcyc (star a.val Ω))))) := by
  let x := tomitaCoreCoordinate J Ω hsep hcyc a
  have hl : modularCyclicEmbedding (M := M) J Ω x
      (cyclicLeftRootVector (M := M) J Ω x) = a.val Ω := by
    exact coreTraceLeftCoordinate_embedding J Ω hsep hcyc a
  have hr : modularCyclicEmbedding (M := M) J Ω x
      (cyclicRightRootVector (M := M) J Ω x) =
      tomitaPolarConjugation J Ω hsep hcyc (star a.val Ω) := by
    exact coreTraceRightCoordinate_embedding J Ω hsep hcyc a
  have h := coreTraceRoot_gauge_balance (M := M) J Ω hsep hcyc x
  rw [hl, hr] at h
  exact h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreTraceEmbeddingSymmetry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_complete _root_.OAI.KadisonKastler.stateCentralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Trace-vector symmetry for compressed algebra generators -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem coreTraceEmbedding_vector_symmetry_oai (a : Algebra M) :
    let U := modularStrongGroup J Ω hsep hcyc
    let hU := modularStrongGroup_continuous J Ω hsep hcyc
    let C := regularCoreConjugation U hU (tomitaPolarConjugation J Ω hsep hcyc)
    let p := regularFrequencyWindow (H := H) 0 1
    let ξ := coreTraceFrequencyVector Ω
    (p * regularCoreEmbedding U hU a.val * p) ξ =
      C ((star (p * regularCoreEmbedding U hU a.val * p)) ξ) := by
  have hΩ : ∀ s, (modularStrongGroup J Ω hsep hcyc s : H →L[ℂ] H) Ω = Ω := by
    intro s
    simpa only [ofAdd_toAdd] using modularStrongGroup_fixes_state J Ω hsep hcyc s.toAdd
  exact regularCoreEmbedding_symmetry_of_balance
    (modularStrongGroup J Ω hsep hcyc) (modularStrongGroup_continuous J Ω hsep hcyc)
    (tomitaPolarConjugation J Ω hsep hcyc) (modularStrongGroup_polar_commutes J Ω hsep hcyc)
    Ω hΩ a.val (coreTraceOriginal_gauge_balance J Ω hsep hcyc a)

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.coreTraceEmbedding_vector_symmetry_oai.{u_1} := @OAI.KadisonKastler.coreTraceEmbedding_vector_symmetry_oai.{u_1}
