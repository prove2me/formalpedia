-- Prove2me | solution 1 for OAI.KadisonKastler.FrequencySmoothing.infDist_smooth_sandwich_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:08:30.976205+00:00
-- url     : https://prove2.me/submissions/55954bc7-bd8d-4fb9-9b30-2a2156f44854

import Mathlib
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.LpSpace
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
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
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
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
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
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Tactic
import Mathlib.Tactic.DeriveCountable
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
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_Q260K065
import Definitions.Def_Q260K032
import Theorems.Thm_OAI_KadisonKastler_infDist_poisson_sandwich_le

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DirectIntegralConjugacy
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Assembling fiber conjugacies on the actual direct-integral space

`OperatorFieldDecomposition` records the decomposition and reconstruction
properties of a given constant-fiber direct integral. It is data, not a
published theorem or an existence assertion. The assembly argument below
uses actual multiplication unitaries on `L²(X,H)`.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem RepresentsOperatorField.unique {μ : Measure X} {F : X → H →L[ℂ] H}
    {T S : Lp H 2 μ →L[ℂ] Lp H 2 μ}
    (hT : RepresentsOperatorField μ F T) (hS : RepresentsOperatorField μ F S) : T = S := by
  apply ContinuousLinearMap.ext
  intro f
  exact Lp.ext ((hT f).trans (hS f).symm)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RealNestMultiplier
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Real character averaging of a bounded multiplier

The real group is made discrete only for its invariant mean. Its unitary
representation is the actual character multiplication on L²(real,H).
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularFieldOperator_commutes_character
    (F : ℝ → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun t => F t x) volume)
    (C : ℝ) (hC : ∀ᵐ t, ‖F t‖ ≤ C) (a : ℝ) :
    Commute (regularFieldOperator volume F hF C hC)
      (regularCharacterUnitary (H := H) a :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  change _ * _ = _ * _
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularFieldOperator_represents volume F hF C hC
      ((regularCharacterUnitary (H := H) a :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularCharacterUnitary_apply_ae a f,
    regularCharacterUnitary_apply_ae a (regularFieldOperator volume F hF C hC f),
    regularFieldOperator_represents volume F hF C hC f] with t h₁ h₂ h₃ h₄
  change (regularFieldOperator volume F hF C hC
      ((regularCharacterUnitary (H := H) a :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)) t =
    ((regularCharacterUnitary (H := H) a :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        (regularFieldOperator volume F hF C hC f)) t
  rw [h₁, h₂, h₃, h₄, map_smul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveFrequencyAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The concrete algebra of positive-frequency multipliers -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A nest-preserving represented field is an element of the concrete
positive-frequency multiplier algebra. -/
theorem regularFieldOperator_mem_positiveFrequencyAlgebra
    (F : ℝ → H →L[ℂ] H)
    (hF : ∀ x, MeasureTheory.AEStronglyMeasurable (fun t => F t x) MeasureTheory.volume)
    (C : ℝ) (hC : ∀ᵐ t ∂MeasureTheory.volume, ‖F t‖ ≤ C)
    (hpres : PreservesProjectionNest regularFrequencyNest
      (regularFieldOperator MeasureTheory.volume F hF C hC)) :
    regularFieldOperator MeasureTheory.volume F hF C hC ∈
      positiveFrequencyAlgebra (H := H) := by
  refine ⟨regularFieldOperator_commutes_character F hF C hC, ?_⟩
  have hp := hpres 0
  simp only [regularFrequencyNest, neg_zero] at hp
  rw [sub_mul, one_mul, sub_mul, sub_eq_zero] at hp
  exact hp.symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FourierConstant
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Constant operators commute with the Fourier frequency cuts -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem constantSchwartz_toLp (T : H →L[ℂ] H) (f : SchwartzMap ℝ H) :
    (f.postcompCLM T).toLp 2 = regularConstantOperator volume T (f.toLp 2) := by
  apply Lp.ext
  filter_upwards [(f.postcompCLM T).coeFn_toLp 2,
    regularConstantOperator_apply_ae volume T (f.toLp 2), f.coeFn_toLp 2]
    with t h₁ h₂ h₃
  rw [h₁, h₂, h₃]
  rfl

private theorem fourier_constant_schwartz_p0 (T : H →L[ℂ] H) (f : SchwartzMap ℝ H) :
    (𝓕 (regularConstantOperator volume T (f.toLp 2)) : RegularCoreHilbert H) =
      regularConstantOperator volume T (𝓕 (f.toLp 2)) := by
  rw [← constantSchwartz_toLp, SchwartzMap.toLp_fourier_eq,
    SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (f.postcompCLM T)).coeFn_toLp 2,
    regularConstantOperator_apply_ae volume T ((𝓕 f).toLp 2),
    (𝓕 f).coeFn_toLp 2] with t h₁ h₂ h₃
  rw [h₁, h₂, h₃]
  change (𝓕 (fun s => T (f s))) t = T (𝓕 (f : ℝ → H) t)
  simp only [Real.fourier_eq]
  rw [← T.integral_comp_comm ((Real.fourierIntegral_convergent_iff t).mpr f.integrable)]
  congr 1
  funext s
  exact (T.map_smul _ _).symm

theorem fourier_regularConstantOperator (T : H →L[ℂ] H) (f : RegularCoreHilbert H) :
    (𝓕 (regularConstantOperator volume T f) : RegularCoreHilbert H) =
      regularConstantOperator volume T (𝓕 f) := by
  let F : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H := Lp.fourierTransformₗᵢ ℝ H
  let C : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H := regularConstantOperator volume T
  have he : F.comp C = C.comp F := by
    apply DFunLike.coe_injective
    apply (SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := H)
      (p := 2) ENNReal.ofNat_ne_top).equalizer (F.comp C).continuous (C.comp F).continuous
    funext g
    exact fourier_constant_schwartz_p0 T g
  exact congrArg (fun A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => A f) he

theorem regularConstantOperator_commutes_frequency (T : H →L[ℂ] H) (a : ℝ) :
    Commute (regularConstantOperator volume T) (regularFrequencyProjection a) := by
  apply ContinuousLinearMap.ext
  intro f
  apply (Lp.fourierTransformₗᵢ ℝ H).injective
  change (𝓕 (regularConstantOperator volume T (regularFrequencyProjection a f)) :
    RegularCoreHilbert H) = 𝓕 (regularFrequencyProjection a (regularConstantOperator volume T f))
  rw [fourier_regularConstantOperator]
  apply Lp.ext
  have hp := regularFrequencyProjection_apply_fourier a (regularConstantOperator volume T f)
  rw [fourier_regularConstantOperator] at hp
  filter_upwards [regularConstantOperator_apply_ae volume T (𝓕 (regularFrequencyProjection a f)),
    regularFrequencyProjection_apply_fourier a f, hp,
    regularConstantOperator_apply_ae volume T (𝓕 f)] with t hc hf hg ht
  rw [hc, hg, hf]
  by_cases hmem : t ∈ Set.Ioi (a / (2 * Real.pi))
  · simp only [Set.indicator_of_mem hmem, ht]
  · simp only [Set.indicator_of_notMem hmem, map_zero]

theorem regularConstantOperator_mem_positiveFrequencyAlgebra (T : H →L[ℂ] H) :
    regularConstantOperator volume T ∈ positiveFrequencyAlgebra (H := H) := by
  refine ⟨fun s => (regularCharacter_commute_constant s T).symm, ?_⟩
  rw [← (regularConstantOperator_commutes_frequency T 0).eq, mul_assoc,
    (regularFrequencyProjection_isStarProjection (H := H) 0).isIdempotentElem.eq]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HardyPoissonProducts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instIsProbabilityMeasureBilateralWalkPathBilateralWalkLaw _root_.OAI.KadisonKastler.instIsProbabilityMeasureRandomWalkBoundaryRandomWalkBoundaryMeasure _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.randomWalkPathLaw_probability _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Poisson products from the published Hardy evaluation

The boundary multiplication operators and their positive-frequency algebra
are concrete. Multiplicativity is obtained by applying the precisely cited
published evaluation homomorphism, including for constant middle factors.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem RepresentsOperatorField.mul
    {B S : ℝ → H →L[ℂ] H}
    {T V : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hB : RepresentsOperatorField volume B T) (hS : RepresentsOperatorField volume S V) :
    RepresentsOperatorField volume (fun t => B t * S t) (T * V) := by
  intro f
  filter_upwards [hB (V f), hS f] with t h₁ h₂
  change (T (V f)) t = B t (S t (f t))
  rw [h₁, h₂]

theorem RepresentsOperatorField.mem_positiveFrequencyAlgebra
    {B : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hB : ∀ x, AEStronglyMeasurable (fun t => B t x) volume)
    {C : ℝ} (hC : ∀ᵐ t, ‖B t‖ ≤ C)
    (hBT : RepresentsOperatorField volume B T)
    (hT : PreservesProjectionNest regularFrequencyNest T) :
    T ∈ positiveFrequencyAlgebra (H := H) := by
  have he := RepresentsOperatorField.unique hBT (regularFieldOperator_represents volume B hB C hC)
  rw [he] at hT ⊢
  exact regularFieldOperator_mem_positiveFrequencyAlgebra B hB C hC hT

private theorem poisson_constant (x : H →L[ℂ] H) (t r : ℝ) (hr : 0 < r) :
    measurablePoissonAverage (fun _ => x) (fun _ => aestronglyMeasurable_const)
      ‖x‖ (Filter.Eventually.of_forall fun _ => le_rfl) t r hr = x := by
  apply ContinuousLinearMap.ext
  intro ξ
  change (∫ _, x ξ ∂ProbabilityTheory.cauchyMeasure t (NNReal.mk r hr.le)) = x ξ
  rw [integral_const, probReal_univ, one_smul]

variable [TopologicalSpace.SeparableSpace H]

/-- The same identity with an arbitrary constant operator in the middle.
Only the two boundary multipliers need to preserve the frequency nest. -/
theorem measurablePoissonAverage_sandwich_of_hardy
    (hHardy : PublishedHardyMultiplierEvaluation.{u})
    (B S : ℝ → H →L[ℂ] H)
    (hB : ∀ ξ, AEStronglyMeasurable (fun t => B t ξ) volume)
    (hS : ∀ ξ, AEStronglyMeasurable (fun t => S t ξ) volume)
    (CB CS : ℝ) (hb : ∀ᵐ t, ‖B t‖ ≤ CB) (hs : ∀ᵐ t, ‖S t‖ ≤ CS)
    (T V : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hBT : RepresentsOperatorField volume B T) (hSV : RepresentsOperatorField volume S V)
    (hT : PreservesProjectionNest regularFrequencyNest T)
    (hV : PreservesProjectionNest regularFrequencyNest V)
    (x : H →L[ℂ] H)
    (hBxS : ∀ ξ, AEStronglyMeasurable (fun t => (B t * x * S t) ξ) volume)
    (C : ℝ) (hC : ∀ᵐ t, ‖B t * x * S t‖ ≤ C)
    (t r : ℝ) (hr : 0 < r) :
    measurablePoissonAverage B hB CB hb t r hr * x *
        measurablePoissonAverage S hS CS hs t r hr =
      measurablePoissonAverage (fun s => B s * x * S s) hBxS C hC t r hr := by
  let A : positiveFrequencyAlgebra (H := H) :=
    ⟨T, hBT.mem_positiveFrequencyAlgebra hB hb hT⟩
  let D : positiveFrequencyAlgebra (H := H) :=
    ⟨V, hSV.mem_positiveFrequencyAlgebra hS hs hV⟩
  let X : positiveFrequencyAlgebra (H := H) :=
    ⟨regularConstantOperator volume x, regularConstantOperator_mem_positiveFrequencyAlgebra x⟩
  have hX : RepresentsOperatorField volume (fun _ => x) X.val :=
    regularConstantOperator_apply_ae volume x
  obtain ⟨ev, he⟩ := hHardy H t r hr
  have hex : ev X = x := (he _ (fun _ => aestronglyMeasurable_const) ‖x‖
    (Filter.Eventually.of_forall fun _ => le_rfl) X hX hr).trans (poisson_constant x t r hr)
  rw [← he B hB CB hb A hBT hr, ← he S hS CS hs D hSV hr]
  conv_lhs => rw [← hex]
  rw [← he _ hBxS C hC (A * X * D) ((hBT.mul hX).mul hSV) hr]
  simp only [map_mul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProbabilityMatrixDistance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Distance to an algebra after vector integration

Diagonal amplification commutes with the actual vector integral. Applying
the published complete commutant-distance bound to the commutant gives
an algebra approximation without choosing measurable nearest points.
-/

namespace KadisonKastler

open MeasureTheory
open scoped BigOperators Pointwise

noncomputable section

variable {S H : Type*} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.matrixIntegralStarOrder
attribute [local instance] OAI.KadisonKastler.integralSourceStarOrder
/-- Scalar multiplication scales distance to the concrete complex algebra. -/
theorem infDist_smul_algebra (M : VonNeumannAlgebra H) (z : ℂ)
    (T : H →L[ℂ] H) :
    Metric.infDist (z • T) (M : Set (H →L[ℂ] H)) =
      ‖z‖ * Metric.infDist T (M : Set (H →L[ℂ] H)) := by
  classical
  by_cases hz : z = 0
  · subst z
    simp only [zero_smul, norm_zero, zero_mul]
    exact Metric.infDist_zero_of_mem M.zero_mem
  · have hset : z • (M : Set (H →L[ℂ] H)) = (M : Set (H →L[ℂ] H)) := by
      ext y
      simp only [Set.mem_smul_set]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact M.toStarSubalgebra.smul_mem hx z
      · intro hy
        refine ⟨z⁻¹ • y, M.toStarSubalgebra.smul_mem hy z⁻¹, ?_⟩
        rw [smul_smul, mul_inv_cancel₀ hz, one_smul]
    have he := infDist_smul₀ hz (M : Set (H →L[ℂ] H)) T
    rwa [hset] at he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AnalyticAlgebraBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Algebra errors of the demodulated analytic products

The Hardy product identity follows from evaluation and preservation of
the frequency nest. The resulting norm estimates pass from boundary
algebra distance to positive-height distance.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.analyticAlgebraOrder
attribute [local instance] OAI.KadisonKastler.analyticAlgebraStarOrder
/-- The published Hardy evaluation and actual frequency preservation give
the quantitative demodulated algebra error at every positive height. -/
private theorem infDist_demodulated_sandwich_le_of_product_identity
    (M : VonNeumannAlgebra H)
    (hDistance : PublishedBlockCommutantApproximation (Algebra M.commutant) H)
    (B S U V : ℝ → H →L[ℂ] H)
    (hB : ∀ ξ, AEStronglyMeasurable (fun s => B s ξ) volume)
    (hS : ∀ ξ, AEStronglyMeasurable (fun s => S s ξ) volume)
    {CB CS : ℝ} (hCB : 0 ≤ CB)
    (hb : ∀ᵐ s, ‖B s‖ ≤ CB) (hs : ∀ᵐ s, ‖S s‖ ≤ CS)
    {δ e : ℝ} (hδ : 0 ≤ δ) (he : 0 ≤ e)
    (hu : ∀ᵐ s, ‖U s‖ ≤ 1) (hv : ∀ᵐ s, ‖V s‖ ≤ 1)
    (hBU : ∀ᵐ s, ‖B s - U s‖ ≤ δ) (hSV : ∀ᵐ s, ‖S s - V s‖ ≤ δ)
    (x : H →L[ℂ] H)
    (hnear : ∀ᵐ s, Metric.infDist (U s * x * V s) (M : Set (H →L[ℂ] H)) ≤ e * ‖x‖)
    (t r : ℝ) (hr : 0 < r)
    (hproduct : measurablePoissonAverage B hB CB hb t r hr * x *
        measurablePoissonAverage S hS CS hs t r hr =
      measurablePoissonAverage (fun s => B s * x * S s)
        (sandwich_vector_measurable B S hB hS x) (CB * ‖x‖ * CS)
        (ae_norm_sandwich_le B S hCB hb hs x) t r hr) :
    Metric.infDist
      (demodulatedPoissonAverage B hB CB hb t r hr * x *
        demodulatedPoissonAverage S hS CS hs t r hr)
      (M : Set (H →L[ℂ] H)) ≤ (Real.exp r) ^ 2 * ((e + 2 * δ + δ ^ 2) * ‖x‖) := by
  let z : ℂ := (Real.exp r : ℂ) * star (Circle.exp t : ℂ)
  have hz : ‖z‖ = Real.exp r := by
    change ‖(Real.exp r : ℂ) * star (Circle.exp t : ℂ)‖ = Real.exp r
    rw [norm_mul, norm_star, Circle.norm_coe, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos r)]
  have hid : demodulatedPoissonAverage B hB CB hb t r hr * x *
      demodulatedPoissonAverage S hS CS hs t r hr =
    z ^ 2 • measurablePoissonAverage (fun s => B s * x * S s)
      (sandwich_vector_measurable B S hB hS x) (CB * ‖x‖ * CS)
      (ae_norm_sandwich_le B S hCB hb hs x) t r hr := by
    simp only [demodulatedPoissonAverage, smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [hproduct]
    simp only [z, pow_two]
  rw [hid, infDist_smul_algebra, norm_pow, hz]
  exact mul_le_mul_of_nonneg_left
    (infDist_poisson_sandwich_le M hDistance B S U V hB hS hCB hb hs hδ he
      hu hv hBU hSV x hnear t r hr) (sq_nonneg _)

theorem infDist_demodulated_sandwich_le
    [TopologicalSpace.SeparableSpace H]
    (hHardy : PublishedHardyMultiplierEvaluation.{u})
    (M : VonNeumannAlgebra H)
    (hDistance : PublishedBlockCommutantApproximation (Algebra M.commutant) H)
    (B S U V : ℝ → H →L[ℂ] H)
    (hB : ∀ ξ, AEStronglyMeasurable (fun s => B s ξ) volume)
    (hS : ∀ ξ, AEStronglyMeasurable (fun s => S s ξ) volume)
    {CB CS : ℝ} (hCB : 0 ≤ CB)
    (hb : ∀ᵐ s, ‖B s‖ ≤ CB) (hs : ∀ᵐ s, ‖S s‖ ≤ CS)
    {δ e : ℝ} (hδ : 0 ≤ δ) (he : 0 ≤ e)
    (hu : ∀ᵐ s, ‖U s‖ ≤ 1) (hv : ∀ᵐ s, ‖V s‖ ≤ 1)
    (hBU : ∀ᵐ s, ‖B s - U s‖ ≤ δ) (hSV : ∀ᵐ s, ‖S s - V s‖ ≤ δ)
    (x : H →L[ℂ] H)
    (hnear : ∀ᵐ s, Metric.infDist (U s * x * V s) (M : Set (H →L[ℂ] H)) ≤ e * ‖x‖)
    (t r : ℝ) (hr : 0 < r)
    (hBpres : PreservesProjectionNest (regularFrequencyNest (H := H))
      (regularFieldOperator volume B hB CB hb))
    (hSpres : PreservesProjectionNest (regularFrequencyNest (H := H))
      (regularFieldOperator volume S hS CS hs)) :
    Metric.infDist
      (demodulatedPoissonAverage B hB CB hb t r hr * x *
        demodulatedPoissonAverage S hS CS hs t r hr)
      (M : Set (H →L[ℂ] H)) ≤ (Real.exp r) ^ 2 * ((e + 2 * δ + δ ^ 2) * ‖x‖) := by
  let TB : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
    regularFieldOperator volume B hB CB hb
  let TS : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
    regularFieldOperator volume S hS CS hs
  have hBT : RepresentsOperatorField volume B TB := regularFieldOperator_represents volume B hB CB hb
  have hST : RepresentsOperatorField volume S TS := regularFieldOperator_represents volume S hS CS hs
  have hproduct := measurablePoissonAverage_sandwich_of_hardy hHardy B S hB hS CB CS hb hs
    TB TS hBT hST hBpres hSpres x
    (sandwich_vector_measurable B S hB hS x) (CB * ‖x‖ * CS)
    (ae_norm_sandwich_le B S hCB hb hs x) t r hr
  exact infDist_demodulated_sandwich_le_of_product_identity
    M hDistance B S U V hB hS hCB hb hs hδ he hu hv hBU hSV x hnear t r hr hproduct

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FrequencySmoothing
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.conjugation_algebraVector _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteTraceEmbedding_inner _root_.OAI.KadisonKastler.concreteTraceLeftAction_embedding _root_.OAI.KadisonKastler.concreteTraceLeftUnitary_coe _root_.OAI.KadisonKastler.concreteTraceRightAction_embedding _root_.OAI.KadisonKastler.concreteTraceRightUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.productBoundaryRepresentation_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.rescaledGraphMap_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_apply _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Actual smoothing from quantitative frequency-cut defects

The boundary approximants are constructed by the published nest distance
theorem and the proved invariant averaging. The smoothing operators are
their actual Poisson integrals; their inverse and algebra estimates use
the published Hardy evaluation, with no additional analytic identities.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace FrequencySmoothing

attribute [local instance] OAI.KadisonKastler.frequencySmoothingStarOrder
variable {F G : ℝ → H →L[ℂ] H} {δ : ℝ}

attribute [local instance] OAI.KadisonKastler.frequencySmoothingOrder
theorem infDist_smooth_sandwich_le_oai [TopologicalSpace.SeparableSpace H]
    (hHardy : PublishedHardyMultiplierEvaluation.{u})
    (M : VonNeumannAlgebra H)
    (hDistance : PublishedBlockCommutantApproximation (Algebra M.commutant) H)
    (A : FrequencySmoothing F δ) (B : FrequencySmoothing G δ)
    (hFn : ∀ᵐ t, ‖F t‖ ≤ 1) (hGn : ∀ᵐ t, ‖G t‖ ≤ 1)
    {e : ℝ} (he : 0 ≤ e) (heδ : e ≤ δ)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 16) (x : H →L[ℂ] H)
    (hnear : ∀ᵐ s, Metric.infDist (F s * x * G s) (M : Set (H →L[ℂ] H)) ≤ e * ‖x‖)
    (t r : ℝ) (hr : 0 < r) (hrδ : r ≤ δ) :
    Metric.infDist (A.smooth t r hr * x * B.smooth t r hr)
      (M : Set (H →L[ℂ] H)) ≤ 12 * δ * ‖x‖ := by
  have hb := infDist_demodulated_sandwich_le hHardy M hDistance
    A.boundary B.boundary F G A.measurable B.measurable
    (show 0 ≤ 1 + 2 * δ by positivity) A.bounded B.bounded
    (show 0 ≤ 2 * δ by positivity) he hFn hGn A.close B.close x hnear t r hr
    A.preserves B.preserves
  have habs : |r| ≤ 1 := by rw [abs_of_pos hr]; linarith
  have hex := Real.abs_exp_sub_one_le habs
  rw [abs_of_pos hr] at hex
  have hex' : Real.exp r ≤ 1 + 2 * δ := by linarith [le_abs_self (Real.exp r - 1)]
  have hex2 : (Real.exp r) ^ 2 ≤ 2 := by
    nlinarith [Real.exp_pos r]
  have herr : e + 2 * (2 * δ) + (2 * δ) ^ 2 ≤ 6 * δ := by nlinarith
  exact hb.trans ((mul_le_mul hex2 (mul_le_mul_of_nonneg_right herr (norm_nonneg x))
    (by positivity) (by norm_num)).trans_eq (by ring))

end FrequencySmoothing

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.FrequencySmoothing.infDist_smooth_sandwich_le_oai.{u} := @OAI.KadisonKastler.FrequencySmoothing.infDist_smooth_sandwich_le_oai.{u}
