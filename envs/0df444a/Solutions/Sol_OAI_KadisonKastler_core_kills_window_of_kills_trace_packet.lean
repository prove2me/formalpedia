-- Prove2me | solution 1 for OAI.KadisonKastler.core_kills_window_of_kills_trace_packet
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:21:48.411016+00:00
-- url     : https://prove2.me/submissions/07a4a695-e16f-4a6c-a841-20ec2cd1111b

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
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
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
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
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
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
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K028
import Definitions.Def_Q260K064

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FixedPointGap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fixed-point algebras and the common-action gap

The fixed algebra is an actual von Neumann algebra, defined as a commutant.
The scalar invariant mean constructed in `InvariantOperatorMean` averages
ordinary unit-ball approximants into fixed-point approximants without
increasing either their norm or their error. No existence of a scalar mean
or fixed-point averaging map is postulated here.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {G H : Type*} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem fixedPointAlgebra_le (U : G →* unitary (H →L[ℂ] H))
    (M : VonNeumannAlgebra H) : fixedPointAlgebra U M ≤ M :=
  fun T hT => ((mem_fixedPointAlgebra_iff U M T).mp hT).1

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The concrete regular core and its first fixed-point inclusion

The tensor algebra is the commutant of the constant copy of `P'` on
`L²(ℝ,H)`. The regular core is the von Neumann algebra generated by the
concrete regular embedding and translations. Its generators lie in the
tensor algebra and are fixed by the common regular action. This proves
the first fixed-point inclusion without a crossed-product assumption.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem regularCoreAlgebra_le_tensor (P : VonNeumannAlgebra H)
    (hP : ∀ s T, T ∈ P → unitaryConj (U s) T ∈ P) :
    regularCoreAlgebra U hU P ≤ regularTensorAlgebra P :=
  (regularCoreAlgebra_le_fixed U hU P hP).trans (fixedPointAlgebra_le _ _)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreFixed
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fixed decomposable operators in the regular representation

The gauge transforms a decomposable operator fixed by `U_s ⊗ ρ_s` into
a translation-fixed multiplier. The preceding scalar Fubini argument
then makes it a constant operator, so the original operator belongs to
the concrete regular image `π(B(H))`.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

/-- Fixedness passes through the exact gauge intertwining identity. -/
theorem regularGauge_translation_fixed
    {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hfixed : ∀ s, unitaryConj (regularCoreAction U s) T = T)
    (s : Multiplicative ℝ) :
    unitaryConj (regularRightTranslation (H := H) s)
      (unitaryConj (regularGauge U hU) T) = unitaryConj (regularGauge U hU) T := by
  have he : regularGauge U hU * regularCoreAction U s =
      regularRightTranslation (H := H) s * regularGauge U hU :=
    Subtype.ext (regularGauge_intertwines_action U hU s)
  rw [← unitaryConj_mul, ← he, unitaryConj_mul, hfixed]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreFrequencyVectors
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Vectors supported in the bounded-frequency core corners -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularFrequencyWindow_packet (a b : ℝ)
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (ξ : H) :
    regularFrequencyWindow a b (regularFrequencyPacket φ ξ) =
      regularFrequencyPacket (regularIndicatorProjection (Set.Ioc a b) measurableSet_Ioc φ) ξ := by
  unfold regularFrequencyWindow regularFrequencyPacket
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.apply_symm_apply,
    regularIndicatorProjection_tensor]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreTraceFrequencyVector
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The bounded-frequency vector for the core trace

The scalar weight is exp(pi (s-1)) on (0,1], in the Fourier convention
exp(-2 pi i t s). The corresponding vector has explicit L2 bounds and frequency support.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

theorem coreTraceFrequencyScalar_apply_ae :
    coreTraceFrequencyScalar =ᵐ[volume] coreTraceFrequencyFunction :=
  coreTraceFrequencyFunction_memLp.coeFn_toLp

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularActionSpectral
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded spectral multipliers of the common regular action

These operators lie in the core commutant. They are used to recover
frequency packets from the bounded-frequency trace vector.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem commute_regularActionMultiplier_of_fixed
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : ∀ s, unitaryConj (regularCoreAction U s) T = T)
    (φ : ℝ → ℂ) (hφ : Measurable φ) (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C) :
    Commute T (regularActionMultiplier U hU φ hφ C hC) := by
  let F := Lp.fourierTransformₗᵢ ℝ H
  let T' := unitaryConj (regularGauge U hU) T
  have htrans (s : Multiplicative ℝ) : Commute T'
      (regularRightTranslation (H := H) s :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :=
    ((commute_unitary_iff_star_right_conjugate (regularRightTranslation (H := H) s).property).mpr
      (regularGauge_translation_fixed U hU hT s)).symm
  have hspec := commute_scalarMultiplier_of_characters (F.conjStarAlgEquiv T')
    (fourier_commute_characters_of_translations T' htrans) φ hφ C hC
  have hback (A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :
      F.symm.conjStarAlgEquiv (F.conjStarAlgEquiv A) = A := by
    apply ContinuousLinearMap.ext
    intro f
    simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      LinearIsometryEquiv.symm_symm,
      LinearIsometryEquiv.symm_apply_apply]
  have hspec' := hspec.map F.symm.conjStarAlgEquiv
  rw [hback] at hspec'
  have hfinal := hspec'.map (Unitary.conjStarAlgAut ℂ _ (star (regularGauge U hU)))
  change Commute (unitaryConj (star (regularGauge U hU))
      (unitaryConj (regularGauge U hU) T))
    (regularActionMultiplier U hU φ hφ C hC) at hfinal
  rwa [unitaryConj_star_unitaryConj] at hfinal

theorem regularActionMultiplier_mem_commutant (M : VonNeumannAlgebra H)
    (hM : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M)
    (φ : ℝ → ℂ) (hφ : Measurable φ) (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C) :
    regularActionMultiplier U hU φ hφ C hC ∈ (regularCoreAlgebra U hU M).commutant := by
  apply VonNeumannAlgebra.mem_commutant_iff.mpr
  intro T hT
  exact (commute_regularActionMultiplier_of_fixed U hU T
    ((mem_fixedPointAlgebra_iff _ _ _).mp
      (regularCoreAlgebra_le_fixed U hU M hM hT)).2 φ hφ C hC).eq

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

theorem regularConstantHom_frequencyPacket (a : H →L[ℂ] H)
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (x : H) :
    regularConstantHom volume a (regularFrequencyPacket φ x) =
      regularFrequencyPacket φ (a x) := by
  rw [regularFrequencyPacket_eq_tensor, regularConstantHom_tensorVector,
    regularFrequencyPacket_eq_tensor]

omit [CompleteSpace H] in
theorem regularScalarMultiplier_tensor (φ : ℝ → ℂ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C) (ψ : Lp ℂ 2 (volume : Measure ℝ)) (x : H) :
    regularScalarMultiplier φ hφ C hC (regularTensorVector ψ x) =
      regularTensorVector (regularScalarMultiplier φ hφ C hC ψ) x := by
  apply Lp.ext
  filter_upwards [regularScalarMultiplier_apply_ae φ hφ C hC (regularTensorVector ψ x),
    regularTensorVector_apply_ae ψ x,
    regularTensorVector_apply_ae (regularScalarMultiplier φ hφ C hC ψ) x,
    regularScalarMultiplier_apply_ae φ hφ C hC ψ] with t hm hψ ht hs
  rw [hm, hψ, ht, hs, smul_smul]
  rfl

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (Ω : H) (hΩ : ∀ t, (U t : H →L[ℂ] H) Ω = Ω)

include hΩ in
theorem regularGauge_frequencyPacket_fixed (ψ : Lp ℂ 2 (volume : Measure ℝ)) :
    (regularGauge U hU : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularFrequencyPacket ψ Ω) = regularFrequencyPacket ψ Ω := by
  rw [regularFrequencyPacket_eq_tensor]
  apply Lp.ext
  filter_upwards [regularGauge_apply_ae U hU
      (regularTensorVector ((Lp.fourierTransformₗᵢ ℝ ℂ).symm ψ) Ω),
    regularTensorVector_apply_ae ((Lp.fourierTransformₗᵢ ℝ ℂ).symm ψ) Ω]
      with t hg ht
  rw [hg, ht, map_smul, hΩ]

include hΩ in
theorem regularGauge_star_frequencyPacket_fixed (ψ : Lp ℂ 2 (volume : Measure ℝ)) :
    (star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularFrequencyPacket ψ Ω) = regularFrequencyPacket ψ Ω := by
  have h := congrArg (fun f => (star (regularGauge U hU) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)
    (regularGauge_frequencyPacket_fixed U hU Ω hΩ ψ)
  have he := congrArg (fun A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H =>
      A (regularFrequencyPacket ψ Ω))
    (Unitary.star_mul_self_of_mem (regularGauge U hU).property)
  exact h.symm.trans he

include hΩ in
theorem regularActionMultiplier_packet (φ : ℝ → ℂ) (hφ : Measurable φ)
    (C : ℝ) (hC : ∀ t, ‖φ t‖ ≤ C) (ψ : Lp ℂ 2 (volume : Measure ℝ)) :
    regularActionMultiplier U hU φ hφ C hC (regularFrequencyPacket ψ Ω) =
      regularFrequencyPacket (regularScalarMultiplier φ hφ C hC ψ) Ω := by
  simp only [regularActionMultiplier, unitaryConj, mul_apply_eq_comp,
    Unitary.coe_star, star_star, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    LinearIsometryEquiv.symm_symm]
  rw [regularGauge_frequencyPacket_fixed U hU Ω hΩ]
  unfold regularFrequencyPacket
  rw [LinearIsometryEquiv.apply_symm_apply, regularScalarMultiplier_tensor]
  exact regularGauge_star_frequencyPacket_fixed U hU Ω hΩ _

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreTraceReciprocal
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.hardyEvaluationAt_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A bounded reciprocal for the core trace packet

The reciprocal is cut off outside the unit frequency window. Its
spectral multiplier recovers the unweighted unit packet exactly.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

theorem coreTraceReciprocal_scalar :
    regularScalarMultiplier coreTraceReciprocal coreTraceReciprocal_measurable
      (Real.exp Real.pi) coreTraceReciprocal_bound coreTraceFrequencyScalar =
      unitFrequencyScalar := by
  apply Lp.ext
  filter_upwards [regularScalarMultiplier_apply_ae coreTraceReciprocal
      coreTraceReciprocal_measurable (Real.exp Real.pi) coreTraceReciprocal_bound
      coreTraceFrequencyScalar,
    coreTraceFrequencyScalar_apply_ae,
    (indicatorConstLp_coeFn (p := 2) (s := Set.Ioc (0 : ℝ) 1)
      (μ := volume) (hs := measurableSet_Ioc)
      (hμs := (measure_Ioc_lt_top (μ := volume)).ne) (c := (1 : ℂ)))] with t hm hw hu
  change unitFrequencyScalar t = _ at hu
  rw [hm, hw, hu]
  by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
  · simp only [coreTraceReciprocal, coreTraceFrequencyFunction,
      Set.indicator_of_mem ht, smul_eq_mul, ← Complex.ofReal_mul, ← Real.exp_add]
    norm_num [show Real.pi * (1 - t) + Real.pi * (t - 1) = 0 by ring]
  · simp [coreTraceReciprocal, coreTraceFrequencyFunction, ht]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem coreTraceReciprocal_packet
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (Ω : H) (hΩ : ∀ t, (U t : H →L[ℂ] H) Ω = Ω) :
    regularActionMultiplier U hU coreTraceReciprocal coreTraceReciprocal_measurable
      (Real.exp Real.pi) coreTraceReciprocal_bound (coreTraceFrequencyVector Ω) =
      unitFrequencyVector Ω := by
  rw [coreTraceFrequencyVector, regularActionMultiplier_packet U hU Ω hΩ,
    coreTraceReciprocal_scalar]
  rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreWindowPackets
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.hardyEvaluationAt_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Simple packets in the unit frequency window -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

theorem unitWindow_indicator_scalar (s : Set ℝ) (hs : MeasurableSet s)
    (hfin : (volume : Measure ℝ) s ≠ ⊤) :
    regularIndicatorProjection (Set.Ioc (0 : ℝ) 1) measurableSet_Ioc
      (indicatorConstLp 2 hs hfin (1 : ℂ)) =
      regularIndicatorProjection s hs unitFrequencyScalar := by
  apply Lp.ext
  filter_upwards [regularIndicatorProjection_apply_ae (Set.Ioc (0 : ℝ) 1)
      measurableSet_Ioc (indicatorConstLp 2 hs hfin (1 : ℂ)),
    regularIndicatorProjection_apply_ae s hs unitFrequencyScalar,
    indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hfin) (c := (1 : ℂ)),
    (indicatorConstLp_coeFn (p := 2) (s := Set.Ioc (0 : ℝ) 1)
      (μ := volume) (hs := measurableSet_Ioc)
      (hμs := (measure_Ioc_lt_top (μ := volume)).ne) (c := (1 : ℂ)))]
      with t hp hq hs' hw
  change unitFrequencyScalar t = _ at hw
  rw [hp, hq]
  by_cases hts : t ∈ s <;> by_cases htw : t ∈ Set.Ioc (0 : ℝ) 1 <;>
    simp [hts, htw, hs', hw]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem regularTensorVector_indicator (s : Set ℝ) (hs : MeasurableSet s)
    (hfin : (volume : Measure ℝ) s ≠ ⊤) (x : H) :
    regularTensorVector (indicatorConstLp 2 hs hfin (1 : ℂ)) x =
      indicatorConstLp 2 hs hfin x := by
  apply Lp.ext
  filter_upwards [regularTensorVector_apply_ae (indicatorConstLp 2 hs hfin (1 : ℂ)) x,
    indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hfin) (c := (1 : ℂ)),
    indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hfin) (c := x)]
      with t ht h1 hx
  rw [ht, h1, hx]
  by_cases hts : t ∈ s <;> simp [hts]

theorem unitWindow_indicator_packet (s : Set ℝ) (hs : MeasurableSet s)
    (hfin : (volume : Measure ℝ) s ≠ ⊤) (x : H) :
    regularFrequencyWindow 0 1
      ((Lp.fourierTransformₗᵢ ℝ H).symm (indicatorConstLp 2 hs hfin x)) =
      regularFrequencyPacket (regularIndicatorProjection s hs unitFrequencyScalar) x := by
  rw [← regularTensorVector_indicator s hs hfin x]
  change regularFrequencyWindow 0 1
    (regularFrequencyPacket (indicatorConstLp 2 hs hfin (1 : ℂ)) x) = _
  rw [regularFrequencyWindow_packet, unitWindow_indicator_scalar]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreFrequencyFaithfulness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.StandardTracialPosition.conjugation_algebraVector _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.hardyEvaluationAt_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Faithfulness of the bounded-frequency vector on its corner

Spectral multipliers of the regular action give localized scalar packets.
The original commutant fills their vector coordinates, proving that an
operator in the core which kills the trace packet vanishes on its window.
No traciality or finiteness assertion is made here.
-/

namespace KadisonKastler

open MeasureTheory UnitalTomsWinter
open scoped ENNReal

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (M : VonNeumannAlgebra H)
  (hM : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M)
  (Ω : H) (hΩ : ∀ t, (U t : H →L[ℂ] H) Ω = Ω)

include hM hΩ in
theorem core_kills_unit_packet_of_kills_trace_packet
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : T ∈ regularCoreAlgebra U hU M)
    (hz : T (coreTraceFrequencyVector Ω) = 0) : T (unitFrequencyVector Ω) = 0 := by
  have hc := VonNeumannAlgebra.mem_commutant_iff.mp
    (regularActionMultiplier_mem_commutant U hU M hM coreTraceReciprocal
      coreTraceReciprocal_measurable (Real.exp Real.pi) coreTraceReciprocal_bound) T hT
  have he := congrArg (fun A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H =>
    A (coreTraceFrequencyVector Ω)) hc
  change T (regularActionMultiplier U hU coreTraceReciprocal
    coreTraceReciprocal_measurable (Real.exp Real.pi) coreTraceReciprocal_bound
      (coreTraceFrequencyVector Ω)) = _ at he
  rw [coreTraceReciprocal_packet U hU Ω hΩ, mul_apply_eq_comp, hz, map_zero] at he
  exact he

include hM hΩ in
theorem core_kills_window_of_kills_unit_packet
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : T ∈ regularCoreAlgebra U hU M)
    (hz : T (unitFrequencyVector Ω) = 0) :
    T * regularFrequencyWindow 0 1 = 0 := by
  have hfixed := ((mem_fixedPointAlgebra_iff _ _ _).mp
    (regularCoreAlgebra_le_fixed U hU M hM hT)).2
  have hconst := (mem_regularTensorAlgebra_iff M T).mp
    (regularCoreAlgebra_le_tensor U hU M hM hT)
  have hdense : DenseRange (fun b : Algebra M.commutant => b.val Ω) :=
    Generator.commutant_orbit_dense M Ω (fun a ha => by
      apply hsep
      exact ha)
  have hpacket (s : Set ℝ) (hs : MeasurableSet s) (x : H) :
      T (regularFrequencyPacket (regularIndicatorProjection s hs unitFrequencyScalar) x) = 0 := by
    let φ := s.indicator (fun _ => (1 : ℂ))
    have hb (t : ℝ) : ‖φ t‖ ≤ 1 := by
      by_cases ht : t ∈ s <;> simp [φ, ht]
    have hc := commute_regularActionMultiplier_of_fixed U hU T hfixed φ
      (measurable_const.indicator hs) 1 hb
    have he := congrArg (fun A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H =>
      A (unitFrequencyVector Ω)) hc.eq
    have hzero : T
        (regularFrequencyPacket (regularIndicatorProjection s hs unitFrequencyScalar) Ω) = 0 := by
      change T (regularActionMultiplier U hU φ (measurable_const.indicator hs) 1 hb
        (regularFrequencyPacket unitFrequencyScalar Ω)) = _ at he
      rw [regularActionMultiplier_packet U hU Ω hΩ] at he
      change T (regularFrequencyPacket (regularIndicatorProjection s hs unitFrequencyScalar) Ω) =
        regularActionMultiplier U hU φ (measurable_const.indicator hs) 1 hb
          (T (unitFrequencyVector Ω)) at he
      simpa only [hz, map_zero] using he
    have hh : (fun y : H => T (regularFrequencyPacket
        (regularIndicatorProjection s hs unitFrequencyScalar) y)) = fun _ => 0 := by
      apply hdense.equalizer
      · exact T.continuous.comp ((Lp.fourierTransformₗᵢ ℝ H).symm.continuous.comp
          (regularTensorVector _).continuous)
      · exact continuous_const
      · funext b
        change T (regularFrequencyPacket
          (regularIndicatorProjection s hs unitFrequencyScalar) (b.val Ω)) = 0
        rw [← regularConstantHom_frequencyPacket]
        have hb' := congrArg (fun A : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H =>
          A (regularFrequencyPacket (regularIndicatorProjection s hs unitFrequencyScalar) Ω))
          (hconst b.val b.property)
        change regularConstantHom volume b.val
          (T (regularFrequencyPacket (regularIndicatorProjection s hs unitFrequencyScalar) Ω)) =
          T (regularConstantHom volume b.val
            (regularFrequencyPacket (regularIndicatorProjection s hs unitFrequencyScalar) Ω)) at hb'
        rw [← hb', hzero, map_zero]
    exact congrFun hh x
  have hall (f : RegularCoreHilbert H) :
      T (regularFrequencyWindow 0 1 ((Lp.fourierTransformₗᵢ ℝ H).symm f)) = 0 := by
    induction f using Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) with
    | @indicatorConst x s hs hfin =>
        rw [Lp.simpleFunc.coe_indicatorConst, unitWindow_indicator_packet s hs hfin.ne]
        exact hpacket s hs x
    | @add f g hf hg hdis hF hG =>
        simp only [map_add, hF, hG, add_zero]
    | isClosed =>
        exact isClosed_eq (T.continuous.comp ((regularFrequencyWindow 0 1).continuous.comp
          (Lp.fourierTransformₗᵢ ℝ H).symm.continuous)) continuous_const
  apply ContinuousLinearMap.ext
  intro f
  change T (regularFrequencyWindow 0 1 f) = 0
  simpa only [LinearIsometryEquiv.symm_apply_apply] using
    hall ((Lp.fourierTransformₗᵢ ℝ H) f)

include hM hΩ in
theorem core_kills_window_of_kills_trace_packet_oai
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hT : T ∈ regularCoreAlgebra U hU M)
    (hz : T (coreTraceFrequencyVector Ω) = 0) :
    T * regularFrequencyWindow 0 1 = 0 :=
  core_kills_window_of_kills_unit_packet U hU M hM Ω hΩ hsep T hT
    (core_kills_unit_packet_of_kills_trace_packet U hU M hM Ω hΩ T hT hz)

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.core_kills_window_of_kills_trace_packet_oai.{u_1} := @OAI.KadisonKastler.core_kills_window_of_kills_trace_packet_oai.{u_1}
