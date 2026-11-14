-- Prove2me | solution 1 for OAI.KadisonKastler.coreTraceTranslation_vector_symmetry
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:55:00.919664+00:00
-- url     : https://prove2.me/submissions/502f6704-1fb6-4664-8906-bf48484d44d3

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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Exponential
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
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
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
import Mathlib.Logic.Equiv.Prod
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
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
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
import Definitions.Def_Q260K028
import Definitions.Def_Q260K029
import Theorems.Thm_OAI_KadisonKastler_regularReflectedConjugation_real_packet

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
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreTraceReflectedPackets
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Reflected conjugation of the trace packets and frequency window -/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem coreTraceFrequencyScalar_real :
    ∀ᵐ t ∂(volume : Measure ℝ), star (coreTraceFrequencyScalar t) = coreTraceFrequencyScalar t := by
  filter_upwards [coreTraceFrequencyScalar_apply_ae] with t ht
  rw [ht]
  by_cases h : t ∈ Set.Ioc (0 : ℝ) 1
  · rw [coreTraceFrequencyFunction, Set.indicator_of_mem h]
    exact Complex.conj_ofReal _
  · simp only [coreTraceFrequencyFunction, Set.indicator_of_notMem h, star_zero]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCoreConjugateGenerators
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.regularVectorMeasure_finite _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Conjugation of the regular generators

The regular modular conjugation sends the represented algebra to the
constant right algebra. Its formula is proved on actual L2 classes.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (J : H ≃ₗᵢ⋆[ℂ] H)
  (hJU : ∀ t x, J ((U t : H →L[ℂ] H) x) = (U t : H →L[ℂ] H) (J x))

include hJU in
theorem regularCoreConjugation_translation (hJ : Function.Involutive J) (s : ℝ) :
    conjugationOperator (regularCoreConjugation U hU J)
      (regularRightTranslation (H := H) (Multiplicative.ofAdd s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      (regularCoreAction U (Multiplicative.ofAdd (-s)) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  have hshift : MeasurePreserving (fun t : ℝ => -t + s) volume volume :=
    (measurePreserving_add_right volume s).comp (Measure.measurePreserving_neg volume)
  have hproduct (t : ℝ) :
      (star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) *
        (U (Multiplicative.ofAdd (-(-t + s))) : H →L[ℂ] H) =
      (U (Multiplicative.ofAdd (-s)) : H →L[ℂ] H) := by
    have he : U (Multiplicative.ofAdd (-t)) * U (Multiplicative.ofAdd (-(-t + s))) =
        U (Multiplicative.ofAdd (-s)) := by
      rw [← map_mul]
      congr 1
      change -t + -(-t + s) = -s
      ring
    simp only [← Unitary.coe_star, regularGroup_star_eq]
    exact congrArg Subtype.val he
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularCoreConjugation_apply_ae U hU J
      ((regularRightTranslation (H := H) (Multiplicative.ofAdd s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (regularCoreConjugation U hU J f)),
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae_eq_comp
      (regularRightTranslation_apply_ae (Multiplicative.ofAdd s)
        (regularCoreConjugation U hU J f)),
    hshift.quasiMeasurePreserving.ae_eq_comp (regularCoreConjugation_apply_ae U hU J f),
    regularCoreAction_apply_ae U (Multiplicative.ofAdd (-s)) f]
    with t ho ht hc hr
  simp only [Function.comp_def, toAdd_ofAdd] at ht hc hr
  change (regularCoreConjugation U hU J
    ((regularRightTranslation (H := H) (Multiplicative.ofAdd s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (regularCoreConjugation U hU J f))) t = _
  rw [ho, ht, hc]
  simp only [← Unitary.coe_star, regularGroup_star_eq U (-t + s)]
  rw [hJU, hJ, hr]
  change ((star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) *
    (U (Multiplicative.ofAdd (-(-t + s))) : H →L[ℂ] H)) (f (-(-t + s))) = _
  rw [hproduct]
  congr 2
  ring

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

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularReflectedGauge
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Gauge identities for the reflected modular conjugation -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (J : H ≃ₗᵢ⋆[ℂ] H)

theorem regularCoreConjugation_traceVector_fixed (Ω : H)
    (hΩ : ∀ s, (U s : H →L[ℂ] H) Ω = Ω) (hJΩ : J Ω = Ω) :
    regularCoreConjugation U hU J (coreTraceFrequencyVector Ω) = coreTraceFrequencyVector Ω := by
  change (star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (regularReflectedConjugation J (regularFrequencyPacket coreTraceFrequencyScalar Ω)) = _
  rw [regularReflectedConjugation_real_packet J _ coreTraceFrequencyScalar_real,
    hJΩ, regularGauge_star_frequencyPacket_fixed U hU Ω hΩ]
  rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreTraceTranslationVector
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Trace-vector symmetry for the translation generators -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
  (hJU : ∀ s x, J ((U s : H →L[ℂ] H) x) = (U s : H →L[ℂ] H) (J x))
  (Ω : H) (hΩ : ∀ s, (U s : H →L[ℂ] H) Ω = Ω) (hJΩ : J Ω = Ω)

include hΩ in
theorem regularCoreAction_traceVector (s : Multiplicative ℝ) :
    (regularCoreAction U s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (coreTraceFrequencyVector Ω) =
    (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (coreTraceFrequencyVector Ω) := by
  change (regularConstantHom volume (U s : H →L[ℂ] H) *
    (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (coreTraceFrequencyVector Ω) = _
  rw [(regularConstant_commute_translation (U s : H →L[ℂ] H) s).eq]
  change (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (regularConstantHom volume (U s : H →L[ℂ] H)
      (regularFrequencyPacket coreTraceFrequencyScalar Ω)) = _
  rw [regularConstantHom_frequencyPacket, hΩ]
  rfl

include hJ hJU hΩ hJΩ in
theorem coreTraceTranslation_vector_symmetry_oai (s : Multiplicative ℝ) :
    (regularRightTranslation (H := H) s : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (coreTraceFrequencyVector Ω) =
    regularCoreConjugation U hU J
      ((star (regularRightTranslation (H := H) s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) (coreTraceFrequencyVector Ω)) := by
  have hCξ := regularCoreConjugation_traceVector_fixed U hU J Ω hΩ hJΩ
  have hc := congrArg (fun T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H =>
    T (coreTraceFrequencyVector Ω))
    (regularCoreConjugation_translation U hU J hJU hJ (-s.toAdd))
  have hs : (regularRightTranslation (H := H) (Multiplicative.ofAdd (-s.toAdd)) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) =
      (star (regularRightTranslation (H := H) s) :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
    exact congrArg Subtype.val (regularGroup_star_eq (regularRightTranslation (H := H)) s.toAdd).symm
  rw [hs] at hc
  change regularCoreConjugation U hU J
    ((star (regularRightTranslation (H := H) s) :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      (regularCoreConjugation U hU J (coreTraceFrequencyVector Ω))) = _ at hc
  rw [hCξ] at hc
  simpa only [neg_neg, ofAdd_toAdd, regularCoreAction_traceVector U Ω hΩ] using hc.symm

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.coreTraceTranslation_vector_symmetry_oai.{u_1} := @OAI.KadisonKastler.coreTraceTranslation_vector_symmetry_oai.{u_1}
