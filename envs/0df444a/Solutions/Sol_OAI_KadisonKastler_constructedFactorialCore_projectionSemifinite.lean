-- Prove2me | solution 1 for OAI.KadisonKastler.constructedFactorialCore_projectionSemifinite
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T16:16:57.891192+00:00
-- url     : https://prove2.me/submissions/80078754-e3fa-497d-9137-dfea4732daa6

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
import Mathlib.Analysis.Normed.Operator.Mul
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
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K043
import Theorems.Thm_OAI_KadisonKastler_constructedCore_traceSymmetry
import Theorems.Thm_OAI_KadisonKastler_core_kills_window_of_kills_trace_packet
import Theorems.Thm_OAI_KadisonKastler_projectionSemifinite_of_finite_projection

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConstructedCoreConjugation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem norm_regularFrequencyPacket (φ : Lp ℂ 2 (volume : Measure ℝ)) (ξ : H) :
    ‖regularFrequencyPacket φ ξ‖ = ‖φ‖ * ‖ξ‖ := by
  rw [regularFrequencyPacket, LinearIsometryEquiv.norm_map, norm_regularTensorVector]

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
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreFrequencyUnitWindow
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.hardyEvaluationAt_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A nonzero bounded frequency window in the modular core

The unit interval supplies an explicit isometric family of vectors fixed by
its frequency projection. No trace or finiteness assertion is used here.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem unitFrequencyScalar_fixed :
    regularIndicatorProjection (Set.Ioc (0 : ℝ) 1) measurableSet_Ioc unitFrequencyScalar =
      unitFrequencyScalar := by
  apply Lp.ext
  filter_upwards [regularIndicatorProjection_apply_ae _ measurableSet_Ioc unitFrequencyScalar,
    (indicatorConstLp_coeFn (p := 2) (s := Set.Ioc (0 : ℝ) 1)
      (μ := volume) (hs := measurableSet_Ioc)
      (hμs := (measure_Ioc_lt_top (μ := volume)).ne) (c := (1 : ℂ)))] with t hp hf
  change regularIndicatorProjection _ _ unitFrequencyScalar t = unitFrequencyScalar t
  rw [hp]
  by_cases ht : t ∈ Set.Ioc (0 : ℝ) 1
  · exact Set.indicator_of_mem ht _
  · rw [Set.indicator_of_notMem ht, show unitFrequencyScalar t = 0 from
      hf.trans (Set.indicator_of_notMem ht _)]

@[simp] theorem norm_unitFrequencyVector (ξ : H) : ‖unitFrequencyVector ξ‖ = ‖ξ‖ := by
  rw [unitFrequencyVector, norm_regularFrequencyPacket, norm_unitFrequencyScalar, one_mul]

theorem unitFrequencyVector_fixed (ξ : H) :
    regularFrequencyWindow 0 1 (unitFrequencyVector ξ) = unitFrequencyVector ξ := by
  rw [unitFrequencyVector, regularFrequencyWindow_packet, unitFrequencyScalar_fixed]

theorem regularFrequencyWindow_unit_ne_zero [Nontrivial H] :
    regularFrequencyWindow (H := H) 0 1 ≠ 0 := by
  obtain ⟨ξ, hξ⟩ := exists_ne (0 : H)
  intro hz
  have hfix := unitFrequencyVector_fixed ξ
  rw [hz, zero_apply] at hfix
  have hn := norm_unitFrequencyVector ξ
  rw [← hfix, norm_zero] at hn
  exact hξ (norm_eq_zero.mp hn.symm)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreTraceFrequencyVector
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.hardyEvaluationAt_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

theorem coreTraceFrequencyScalar_fixed :
    regularIndicatorProjection (Set.Ioc (0 : ℝ) 1) measurableSet_Ioc coreTraceFrequencyScalar =
      coreTraceFrequencyScalar := by
  apply Lp.ext
  filter_upwards [regularIndicatorProjection_apply_ae _ measurableSet_Ioc coreTraceFrequencyScalar,
    coreTraceFrequencyScalar_apply_ae] with t hp ht
  change regularIndicatorProjection _ _ coreTraceFrequencyScalar t = coreTraceFrequencyScalar t
  rw [hp]
  by_cases h : t ∈ Set.Ioc (0 : ℝ) 1
  · exact Set.indicator_of_mem h _
  · rw [Set.indicator_of_notMem h, ht]
    simp [coreTraceFrequencyFunction, h]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem coreTraceFrequencyVector_fixed (Ω : H) :
    regularFrequencyWindow 0 1 (coreTraceFrequencyVector Ω) = coreTraceFrequencyVector Ω := by
  rw [coreTraceFrequencyVector, regularFrequencyWindow_packet, coreTraceFrequencyScalar_fixed]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreTraceSymmetry
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The weakly closed vector symmetry used for the core trace

Its scalar formulation is linear in the operator and passes to weak
operator limits. An involutive antiunitary then turns it into the exact
tracial norm identity needed by the finite-window criterion.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem coreTraceSymmetry_norm (C : H ≃ₗᵢ⋆[ℂ] H) (hC : Function.Involutive C)
    (ξ : H) (T : H →L[ℂ] H) (hT : T ∈ coreTraceSymmetrySpace C ξ) :
    ‖T ξ‖ = ‖(star T) ξ‖ := by
  have he : T ξ = C ((star T) ξ) := by
    apply ext_inner_left ℂ
    intro η
    have hc := conjugateIsometry_inner C (C η) ((star T) ξ)
    rw [hC η] at hc
    have hswap : star (inner ℂ (C η) ((star T) ξ)) =
        inner ℂ ((star T) ξ) (C η) := inner_conj_symm _ _
    rw [hswap] at hc
    change inner ℂ η (T ξ) = inner ℂ η (C ((star T) ξ))
    rw [hc, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    exact hT η
  rw [he, C.norm_map]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteProjectionVectorCriterion
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finiteness from the faithful tracial vector identity on a corner

Only the norm identity for elements of the indicated corner is needed.
This isolates the final projection argument from construction of the
core's tracial vector.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

private theorem operator_vector_norm_sq (a : H →L[ℂ] H) (ξ : H) :
    ‖a ξ‖ ^ 2 = (inner ℂ ξ ((star a * a) ξ)).re := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  change (inner ℂ (a ξ) (a ξ)).re = (inner ℂ ξ ((star a * a) ξ)).re
  exact congrArg Complex.re (ContinuousLinearMap.adjoint_inner_right a ξ (a ξ)).symm

theorem finiteProjectionIn_of_faithful_vector_norm
    (p : AlgebraProjection M) (ξ : H) (hξ : p.val.val ξ = ξ)
    (hfaith : ∀ a : Algebra M, a.val ξ = 0 → a * p.val = 0)
    (htrace : ∀ a : Algebra M, p.val * a = a → a * p.val = a →
      ‖a.val ξ‖ = ‖(star a).val ξ‖) : FiniteProjectionIn M p.val := by
  intro v hvi hpv
  let V : PartialIsometry M := ⟨p, v, hvi⟩
  have hq : V.target ≤ p := (V.target_le_iff_mul p).mpr hpv
  let r := AlgebraProjection.remainder V.target p hq
  have hrv : r.val = p.val - v * star v := rfl
  have hvp : v * p.val = v := V.mul_support
  have hvnorm : ‖v.val ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
    rw [operator_vector_norm_sq]
    have he : star v.val * v.val = p.val.val := congrArg Subtype.val hvi
    rw [he, hξ, norm_sq_eq_re_inner (𝕜 := ℂ)]
    rfl
  have hvsnorm : ‖(star v).val ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
    rw [← htrace v hpv hvp]
    exact hvnorm
  have hrzero : r.val.val ξ = 0 := by
    have hrsq : ‖r.val.val ξ‖ ^ 2 = 0 := by
      rw [operator_vector_norm_sq]
      have hrs : star r.val * r.val = r.val := by
        rw [r.property.isSelfAdjoint.star_eq, r.property.isIdempotentElem.eq]
      have he : star r.val.val * r.val.val = r.val.val := congrArg Subtype.val hrs
      rw [he]
      change (inner ℂ ξ ((p.val.val - v.val * star v.val) ξ)).re = 0
      rw [sub_apply, hξ, inner_sub_right, Complex.sub_re]
      have hvstar := operator_vector_norm_sq (star v.val) ξ
      simp only [star_star] at hvstar
      rw [← hvstar]
      change RCLike.re (inner ℂ ξ ξ) - ‖(star v).val ξ‖ ^ 2 = 0
      rw [← norm_sq_eq_re_inner (𝕜 := ℂ), hvsnorm, sub_self]
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (r.val.val ξ)])
  have hrp : r.val * p.val = r.val := by
    have he := congrArg star (AlgebraProjection.remainder_le V.target p hq)
    change star (p.val * r.val) = star r.val at he
    simpa only [star_mul, p.property.isSelfAdjoint.star_eq,
      r.property.isSelfAdjoint.star_eq] using he
  have hr := hfaith r.val hrzero
  rw [hrp, hrv] at hr
  exact (sub_eq_zero.mp hr).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CoreFrequencyFinite
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The finite-window reduction for the modular core

The frequency window is nonzero, and the weighted packet gives a
faithful vector on its corner. Equality of the vector norms for an
operator and its adjoint makes this corner finite.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (M : VonNeumannAlgebra H)

theorem unitCoreFrequencyProjection_ne_zero [Nontrivial H] :
    (unitCoreFrequencyProjection U hU M).val ≠ 0 := by
  intro he
  exact regularFrequencyWindow_unit_ne_zero (congrArg Subtype.val he)

theorem unitCoreFrequencyProjection_finite_of_norm
    (hM : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M)
    (Ω : H) (hΩ : ∀ t, (U t : H →L[ℂ] H) Ω = Ω)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (htrace : ∀ a : Algebra (regularCoreAlgebra U hU M),
      (unitCoreFrequencyProjection U hU M).val * a = a →
      a * (unitCoreFrequencyProjection U hU M).val = a →
      ‖a.val (coreTraceFrequencyVector Ω)‖ = ‖(star a).val (coreTraceFrequencyVector Ω)‖) :
    FiniteProjectionIn (regularCoreAlgebra U hU M) (unitCoreFrequencyProjection U hU M).val := by
  apply finiteProjectionIn_of_faithful_vector_norm (unitCoreFrequencyProjection U hU M)
    (coreTraceFrequencyVector Ω) (coreTraceFrequencyVector_fixed Ω) ?_ htrace
  intro a ha
  apply Subtype.ext
  exact core_kills_window_of_kills_trace_packet U hU M hM Ω hΩ hsep a.val a.property ha

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConstructedCoreFiniteWindow
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A finite nonzero projection in the constructed modular core -/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}
  (J : H ≃ₗᵢ⋆[ℂ] H) (Ω : H)
  (hsep : Function.Injective (algebraVectorMap M Ω))
  (hcyc : DenseRange (algebraVectorMap M Ω))

theorem constructedCore_unitWindow_finite :
    let U := modularStrongGroup J Ω hsep hcyc
    let hU := modularStrongGroup_continuous J Ω hsep hcyc
    FiniteProjectionIn (regularCoreAlgebra U hU M)
      (unitCoreFrequencyProjection U hU M).val := by
  let U := modularStrongGroup J Ω hsep hcyc
  let hU := modularStrongGroup_continuous J Ω hsep hcyc
  have hn : ∀ s a, a ∈ M → unitaryConj (U s) a ∈ M := by
    intro s a ha
    have he := modularStrongGroup_normalizes J Ω hsep hcyc s
    change unitaryConj (U s) a ∈ (M : Set (H →L[ℂ] H))
    rw [← he]
    exact Set.mem_image_of_mem _ ha
  have hΩ : ∀ s, (U s : H →L[ℂ] H) Ω = Ω := by
    intro s
    simpa only [ofAdd_toAdd] using modularStrongGroup_fixes_state J Ω hsep hcyc s.toAdd
  apply unitCoreFrequencyProjection_finite_of_norm U hU M hn Ω hΩ hsep
  intro a hpa hap
  let P := tomitaPolarConjugation J Ω hsep hcyc
  let C := regularCoreConjugation U hU P
  have hC := regularCoreConjugation_involutive U hU P
    (tomitaPolarConjugation_involutive J Ω hsep hcyc)
    (modularStrongGroup_polar_commutes J Ω hsep hcyc)
  have ha := constructedCore_traceSymmetry J Ω hsep hcyc a.val a.property
  have hl : regularFrequencyWindow 0 1 * a.val = a.val := congrArg Subtype.val hpa
  have hr : a.val * regularFrequencyWindow 0 1 = a.val := congrArg Subtype.val hap
  rw [hl, hr] at ha
  exact coreTraceSymmetry_norm C hC (coreTraceFrequencyVector Ω) a.val ha

theorem constructedFactorialCore_projectionSemifinite_oai [Nontrivial H]
    (hfactor : ScalarCenter (regularCoreAlgebra (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc) M)) :
    let R := regularCoreAlgebra (modularStrongGroup J Ω hsep hcyc)
      (modularStrongGroup_continuous J Ω hsep hcyc) M
    ∀ p : AlgebraProjection R, p.val ≠ 0 →
      ∃ q : AlgebraProjection R, q ≤ p ∧ q.val ≠ 0 ∧ FiniteProjectionIn R q.val := by
  exact projectionSemifinite_of_finite_projection hfactor
    (unitCoreFrequencyProjection _ _ M) (unitCoreFrequencyProjection_ne_zero _ _ M)
    (constructedCore_unitWindow_finite J Ω hsep hcyc)

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.constructedFactorialCore_projectionSemifinite_oai.{u_1} := @OAI.KadisonKastler.constructedFactorialCore_projectionSemifinite_oai.{u_1}
