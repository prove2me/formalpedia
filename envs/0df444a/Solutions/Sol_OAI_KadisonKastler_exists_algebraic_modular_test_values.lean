-- Prove2me | solution 1 for OAI.KadisonKastler.exists_algebraic_modular_test_values
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:58:03.511853+00:00
-- url     : https://prove2.me/submissions/4a895c26-dcc4-4e91-8625-39ebb14012cf

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
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Combination
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
import Mathlib.Analysis.Normed.Algebra.Exponential
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
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Pi.Bounds
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
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
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
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Countable
import Mathlib.LinearAlgebra.Dual.Lemmas
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
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
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
import Mathlib.Topology.Algebra.InfiniteSum.Real
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
import Mathlib.Topology.MetricSpace.Contracting
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
import Definitions.Def_Q260K035
import Theorems.Thm_OAI_KadisonKastler_modular_localized_algebra_approximate

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RegularCommutantPackets
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Gauged wave-packet coefficients

Compression between two scalar wave packets turns commutation with the
regular copy of `P` into membership in `P'`. Translation commutation
then gives the exact covariance of these coefficients. These are the
operator-valued coefficients used in the regular commutant argument.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ ξ, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))

theorem norm_regularGaugedPacket_apply (φ : Lp ℂ 2 (volume : Measure ℝ)) (ξ : H) :
    ‖regularGaugedPacket U hU φ ξ‖ = ‖φ‖ * ‖ξ‖ := by
  change ‖(star (regularGauge U hU) : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (regularTensorVector φ ξ)‖ = _
  exact (Unitary.norm_map (star (regularGauge U hU)) (regularTensorVector φ ξ)).trans
    (norm_regularTensorVector φ ξ)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularLocalizedPackets
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.hardyEvaluationAt_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fourier packets localized by the modular spectral cuts

The already constructed Fourier gauge identity transports bounded scalar
frequency windows to short modular spectral intervals, fiber by fiber.
The norm identity gives the total weight of the resulting vector states.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

namespace ModularSpectralResolution

variable (S : ModularSpectralResolution M Ω)

theorem norm_fourierPacket (φ : Lp ℂ 2 (volume : Measure ℝ)) (ξ : H) :
    ‖S.fourierPacket φ ξ‖=‖φ‖*‖ξ‖ := by
  rw [fourierPacket,LinearIsometryEquiv.norm_map,norm_regularGaugedPacket_apply]

theorem fourierPacket_cut (a : ℝ) (φ : Lp ℂ 2 (volume : Measure ℝ)) (ξ : H) :
    regularFieldOperator volume (fun s => S.upperCut (a-2*Real.pi*s))
      (S.measurable a) 1 (Filter.Eventually.of_forall fun _ => S.upper_contracts _)
      (S.fourierPacket φ ξ)=S.fourierPacket (regularFrequencyProjection a φ) ξ := by
  let G := regularGauge S.group S.continuous
  let e := Lp.fourierTransformₗᵢ ℝ H
  let x := regularTensorVector φ ξ
  let A := regularFieldOperator volume (fun s => S.upperCut (a-2*Real.pi*s))
    (S.measurable a) 1 (Filter.Eventually.of_forall fun _ => S.upper_contracts _)
  have hG : (G : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      ((star G : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) x)=x :=
    congrArg (fun T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H => T x)
      (Unitary.mul_star_self_of_mem G.property)
  have h := congrArg
    (fun T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H =>
      e (T ((star G : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) x)))
    (S.gauge_identity a)
  change e ((star G : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (regularFrequencyProjection a ((G : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
      ((star G : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) x))))=
    e (e.symm (A (e ((star G : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) x)))) at h
  rw [hG,e.apply_symm_apply] at h
  have ht : regularFrequencyProjection a x=regularTensorVector (regularFrequencyProjection a φ) ξ := by
    change regularFrequencyProjection a (scalarLpTensor volume φ ξ)=
      scalarLpTensor volume (regularFrequencyProjection a φ) ξ
    exact (compLp_regularFrequencyProjection (ContinuousLinearMap.toSpanSingleton ℂ ξ) a φ).symm
  rw [ht] at h
  exact h.symm

theorem fourierPacket_lower_support (a : ℝ) (φ : Lp ℂ 2 (volume : Measure ℝ))
    (hφ : regularFrequencyProjection a φ=φ) (ξ : H) :
    ∀ᵐ s : ℝ, S.upperCut (a-2*Real.pi*s) (S.fourierPacket φ ξ s)=S.fourierPacket φ ξ s := by
  have h := regularFieldOperator_represents volume (fun s => S.upperCut (a-2*Real.pi*s))
    (S.measurable a) 1 (Filter.Eventually.of_forall fun _ => S.upper_contracts _)
    (S.fourierPacket φ ξ)
  rw [S.fourierPacket_cut,hφ] at h
  exact h.symm

theorem fourierPacket_upper_support (b : ℝ) (φ : Lp ℂ 2 (volume : Measure ℝ))
    (hφ : regularFrequencyProjection b φ=0) (ξ : H) :
    ∀ᵐ s : ℝ, S.upperCut (b-2*Real.pi*s) (S.fourierPacket φ ξ s)=0 := by
  have h := regularFieldOperator_represents volume (fun s => S.upperCut (b-2*Real.pi*s))
    (S.measurable b) 1 (Filter.Eventually.of_forall fun _ => S.upper_contracts _)
    (S.fourierPacket φ ξ)
  have hz : S.fourierPacket (0 : Lp ℂ 2 (volume : Measure ℝ)) ξ=0 := by
    simp [fourierPacket,regularGaugedPacket]
  rw [S.fourierPacket_cut,hφ,hz] at h
  filter_upwards [h,Lp.coeFn_zero (E := H) (p := 2) (μ := (volume : Measure ℝ))] with s hs hz
  exact hs.symm.trans hz

end ModularSpectralResolution

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarPacketMeasure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The probability measure and action average of a scalar packet -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

theorem integral_scalarPacketMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (f : ℝ → E) :
    (∫ t, f t ∂scalarPacketMeasure φ)=∫ t, (‖φ t‖^2) • f t := by
  rw [scalarPacketMeasure,integral_withDensity_eq_integral_toReal_smul
    ((Lp.stronglyMeasurable φ).measurable.norm.pow_const 2 |>.ennreal_ofReal)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext t
  rw [ENNReal.toReal_ofReal (sq_nonneg _)]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem scalarPacketAverage_coefficient
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (hφ : ‖φ‖=1) (T : H →L[ℂ] H) (ξ : H) :
    inner ℂ ξ (scalarPacketAverage U hU φ hφ T ξ)=
      ∫ t, (‖φ t‖^2) • inner ℂ ξ (stateActionOrbit U T t ξ) := by
  let : IsProbabilityMeasure (scalarPacketMeasure φ) := scalarPacketMeasure_probability φ hφ
  have hi := integrable_bounded_operator_vector (scalarPacketMeasure φ) (stateActionOrbit U T)
    (fun x => (stateActionOrbit_continuous U hU T x).aestronglyMeasurable)
    (Eventually.of_forall fun t => (stateActionOrbit_norm U T t).le) ξ
  change (innerSL ℂ ξ) (∫ t, stateActionOrbit U T t ξ ∂scalarPacketMeasure φ)=_
  rw [← (innerSL ℂ ξ).integral_comp_comm hi,integral_scalarPacketMeasure]
  rfl

theorem scalarPacketAverage_strongly_invariant
    (ψ : (H →L[ℂ] H) →L[ℂ] ℂ)
    (hψ : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : H →L[ℂ] H),
      ψ (stateActionAverage U hU μ T)=ψ T)
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (hφ : ‖φ‖=1) (T : H →L[ℂ] H) :
    ψ (scalarPacketAverage U hU φ hφ T)=ψ T := by
  let : IsProbabilityMeasure (scalarPacketMeasure φ) := scalarPacketMeasure_probability φ hφ
  exact hψ (scalarPacketMeasure φ) T

theorem regularGaugedPacket_coefficient
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (hφ : ‖φ‖=1) (T : H →L[ℂ] H) (ξ : H) :
    inner ℂ (regularGaugedPacket U hU φ ξ)
      (regularConstantHom volume T (regularGaugedPacket U hU φ ξ))=
        inner ℂ ξ (scalarPacketAverage U hU φ hφ T ξ) := by
  rw [scalarPacketAverage_coefficient,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [regularGaugedPacket_apply_ae U hU φ ξ,
    regularConstantHom_apply_ae (volume : Measure ℝ) T (regularGaugedPacket U hU φ ξ)] with t hf hT
  rw [hT,hf,map_smul,map_smul,inner_smul_left,inner_smul_right]
  have hi : inner ℂ
      ((star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) ξ)
      (T ((star (U (Multiplicative.ofAdd t)) : H →L[ℂ] H) ξ))=
      inner ℂ ξ (stateActionOrbit U T t ξ) := by
    change inner ℂ (star (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ)
      (T (star (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ))=
      inner ℂ ξ ((U (Multiplicative.ofAdd t) : H →L[ℂ] H)
        (T (star (U (Multiplicative.ofAdd t) : H →L[ℂ] H) ξ)))
    exact ContinuousLinearMap.adjoint_inner_left _ _ _
  rw [hi]
  change star (φ t)*(φ t*inner ℂ ξ (stateActionOrbit U T t ξ))=
    ((‖φ t‖^2 : ℝ) : ℂ)*inner ℂ ξ (stateActionOrbit U T t ξ)
  rw [← mul_assoc,Complex.star_def,Complex.conj_mul',Complex.ofReal_pow]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ScalarPacketCompression
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Packet compression equals the scalar probability action average -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem scalarPacketAverage_eq_compression
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (hφ : ‖φ‖=1) (T : H →L[ℂ] H) :
    scalarPacketAverage U hU φ hφ T=
      operatorCompression (regularGaugedPacket U hU φ) (regularConstantHom volume T) := by
  suffices he : (scalarPacketAverage U hU φ hφ T).toLinearMap=
      (operatorCompression (regularGaugedPacket U hU φ) (regularConstantHom volume T)).toLinearMap by
    ext ξ
    exact LinearMap.congr_fun he ξ
  apply (ext_inner_map _ _).mp
  intro ξ
  have h : inner ℂ ξ (scalarPacketAverage U hU φ hφ T ξ)=
      inner ℂ ξ (operatorCompression (regularGaugedPacket U hU φ)
        (regularConstantHom volume T) ξ) := by
    rw [operatorCompression_apply]
    change inner ℂ ξ (scalarPacketAverage U hU φ hφ T ξ)=
      inner ℂ ξ ((regularGaugedPacket U hU φ).adjoint
        (regularConstantHom volume T (regularGaugedPacket U hU φ ξ)))
    rw [ContinuousLinearMap.adjoint_inner_right]
    exact (regularGaugedPacket_coefficient U hU φ hφ T ξ).symm
  have hs := congrArg star h
  calc
    _ = star (inner ℂ ξ (scalarPacketAverage U hU φ hφ T ξ)) := (inner_conj_symm _ _).symm
    _ = star (inner ℂ ξ (operatorCompression (regularGaugedPacket U hU φ)
      (regularConstantHom volume T) ξ)) := hs
    _ = _ := inner_conj_symm _ _

theorem scalarPacketAverage_selfAdjoint
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (hφ : ‖φ‖=1)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (scalarPacketAverage U hU φ hφ T) := by
  rw [scalarPacketAverage_eq_compression]
  have hc : (regularConstantHom (volume : Measure ℝ) T).adjoint=regularConstantHom volume T := by
    rw [← ContinuousLinearMap.star_eq_adjoint,← map_star,hT.star_eq]
  change (operatorCompression (regularGaugedPacket U hU φ) (regularConstantHom volume T)).adjoint=_
  simp only [operatorCompression_apply,ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint,hc,ContinuousLinearMap.comp_assoc]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularPacketCoefficient
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Integrated vector-state coefficients of modular Fourier packets -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem integrable_regular_vector_coefficient (F : RegularCoreHilbert H) (T : H →L[ℂ] H) :
    Integrable (fun s => inner ℂ (F s) (T (F s))) volume := by
  apply (L2.integrable_inner (𝕜:=ℂ) F (regularConstantHom volume T F)).congr
  filter_upwards [regularConstantHom_apply_ae (volume : Measure ℝ) T F] with s hs
  exact congrArg (inner ℂ (F s)) hs

theorem integral_regular_vector_coefficient (F : RegularCoreHilbert H) (T : H →L[ℂ] H) :
    (∫ s : ℝ, inner ℂ (F s) (T (F s)))=inner ℂ F (regularConstantHom volume T F) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [regularConstantHom_apply_ae (volume : Measure ℝ) T F] with s hs
  exact (congrArg (inner ℂ (F s)) hs).symm

variable {M : VonNeumannAlgebra H} {Ω : H}

namespace ModularSpectralResolution

variable (S : ModularSpectralResolution M Ω)

theorem fourierPacket_coefficient
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (hφ : ‖φ‖=1) (T : H →L[ℂ] H) (ξ : H) :
    (∫ s : ℝ, inner ℂ (S.fourierPacket φ ξ s) (T (S.fourierPacket φ ξ s)))=
      inner ℂ ξ (scalarPacketAverage S.group S.continuous φ hφ T ξ) := by
  rw [integral_regular_vector_coefficient]
  let F := regularGaugedPacket S.group S.continuous φ ξ
  let e := Lp.fourierTransformₗᵢ ℝ H
  have he : regularConstantHom volume T (e F)=e (regularConstantHom volume T F) :=
    (fourier_compLp T F).symm
  change inner ℂ (e F) (regularConstantHom volume T (e F))=_
  rw [he,e.inner_map_map]
  exact regularGaugedPacket_coefficient S.group S.continuous φ hφ T ξ

theorem fourierPacket_coefficient_re
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (hφ : ‖φ‖=1) (T : H →L[ℂ] H) (ξ : H) :
    (∫ s : ℝ, (inner ℂ (S.fourierPacket φ ξ s) (T (S.fourierPacket φ ξ s))).re)=
      (inner ℂ ξ (scalarPacketAverage S.group S.continuous φ hφ T ξ)).re := by
  calc
    _ = (∫ s : ℝ, inner ℂ (S.fourierPacket φ ξ s) (T (S.fourierPacket φ ξ s))).re :=
      integral_re (𝕜:=ℂ) (integrable_regular_vector_coefficient _ _)
    _ = _ := congrArg Complex.re (S.fourierPacket_coefficient φ hφ T ξ)

end ModularSpectralResolution

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ShortFrequencyScalar
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Unit scalar packets in arbitrarily short frequency intervals -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

theorem shortFrequencyIndicator_norm_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < ‖shortFrequencyIndicator δ‖ := by
  rw [shortFrequencyIndicator,norm_indicatorConstLp (by norm_num) (by norm_num)]
  have hwidth : 0 < δ/(2*Real.pi) := by positivity
  have hv : 0 < (volume : Measure ℝ).real (Set.Ioc 0 (δ/(2*Real.pi))) := by
    simpa only [measureReal_def,Real.volume_Ioc,sub_zero,ENNReal.toReal_ofReal hwidth.le] using hwidth
  exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hv _)

theorem shortFrequencyIndicator_low (δ : ℝ) :
    regularIndicatorProjection (Set.Ioi (0 : ℝ)) measurableSet_Ioi (shortFrequencyIndicator δ)=
      shortFrequencyIndicator δ := by
  apply Lp.ext
  filter_upwards [regularIndicatorProjection_apply_ae _ measurableSet_Ioi (shortFrequencyIndicator δ),
    indicatorConstLp_coeFn (p:=2) (s:=Set.Ioc 0 (δ/(2*Real.pi))) (μ:=volume)
      (hs:=measurableSet_Ioc) (hμs:=(measure_Ioc_lt_top (μ:=volume)).ne) (c:=(1 : ℂ))]
    with t hp hf
  change shortFrequencyIndicator δ t=_ at hf
  rw [hp]
  by_cases ht : 0 < t
  · exact Set.indicator_of_mem ht _
  · rw [Set.indicator_of_notMem (show t ∉ Set.Ioi (0 : ℝ) from ht)]
    exact (hf.trans (Set.indicator_of_notMem (fun h => ht h.1) _)).symm

theorem shortFrequencyIndicator_high (δ : ℝ) :
    regularIndicatorProjection (Set.Ioi (δ/(2*Real.pi))) measurableSet_Ioi
      (shortFrequencyIndicator δ)=0 := by
  apply Lp.ext
  filter_upwards [regularIndicatorProjection_apply_ae _ measurableSet_Ioi (shortFrequencyIndicator δ),
    indicatorConstLp_coeFn (p:=2) (s:=Set.Ioc 0 (δ/(2*Real.pi))) (μ:=volume)
      (hs:=measurableSet_Ioc) (hμs:=(measure_Ioc_lt_top (μ:=volume)).ne) (c:=(1 : ℂ)),
    Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with t hp hf hz
  change shortFrequencyIndicator δ t=_ at hf
  rw [hp,hz]
  by_cases ht : δ/(2*Real.pi) < t
  · rw [Set.indicator_of_mem (show t ∈ Set.Ioi (δ/(2*Real.pi)) from ht),hf,
      Set.indicator_of_notMem (show t ∉ Set.Ioc 0 (δ/(2*Real.pi)) from fun h => not_le_of_gt ht h.2)]
    rfl
  · exact Set.indicator_of_notMem (show t ∉ Set.Ioi (δ/(2*Real.pi)) from ht) _

theorem exists_short_frequency_scalar {δ : ℝ} (hδ : 0 < δ) :
    ∃ φ : Lp ℂ 2 (volume : Measure ℝ), ‖φ‖=1 ∧
      regularFrequencyProjection 0 φ=φ ∧ regularFrequencyProjection δ φ=0 := by
  let f := shortFrequencyIndicator δ
  let c : ℂ := (‖f‖⁻¹ : ℝ)
  let g := c • f
  let e := Lp.fourierTransformₗᵢ ℝ ℂ
  have hf : 0 < ‖f‖ := shortFrequencyIndicator_norm_pos hδ
  have hg : ‖g‖=1 := by
    change ‖c • f‖=1
    rw [norm_smul]
    change ‖((‖f‖⁻¹ : ℝ) : ℂ)‖*‖f‖=1
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hf),inv_mul_cancel₀ hf.ne']
  refine ⟨e.symm g,by rwa [e.symm.norm_map],?_,?_⟩
  · change e.symm (regularIndicatorProjection (Set.Ioi (0/(2*Real.pi))) measurableSet_Ioi
      (e (e.symm g)))=e.symm g
    rw [e.apply_symm_apply]
    congr 1
    simp only [zero_div]
    change regularIndicatorProjection (Set.Ioi (0 : ℝ)) measurableSet_Ioi (c • f)=c • f
    rw [map_smul,shortFrequencyIndicator_low]
  · change e.symm (regularIndicatorProjection (Set.Ioi (δ/(2*Real.pi))) measurableSet_Ioi
      (e (e.symm g)))=0
    rw [e.apply_symm_apply]
    change e.symm (regularIndicatorProjection (Set.Ioi (δ/(2*Real.pi))) measurableSet_Ioi
      (c • f))=0
    rw [map_smul,shortFrequencyIndicator_high,smul_zero,map_zero]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_VectorStateWitness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A unit-vector witness for a strict state inequality

A self-adjoint operator cannot have a state value above all its vector
values. The proof uses only the quadratic-form order and positivity of states.
-/

namespace KadisonKastler

open NaimarkZFC
open scoped ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem state_value_le_of_vector_bound
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (hφ : IsState φ)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) (c : ℝ)
    (hbound : ∀ ξ, (inner ℂ ξ (T ξ)).re ≤ c*‖ξ‖^2) : (φ T).re ≤ c := by
  let B := (c : ℂ) • (1 : H →L[ℂ] H)-T
  have hc : IsSelfAdjoint (c : ℂ) := by simp [isSelfAdjoint_iff]
  have hB : IsSelfAdjoint B := hc.smul (IsSelfAdjoint.one _ ) |>.sub hT
  have hBs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hB
  have hpos : B.IsPositive := by
    apply (ContinuousLinearMap.isPositive_iff' B).mpr
    refine ⟨hB,fun ξ => ?_⟩
    have hr : ((inner ℂ (B ξ) ξ).re : ℂ)=inner ℂ (B ξ) ξ :=
      hBs.coe_re_inner_apply_self ξ
    rw [← hr]
    have he : (inner ℂ (B ξ) ξ).re=c*‖ξ‖^2-(inner ℂ ξ (T ξ)).re := by
      simp only [B,sub_apply,smul_apply,one_apply_eq_self,inner_sub_left,inner_smul_left,
        inner_self_eq_norm_sq_to_K]
      change ((star (c : ℂ))*((‖ξ‖ : ℂ)^2)-inner ℂ (T ξ) ξ).re=_
      rw [← Complex.ofReal_pow]
      simp only [Complex.sub_re,Complex.mul_re,Complex.conj_ofReal,
        Complex.star_def,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
      exact congrArg (fun r : ℝ => c*‖ξ‖^2-r)
        (show (inner ℂ (T ξ) ξ).re=(inner ℂ ξ (T ξ)).re from inner_re_symm (𝕜:=ℂ) (T ξ) ξ)
    rw [he]
    exact_mod_cast (sub_nonneg.mpr (hbound ξ))
  have hp := (positiveOfSquares φ hφ.2).map_nonneg
    ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr hpos)
  have hreal := hp.1
  change 0 ≤ (φ ((c : ℂ) • (1 : H →L[ℂ] H)-T)).re at hreal
  rw [map_sub,map_smul,((isState_iff φ).mp hφ).1,smul_eq_mul,mul_one,
    Complex.sub_re,Complex.ofReal_re] at hreal
  linarith

theorem exists_vector_state_gt
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (hφ : IsState φ)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) {c : ℝ} (hc : c < (φ T).re) :
    ∃ ξ : H, ‖ξ‖=1 ∧ c < (inner ℂ ξ (T ξ)).re := by
  have hex : ∃ ξ : H, c*‖ξ‖^2 < (inner ℂ ξ (T ξ)).re := by
    by_contra hn
    push Not at hn
    exact (not_le_of_gt hc) (state_value_le_of_vector_bound φ hφ T hT c hn)
  obtain ⟨ξ,hξ⟩ := hex
  have hne : ξ ≠ 0 := by
    intro h
    simp only [h,norm_zero,map_zero,inner_zero_left,Complex.zero_re,mul_zero,zero_pow
      (by decide : (2 : ℕ) ≠ 0),lt_self_iff_false] at hξ
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hne
  refine ⟨(‖ξ‖⁻¹ : ℝ) • ξ,?_,?_⟩
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
  · have he : (inner ℂ ((‖ξ‖⁻¹ : ℝ) • ξ) (T ((‖ξ‖⁻¹ : ℝ) • ξ))).re=
        ‖ξ‖⁻¹^2*(inner ℂ ξ (T ξ)).re := by
      change (inner ℂ (((‖ξ‖⁻¹ : ℝ) : ℂ) • ξ)
        (T (((‖ξ‖⁻¹ : ℝ) : ℂ) • ξ))).re=_
      rw [map_smul,inner_smul_left,inner_smul_right]
      change (star ((‖ξ‖⁻¹ : ℝ) : ℂ)*
        (((‖ξ‖⁻¹ : ℝ) : ℂ)*inner ℂ ξ (T ξ))).re=_
      simp only [Complex.star_def,Complex.conj_ofReal,Complex.mul_re,Complex.ofReal_re,
        Complex.ofReal_im,zero_mul,sub_zero]
      ring
    rw [he]
    have hm := mul_lt_mul_of_pos_left hξ (sq_pos_of_pos (inv_pos.mpr hn))
    have hi : ‖ξ‖⁻¹^2*‖ξ‖^2=1 := by rw [← mul_pow,inv_mul_cancel₀ hn.ne']; norm_num
    have heq : ‖ξ‖⁻¹^2*(c*‖ξ‖^2)=c := by
      calc
        _ = c*(‖ξ‖⁻¹^2*‖ξ‖^2) := by ring
        _ = c := by rw [hi,mul_one]
    rwa [heq] at hm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularPacketSelection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A short spectral interval retaining a strict state inequality

Strong invariance and the packet norm identity allow one Fourier fiber to
retain any strict self-adjoint test. This is the local separation step toward
the required approximate-eigenstate decomposition, without a disintegration
hypothesis or an assumed measure on states.
-/

namespace KadisonKastler

open MeasureTheory NaimarkZFC

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_packet_fiber_gt
    (F : RegularCoreHilbert H) (hF : ‖F‖=1) (T : H →L[ℂ] H) {c : ℝ}
    (hc : c < ∫ s : ℝ, (inner ℂ (F s) (T (F s))).re)
    (P : ℝ → Prop) (hP : ∀ᵐ s : ℝ, P s) :
    ∃ s : ℝ, P s ∧ c*‖F s‖^2 < (inner ℂ (F s) (T (F s))).re := by
  by_contra hn
  push Not at hn
  have hle : ∀ᵐ s : ℝ, (inner ℂ (F s) (T (F s))).re ≤ c*‖F s‖^2 :=
    hP.mono fun s hs => hn s hs
  have hi := (integrable_regular_vector_coefficient F T).re
  have hj := ((Lp.memLp F).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)).const_mul c
  have h := integral_mono_ae hi hj hle
  rw [integral_const_mul,regular_integral_norm_sq,hF,one_pow,mul_one] at h
  exact (not_le_of_gt hc) h

variable {M : VonNeumannAlgebra H} {Ω : H}

namespace ModularSpectralResolution

variable (S : ModularSpectralResolution M Ω)

theorem exists_packet_localized_vector_gt
    (ψ : (H →L[ℂ] H) →L[ℂ] ℂ) (hψ : IsState ψ)
    (hinv : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : H →L[ℂ] H),
      ψ (stateActionAverage S.group S.continuous μ T)=ψ T)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) {c : ℝ} (hc : c < (ψ T).re)
    (φ : Lp ℂ 2 (volume : Measure ℝ)) (hφ : ‖φ‖=1) (a b : ℝ)
    (hlo : regularFrequencyProjection a φ=φ) (hhi : regularFrequencyProjection b φ=0) :
    ∃ (s : ℝ) (ξ : H), ξ ≠ 0 ∧
      S.upperCut (a-2*Real.pi*s) ξ=ξ ∧ S.upperCut (b-2*Real.pi*s) ξ=0 ∧
      c*‖ξ‖^2 < (inner ℂ ξ (T ξ)).re := by
  have hvalue : c < (ψ (scalarPacketAverage S.group S.continuous φ hφ T)).re := by
    rwa [scalarPacketAverage_strongly_invariant S.group S.continuous ψ hinv]
  obtain ⟨η,hη,hηT⟩ := exists_vector_state_gt ψ hψ _
    (scalarPacketAverage_selfAdjoint S.group S.continuous φ hφ T hT) hvalue
  have hnorm : ‖S.fourierPacket φ η‖=1 := by rw [S.norm_fourierPacket,hφ,hη,one_mul]
  have hint : c < ∫ s : ℝ,
      (inner ℂ (S.fourierPacket φ η s) (T (S.fourierPacket φ η s))).re := by
    rwa [S.fourierPacket_coefficient_re φ hφ]
  have hsupport := (S.fourierPacket_lower_support a φ hlo η).and
    (S.fourierPacket_upper_support b φ hhi η)
  obtain ⟨s,hs,hgt⟩ := exists_packet_fiber_gt _ hnorm T hint _ hsupport
  refine ⟨s,S.fourierPacket φ η s,?_,hs.1,hs.2,hgt⟩
  intro hz
  simp only [hz,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),mul_zero,
    map_zero,inner_zero_left,Complex.zero_re,lt_self_iff_false] at hgt

theorem exists_short_spectral_vector_gt
    (ψ : (H →L[ℂ] H) →L[ℂ] ℂ) (hψ : IsState ψ)
    (hinv : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : H →L[ℂ] H),
      ψ (stateActionAverage S.group S.continuous μ T)=ψ T)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) {c : ℝ} (hc : c < (ψ T).re)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (r : ℝ) (ξ : H), ξ ≠ 0 ∧ S.upperCut r ξ=ξ ∧ S.upperCut (r+δ) ξ=0 ∧
      c*‖ξ‖^2 < (inner ℂ ξ (T ξ)).re := by
  obtain ⟨φ,hφ,hlo,hhi⟩ := exists_short_frequency_scalar hδ
  obtain ⟨s,ξ,hξ,hl,hh,hgt⟩ := S.exists_packet_localized_vector_gt ψ hψ hinv T hT hc φ hφ 0 δ hlo hhi
  refine ⟨-2*Real.pi*s,ξ,hξ,?_,?_,hgt⟩
  · simpa only [zero_sub, neg_mul] using hl
  · simpa only [sub_eq_add_neg, neg_mul, add_comm] using hh

end ModularSpectralResolution

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularUnitPacketSelection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Unit-vector form of modular packet separation -/

namespace KadisonKastler

open MeasureTheory NaimarkZFC

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

namespace ModularSpectralResolution

variable (S : ModularSpectralResolution M Ω)

theorem exists_short_spectral_unit_vector_gt
    (ψ : (H →L[ℂ] H) →L[ℂ] ℂ) (hψ : IsState ψ)
    (hinv : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : H →L[ℂ] H),
      ψ (stateActionAverage S.group S.continuous μ T)=ψ T)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) {c : ℝ} (hc : c < (ψ T).re)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (r : ℝ) (ξ : H), ‖ξ‖=1 ∧ S.upperCut r ξ=ξ ∧ S.upperCut (r+δ) ξ=0 ∧
      c < (inner ℂ ξ (T ξ)).re := by
  obtain ⟨r,η,hη,hlo,hhi,hgt⟩ := S.exists_short_spectral_vector_gt ψ hψ hinv T hT hc hδ
  have hn : 0 < ‖η‖ := norm_pos_iff.mpr hη
  let ξ : H := (((‖η‖⁻¹ : ℝ) : ℂ)) • η
  refine ⟨r,ξ,?_,?_,?_,?_⟩
  · change ‖(((‖η‖⁻¹ : ℝ) : ℂ)) • η‖=1
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),
      inv_mul_cancel₀ hn.ne']
  · change S.upperCut r ((((‖η‖⁻¹ : ℝ) : ℂ)) • η)=_
    rw [map_smul,hlo]
  · change S.upperCut (r+δ) ((((‖η‖⁻¹ : ℝ) : ℂ)) • η)=0
    rw [map_smul,hhi,smul_zero]
  · have he : (inner ℂ ξ (T ξ)).re=‖η‖⁻¹^2*(inner ℂ η (T η)).re := by
      change (inner ℂ (((‖η‖⁻¹ : ℝ) : ℂ) • η)
        (T (((‖η‖⁻¹ : ℝ) : ℂ) • η))).re=_
      rw [map_smul,inner_smul_left,inner_smul_right]
      change (star ((‖η‖⁻¹ : ℝ) : ℂ)*
        (((‖η‖⁻¹ : ℝ) : ℂ)*inner ℂ η (T η))).re=_
      simp only [Complex.star_def,Complex.conj_ofReal,Complex.mul_re,Complex.ofReal_re,
        Complex.ofReal_im,zero_mul,sub_zero]
      ring
    rw [he]
    have hm := mul_lt_mul_of_pos_left hgt (sq_pos_of_pos (inv_pos.mpr hn))
    have hi : ‖η‖⁻¹^2*‖η‖^2=1 := by rw [← mul_pow,inv_mul_cancel₀ hn.ne']; norm_num
    have heq : ‖η‖⁻¹^2*(c*‖η‖^2)=c := by
      calc
        _ = c*(‖η‖⁻¹^2*‖η‖^2) := by ring
        _ = c := by rw [hi,mul_one]
    rwa [heq] at hm

end ModularSpectralResolution

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_VectorQuadraticContinuity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Uniform continuity of quadratic coefficients near a unit vector -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem vector_quadratic_sub_le (T : H →L[ℂ] H) (v w : H) :
    ‖inner ℂ v (T v)-inner ℂ w (T w)‖ ≤ ‖T‖*(‖v‖+‖w‖)*‖v-w‖ := by
  have he : inner ℂ v (T v)-inner ℂ w (T w) =
      inner ℂ (v-w) (T v)+inner ℂ w (T (v-w)) := by
    rw [inner_sub_left,map_sub,inner_sub_right]
    abel
  rw [he]
  calc
    _ ≤ ‖inner ℂ (v-w) (T v)‖+‖inner ℂ w (T (v-w))‖ := norm_add_le _ _
    _ ≤ ‖v-w‖*‖T v‖+‖w‖*‖T (v-w)‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖v-w‖*(‖T‖*‖v‖)+‖w‖*(‖T‖*‖v-w‖) :=
      add_le_add (mul_le_mul_of_nonneg_left (T.le_opNorm v) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (T.le_opNorm (v-w)) (norm_nonneg _))
    _ = _ := by ring

theorem vector_quadratic_error_le_of_unit (T : H →L[ℂ] H) (v w : H)
    (hw : ‖w‖=1) {ε : ℝ} (hε : ε ≤ 1) (hv : ‖v-w‖ ≤ ε) :
    ‖inner ℂ v (T v)-inner ℂ w (T w)‖ ≤ 3*‖T‖*ε := by
  have hvnorm : ‖v‖ ≤ 2 := by
    have hh := norm_le_norm_sub_add v w
    rw [hw] at hh
    linarith
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hv
  calc
    _ ≤ ‖T‖*(‖v‖+‖w‖)*‖v-w‖ := vector_quadratic_sub_le T v w
    _ ≤ ‖T‖*(2+1)*ε := by
      rw [hw]
      gcongr
    _ = _ := by ring

theorem vector_quadratic_gt_of_near_unit (T : H →L[ℂ] H) (v w : H)
    (hw : ‖w‖=1) {ε c c' : ℝ} (hε : ε ≤ 1) (hv : ‖v-w‖ ≤ ε)
    (hc : c' < (inner ℂ w (T w)).re) (hsmall : 3*‖T‖*ε < c'-c) :
    c < (inner ℂ v (T v)).re := by
  have hh := vector_quadratic_error_le_of_unit T v w hw hε hv
  have hr : |(inner ℂ v (T v)).re-(inner ℂ w (T w)).re| ≤ 3*‖T‖*ε := by
    have hb := (Complex.abs_re_le_norm (inner ℂ v (T v)-inner ℂ w (T w))).trans hh
    exact hb
  have hlow := (abs_le.mp hr).1
  linarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularAlgebraicSeparation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Strict state tests detected by approximate modular eigenvectors

This is the separation consequence needed from the approximate-eigenstate
argument. All spectral, packet and algebraic approximations are constructed.
-/

namespace KadisonKastler

open MeasureTheory NaimarkZFC

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

theorem exists_algebraic_modular_test
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (d : ModularConjugationData M Ω)
    (hd : d.conjugation=tomitaPolarConjugation J Ω hsep hcyc)
    (S : ModularSpectralResolution M Ω)
    (hcuts : ∀ r, S.upperCut r=modularUpperCut M J Ω r)
    (ψ : (H →L[ℂ] H) →L[ℂ] ℂ) (hψ : IsState ψ)
    (hinv : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : H →L[ℂ] H),
      ψ (stateActionAverage S.group S.continuous μ T)=ψ T)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) {c : ℝ} (hc : c < (ψ T).re)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (a : Algebra M) (q : ℝ) (ξ : H), 0 < q ∧ ‖ξ‖=1 ∧
      c < (inner ℂ ξ (T ξ)).re ∧ ‖a.val Ω-ξ‖ < ε ∧
      ‖((q : ℂ)⁻¹) • d.rightAction a Ω-ξ‖ < ε := by
  let δ := Real.log (1+ε/2)
  have hδ : 0 < δ := Real.log_pos (by linarith)
  have hexp : Real.exp δ-1=ε/2 := by
    rw [Real.exp_log (by positivity)]
    ring
  obtain ⟨r,ξ,hξ,hlo,hhi,hgt⟩ := S.exists_short_spectral_unit_vector_gt ψ hψ hinv T hT hc hδ
  rw [hcuts] at hlo hhi
  obtain ⟨a,q,hq,ha,hb⟩ := modular_localized_algebra_approximate J hsep hcyc d hd ξ
    hδ.le hlo hhi (show 0 < ε/4 by positivity)
  rw [hexp,hξ,mul_one] at ha hb
  exact ⟨a,q,ξ,hq,hξ,hgt,ha.trans_le (by linarith),hb.trans_le (by linarith)⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModularAlgebraicTestValues
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.matrixClosureVectorTrace_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.KadisonSimilarity.tracialInclusionIsometry_vector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Both approximate eigenvector coordinates retain the strict test -/

namespace KadisonKastler

open MeasureTheory NaimarkZFC

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} {Ω : H}

theorem exists_algebraic_modular_test_values_oai
    (J : H ≃ₗᵢ⋆[ℂ] H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (hcyc : DenseRange (algebraVectorMap M Ω))
    (d : ModularConjugationData M Ω)
    (hd : d.conjugation=tomitaPolarConjugation J Ω hsep hcyc)
    (S : ModularSpectralResolution M Ω)
    (hcuts : ∀ r, S.upperCut r=modularUpperCut M J Ω r)
    (ψ : (H →L[ℂ] H) →L[ℂ] ℂ) (hψ : IsState ψ)
    (hinv : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (T : H →L[ℂ] H),
      ψ (stateActionAverage S.group S.continuous μ T)=ψ T)
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) {c : ℝ} (hc : c < (ψ T).re)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (a : Algebra M) (q : ℝ) (ξ : H), 0 < q ∧ ‖ξ‖=1 ∧
      ‖a.val Ω-ξ‖ < ε ∧ ‖((q : ℂ)⁻¹) • d.rightAction a Ω-ξ‖ < ε ∧
      c < (inner ℂ (a.val Ω) (T (a.val Ω))).re ∧
      c < (inner ℂ (((q : ℂ)⁻¹) • d.rightAction a Ω)
        (T (((q : ℂ)⁻¹) • d.rightAction a Ω))).re := by
  let c' := (c+(ψ T).re)/2
  have hc' : c < c' := by dsimp [c'] <;> linarith
  have hcψ : c' < (ψ T).re := by dsimp [c'] <;> linarith
  obtain ⟨η,hη,hsmall⟩ := exists_pos_mul_lt (sub_pos.mpr hc') (3*‖T‖)
  let γ := min η (min 1 ε)
  have hγ : 0 < γ := lt_min hη (lt_min zero_lt_one hε)
  have hγ1 : γ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hγε : γ ≤ ε := (min_le_right _ _).trans (min_le_right _ _)
  have hγsmall : 3*‖T‖*γ < c'-c :=
    (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)).trans_lt hsmall
  obtain ⟨a,q,ξ,hq,hξ,hvalue,ha,hb⟩ :=
    exists_algebraic_modular_test J hsep hcyc d hd S hcuts ψ hψ hinv T hT hcψ hγ
  exact ⟨a,q,ξ,hq,hξ,ha.trans_le hγε,hb.trans_le hγε,
    vector_quadratic_gt_of_near_unit T _ ξ hξ hγ1 ha.le hvalue hγsmall,
    vector_quadratic_gt_of_near_unit T _ ξ hξ hγ1 hb.le hvalue hγsmall⟩

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.exists_algebraic_modular_test_values_oai.{u_1} := @OAI.KadisonKastler.exists_algebraic_modular_test_values_oai.{u_1}
