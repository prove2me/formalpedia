-- Prove2me | solution 1 for OAI.KadisonKastler.expectedMatrixSubfactorModel_of_projection_cuts_with_gap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T19:08:54.479075+00:00
-- url     : https://prove2.me/submissions/a69491b6-bfea-4d42-8fde-09ce5e64244f

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.End
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
import Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart
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
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
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
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
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
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Nat
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Sum
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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.NumberTheory.Real.Irrational
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
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
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
import Theorems.Thm_OAI_KadisonKastler_expectedMatrixSubfactorModel_of_supported_central_line

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProjectionNormDecomposition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem projection_apply_norm_le {P : H →L[ℂ] H} (hP : IsStarProjection P) (x : H) :
    ‖P x‖ ≤ ‖x‖ := by
  simpa only [one_mul] using P.le_of_opNorm_le (hP.norm_le P) x

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

theorem nested_projection_norm_sq_eq {P R : H →L[ℂ] H}
    (hP : IsStarProjection P) (hPR : P * R = P) (x : H) :
    ‖P x‖ ^ 2 + ‖(R - P) x‖ ^ 2 = ‖R x‖ ^ 2 := by
  have hs : P.adjoint = P := by
    simpa only [ContinuousLinearMap.star_eq_adjoint] using hP.isSelfAdjoint.star_eq
  have hz : P * (R - P) = 0 := by
    rw [mul_sub, hPR, hP.isIdempotentElem.eq, sub_self]
  have hi : inner ℂ (P x) ((R - P) x) = 0 := by
    rw [← P.adjoint_inner_right, hs]
    change inner ℂ x ((P * (R - P)) x) = 0
    rw [hz, zero_apply, inner_zero_right]
  calc
    _ = ‖P x + (R - P) x‖ ^ 2 := by
      simpa only [pow_two] using
        (norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hi).symm
    _ = ‖R x‖ ^ 2 := by simp

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
-- module Solutions.OAIQ075_KS.KadisonKastler_CentralProjectionEnergy
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A commutator gap forces contraction of the central-vector projection -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem centralProjection_pairedCut (K : Submodule ℂ H) [CompleteSpace K]
    {p q : H →L[ℂ] H} (hp : IsStarProjection p) (hq : IsStarProjection q) (hc : Commute p q)
    (hK : ∀ x ∈ K, p x = q x) (ξ : H) :
    K.starProjection (pairedProjectionCut p q ξ) = K.starProjection ξ := by
  let Q := pairedProjectionCut p q
  have hQ := pairedProjectionCut_isProjection hp hq hc
  have hfix (x : H) (hx : x ∈ K) : Q x = x := by
    have hd : (p - q) x = 0 := by simpa only [sub_apply,sub_eq_zero] using hK x hx
    have hzero : ((p - q) * (p - q)) x = 0 := by rw [mul_apply_eq_comp,hd,map_zero]
    rw [pairedProjectionCut_complement hp hq hc] at hzero
    change x - Q x = 0 at hzero
    exact (sub_eq_zero.mp hzero).symm
  have he : K.starProjection (Q ξ) = K.starProjection ξ := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
      (K.starProjection_apply_mem ξ)
    intro w hw
    rw [inner_sub_left]
    have hs : Q.adjoint = Q := hQ.isSelfAdjoint.star_eq
    rw [← Q.adjoint_inner_right,hs,hfix w hw]
    simpa only [inner_sub_left] using K.starProjection_inner_eq_zero ξ w hw
  exact he

theorem centralProjection_energy_le (K : Submodule ℂ H) [CompleteSpace K]
    {p q : H →L[ℂ] H} (hp : IsStarProjection p) (hq : IsStarProjection q) (hc : Commute p q)
    (hK : ∀ x ∈ K, p x = q x) (ξ : H) :
    ‖K.starProjection ξ‖ ^ 2 + ‖(p - q) ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by
  have hn : ‖K.starProjection ξ‖ ≤ ‖pairedProjectionCut p q ξ‖ := by
    rw [← centralProjection_pairedCut K hp hq hc hK ξ]
    exact K.norm_starProjection_apply_le _
  have he := pairedProjectionCut_energy hp hq hc ξ
  nlinarith [norm_nonneg (K.starProjection ξ),norm_nonneg (pairedProjectionCut p q ξ)]

theorem centralProjection_contraction_of_gap (K : Submodule ℂ H) [CompleteSpace K]
    {p q : H →L[ℂ] H} (hp : IsStarProjection p) (hq : IsStarProjection q) (hc : Commute p q)
    (hK : ∀ x ∈ K, p x = q x) (ξ : H) (γ : ℝ)
    (hgap : γ * ‖ξ‖ ^ 2 ≤ ‖(p - q) ξ‖ ^ 2) :
    ‖K.starProjection ξ‖ ^ 2 ≤ (1 - γ) * ‖ξ‖ ^ 2 := by
  have he := centralProjection_energy_le K hp hq hc hK ξ
  nlinarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CentralVectorSpace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Central vectors and the relative commutant

The central-vector space used in Haagerup's construction is a closed
complex subspace. A one-dimensional central-vector space detects an
irreducible inclusion once its generating vector is separating.
-/

namespace KadisonKastler

open UltrapowerBridge

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {N P M : VonNeumannAlgebra H}

theorem centralVectorSpace_antitone (hNP : N ≤ P) (J : H ≃ₗᵢ⋆[ℂ] H) :
    centralVectorSpace P J ≤ centralVectorSpace N J := by
  intro ξ hξ a
  exact hξ (StarSubalgebra.inclusion hNP a)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixCentralVectorTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Matrix-unit tests for central vectors -/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem mem_centralVectorSpace_matrix_iff
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : MatrixUnitSystem ι (Algebra M)) (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) :
    ξ ∈ centralVectorSpace (matrixUnitConcreteAlgebra E) J ↔
      ∀ i j, (E.entry i j).val ξ = conjugationOperator J (star (E.entry i j).val) ξ := by
  constructor
  · intro h i j
    exact h ((concreteMatrixUnits E).entry i j)
  · intro h a
    obtain ⟨b,hb⟩ := a.property
    have hentry (i j : ι) : (E.entry i j).val ξ = rightVectorLinear J ξ (E.entry i j).val :=
      h i j
    change a.val ξ = rightVectorLinear J ξ a.val
    rw [← hb]
    change (E.concreteHom b) ξ = rightVectorLinear J ξ (E.concreteHom b)
    rw [show E.concreteHom b = ∑ i, ∑ j, b i j • (E.entry i j).val by
      change M.toStarSubalgebra.subtype (E.hom b) = _
      simp only [MatrixUnitSystem.hom_apply, map_sum, map_smul]
      rfl]
    simp only [map_sum, map_smul, sum_apply, smul_apply]
    simp_rw [hentry]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DecreasingHilbertProjections
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The strong limit of decreasing Hilbert projections

The squared norms decrease. Their Cauchy estimate identifies the strong
limit with projection onto the intersection, as needed for central vectors.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Decreasing closed subspaces have strongly convergent projections. -/
theorem decreasing_projection_limit (K : ℕ → Submodule ℂ H)
    [∀ n, CompleteSpace (K n)] (hK : Antitone K) (ξ : H) :
    ∃ η : H, (∀ n, η ∈ K n) ∧
      Tendsto (fun n => (K n).starProjection ξ) atTop (𝓝 η) ∧
      ∀ w : H, (∀ n, w ∈ K n) → inner ℂ (ξ - η) w = 0 := by
  let P (n : ℕ) : H →L[ℂ] H := (K n).starProjection
  have hP (n : ℕ) : IsStarProjection (P n) :=
    ⟨Submodule.isIdempotentElem_starProjection _, isSelfAdjoint_starProjection _⟩
  have hnest {m n : ℕ} (hmn : m ≤ n) : P n * P m = P n :=
    Submodule.starProjection_comp_starProjection_of_le (hK hmn)
  let f (n : ℕ) : ℝ := ‖P n ξ‖ ^ 2
  have hid {m n : ℕ} (hmn : m ≤ n) :
      f n + ‖P m ξ - P n ξ‖ ^ 2 = f m := by
    simpa only [sub_apply] using nested_projection_norm_sq_eq (hP n) (hnest hmn) ξ
  have hf : Antitone f := by
    intro m n hmn
    have h := hid hmn
    linarith [sq_nonneg ‖P m ξ - P n ξ‖]
  have ht : Tendsto f atTop (𝓝 (⨅ n, f n)) :=
    tendsto_atTop_ciInf hf ⟨0, by rintro _ ⟨n,rfl⟩; exact sq_nonneg _⟩
  have hc := ht.cauchySeq
  have hpc : CauchySeq (fun n => P n ξ) := by
    rw [Metric.cauchySeq_iff] at hc ⊢
    intro ε hε
    obtain ⟨k,hk⟩ := hc (ε ^ 2) (sq_pos_of_pos hε)
    have hb (m n : ℕ) (hm : k ≤ m) (hn : k ≤ n) (hmn : m ≤ n) :
        dist (P m ξ) (P n ξ) < ε := by
      have hd := hk m hm n hn
      have he := hid hmn
      rw [Real.dist_eq] at hd
      rw [dist_eq_norm]
      nlinarith [le_abs_self (f m - f n), norm_nonneg (P m ξ - P n ξ)]
    refine ⟨k,fun m hm n hn => ?_⟩
    rcases le_total m n with h | h
    · exact hb m n hm hn h
    · simpa only [dist_comm] using hb n m hn hm h
  obtain ⟨η,hη⟩ := cauchySeq_tendsto_of_complete hpc
  refine ⟨η, ?_, hη, ?_⟩
  · intro n
    have hclosed : IsClosed (K n : Set H) :=
      (completeSpace_coe_iff_isComplete.mp (inferInstance : CompleteSpace (K n))).isClosed
    apply hclosed.mem_of_tendsto hη
    filter_upwards [eventually_ge_atTop n] with m hm
    exact hK hm (Submodule.starProjection_apply_mem _ _)
  · intro w hw
    have hi : Tendsto (fun n => inner ℂ (ξ - P n ξ) w) atTop
        (𝓝 (inner ℂ (ξ - η) w)) :=
      ((tendsto_const_nhds.sub hη).inner tendsto_const_nhds)
    have hz (n : ℕ) : inner ℂ (ξ - P n ξ) w = 0 :=
      Submodule.starProjection_inner_eq_zero ξ w (hw n)
    exact tendsto_nhds_unique hi (by simpa only [hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0)))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CentralVectorMatrixLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Central vectors of an increasing matrix sequence

The decreasing central-vector projections have an actual strong limit.
When their common range is a separating line, the state and commutant
identities supply the exact expected-subfactor model.
-/

namespace KadisonKastler

open Generator Generator.Tracial UltrapowerBridge Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem matrixCentralVectorSpace_le
    (A : ℕ → FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H) (n : ℕ) :
    matrixCentralVectorSpace A J ≤ centralVectorSpace (matrixUnitConcreteAlgebra (A n).units) J :=
  iInf_le _ n

theorem matrixCentralVectorSpace_tendsto
    (A : ℕ → FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) :
    Tendsto (fun n => (centralVectorSpace (matrixUnitConcreteAlgebra (A n).units) J).starProjection ξ)
      atTop (𝓝 ((matrixCentralVectorSpace A J).starProjection ξ)) := by
  have hanti : Antitone (fun n => centralVectorSpace (matrixUnitConcreteAlgebra (A n).units) J) := by
    intro m n hmn
    apply centralVectorSpace_antitone
    exact hA hmn
  obtain ⟨η,hη,ht,ho⟩ := decreasing_projection_limit _ hanti ξ
  have hm : η ∈ matrixCentralVectorSpace A J := (Submodule.mem_iInf _).mpr hη
  have he : (matrixCentralVectorSpace A J).starProjection ξ = η :=
    Submodule.eq_starProjection_of_mem_of_inner_eq_zero hm
      (fun w hw => ho w ((Submodule.mem_iInf _).mp hw))
  rwa [he]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CentralLineApproximation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Dense finite tests force a central line

The finite-dimensional refinement estimates pass through the projection
onto the common central-vector space. Vanishing errors on a dense family
then force its entire range into a single line.
-/

namespace KadisonKastler

open Generator Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem projection_range_line_of_dense_tests
    (K : Submodule ℂ H) [CompleteSpace K]
    (L : ℕ → Submodule ℂ H) [∀ n, CompleteSpace (L n)]
    (hKL : ∀ n, K ≤ L n) (ξ : H) (η : ℕ → H) (hdense : DenseRange η)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (htest : ∀ n i, i ≤ n → ∃ c : ℂ,
      ‖(L n).starProjection (η i) - c • (L n).starProjection ξ‖ ≤ ε n) :
    K ≤ Submodule.span ℂ {K.starProjection ξ} := by
  let S := Submodule.span ℂ {K.starProjection ξ}
  have hS : IsClosed (S : Set H) := S.closed_of_finiteDimensional
  have htest' (i : ℕ) : K.starProjection (η i) ∈ S := by
    apply closure_minimal (fun _ h => h) hS
    apply Metric.mem_closure_iff.mpr
    intro δ hδ
    obtain ⟨n,hn,hi⟩ := ((hε.eventually (gt_mem_nhds hδ)).and
      (eventually_ge_atTop i)).exists
    obtain ⟨c,hc⟩ := htest n i hi
    refine ⟨c • K.starProjection ξ, S.smul_mem c (Submodule.subset_span (by simp)), ?_⟩
    have hcomp : K.starProjection ∘L (L n).starProjection = K.starProjection :=
      Submodule.starProjection_comp_starProjection_of_le (hKL n)
    have he : K.starProjection ((L n).starProjection (η i) -
        c • (L n).starProjection ξ) = K.starProjection (η i) - c • K.starProjection ξ := by
      rw [map_sub, map_smul]
      have h1 := congrArg (fun T : H →L[ℂ] H => T (η i)) hcomp
      have h2 := congrArg (fun T : H →L[ℂ] H => T ξ) hcomp
      change K.starProjection ((L n).starProjection (η i)) = K.starProjection (η i) at h1
      change K.starProjection ((L n).starProjection ξ) = K.starProjection ξ at h2
      rw [h1,h2]
    rw [dist_eq_norm, ← he]
    exact ((K.norm_starProjection_apply_le _).trans hc).trans_lt hn
  have hclosed : IsClosed {x : H | K.starProjection x ∈ S} := hS.preimage K.starProjection.continuous
  have hall (x : H) : K.starProjection x ∈ S :=
    (closure_minimal (by rintro _ ⟨i,rfl⟩; exact htest' i) hclosed) (hdense x)
  intro x hx
  have h := hall x
  rwa [Submodule.starProjection_eq_self_iff.mpr hx] at h

variable {M : VonNeumannAlgebra H}

/-- The finite central-vector tests used in the refinement construction
force the common central-vector space to be a line. -/
theorem matrixCentralVectorSpace_le_line_of_dense_tests
    (A : ℕ → FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H)
    (ξ : H) (η : ℕ → H) (hdense : DenseRange η)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (htest : ∀ n i, i ≤ n → ∃ c : ℂ,
      ‖(centralVectorSpace (matrixUnitConcreteAlgebra (A n).units) J).starProjection (η i) -
        c • (centralVectorSpace (matrixUnitConcreteAlgebra (A n).units) J).starProjection ξ‖ ≤ ε n) :
    matrixCentralVectorSpace A J ≤
      Submodule.span ℂ {(matrixCentralVectorSpace A J).starProjection ξ} :=
  projection_range_line_of_dense_tests _ _ (matrixCentralVectorSpace_le A J) ξ η hdense ε hε htest

/-- The displacement bound survives the strong projection limit. -/
theorem matrixCentralVectorSpace_displacement_le
    (A : ℕ → FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) (δ : ℝ)
    (hδ : ∀ n,
      ‖ξ - (centralVectorSpace (matrixUnitConcreteAlgebra (A n).units) J).starProjection ξ‖ ≤ δ) :
    ‖ξ - (matrixCentralVectorSpace A J).starProjection ξ‖ ≤ δ :=
  le_of_tendsto (tendsto_const_nhds.sub (matrixCentralVectorSpace_tendsto A hA J ξ)).norm
    (Eventually.of_forall hδ)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixCentralRefinement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.centralRefinementIterates_succ _root_.OAI.KadisonKastler.centralRefinementIterates_zero _root_.OAI.KadisonSimilarity.concreteStageEquiv_apply _root_.OAI.KadisonSimilarity.generatedMatrixVector_apply _root_.OAI.KadisonSimilarity.generatedStageEmbedding_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Passing central-vector refinement estimates to finite families

Further matrix refinement preserves every previous distance-to-line
estimate. Repeated one-vector refinement therefore handles any finite
family with a prescribed total displacement budget.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem matrixStageCentralProjection_error_mono (E F : FiniteMatrixStage M)
    (hEF : E.units.concreteAlgebra ≤ F.units.concreteAlgebra)
    (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H) (c : ℂ) :
    ‖matrixStageCentralProjection F J η - c • matrixStageCentralProjection F J ξ‖ ≤
      ‖matrixStageCentralProjection E J η - c • matrixStageCentralProjection E J ξ‖ := by
  let K := centralVectorSpace (matrixUnitConcreteAlgebra F.units) J
  have hcomp : K.starProjection ∘L matrixStageCentralProjection E J = K.starProjection :=
    Submodule.starProjection_comp_starProjection_of_le (centralVectorSpace_antitone hEF J)
  have he (x : H) : K.starProjection (matrixStageCentralProjection E J x) =
      matrixStageCentralProjection F J x :=
    congrArg (fun T : H →L[ℂ] H => T x) hcomp
  calc
    _ = ‖K.starProjection (matrixStageCentralProjection E J η -
        c • matrixStageCentralProjection E J ξ)‖ := by rw [map_sub,map_smul,he,he]
    _ ≤ _ := K.norm_starProjection_apply_le _

theorem exists_finite_central_refinement
    (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H)
    (hstep : ∀ (E : FiniteMatrixStage M) (η : H) (δ ε : ℝ), 0 < δ → 0 < ε →
      ∃ F : FiniteMatrixStage M, E.units.concreteAlgebra ≤ F.units.concreteAlgebra ∧
        ‖matrixStageCentralProjection E J ξ - matrixStageCentralProjection F J ξ‖ ≤ δ ∧
        ∃ c : ℂ, ‖matrixStageCentralProjection F J η -
          c • matrixStageCentralProjection F J ξ‖ ≤ ε)
    (η : ℕ → H) (n : ℕ) (E : FiniteMatrixStage M) (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ F : FiniteMatrixStage M, E.units.concreteAlgebra ≤ F.units.concreteAlgebra ∧
      ‖matrixStageCentralProjection E J ξ - matrixStageCentralProjection F J ξ‖ ≤ δ ∧
      ∀ i < n, ∃ c : ℂ, ‖matrixStageCentralProjection F J (η i) -
        c • matrixStageCentralProjection F J ξ‖ ≤ ε := by
  induction n generalizing E δ with
  | zero => exact ⟨E,le_rfl,by simpa using hδ.le,by simp⟩
  | succ n ih =>
    obtain ⟨F,hEF,hδF,hF⟩ := ih E (δ / 2) (half_pos hδ)
    obtain ⟨G,hFG,hδG,c,hc⟩ := hstep F (η n) (δ / 2) ε (half_pos hδ) hε
    refine ⟨G,hEF.trans hFG,?_,?_⟩
    · exact (norm_sub_le_norm_sub_add_norm_sub (matrixStageCentralProjection E J ξ)
        (matrixStageCentralProjection F J ξ) (matrixStageCentralProjection G J ξ)).trans
        ((add_le_add hδF hδG).trans_eq (add_halves δ))
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · obtain ⟨b,hb⟩ := hF i hi
        exact ⟨b,(matrixStageCentralProjection_error_mono F G hFG J ξ (η i) b).trans hb⟩
      · exact ⟨c,hc⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixProjectionCut
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A spectral cut supplies the matrix central-vector contraction

A matrix subalgebra containing the cut lies inside its diagonal
central-vector space. The exact discarded-energy identity therefore
gives the contraction estimate used in Haagerup's Lemma 3.6.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem matrixStageCentralProjection_contraction
    (E : FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hright : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (p : AlgebraProjection M) (hmem : p.val.val ∈ E.units.concreteAlgebra)
    (η : H) (γ : ℝ)
    (hgap : γ * ‖η‖ ^ 2 ≤ ‖p.val.val η - conjugationOperator J p.val.val η‖ ^ 2) :
    ‖matrixStageCentralProjection E J η‖ ^ 2 ≤ (1 - γ) * ‖η‖ ^ 2 := by
  let K := centralVectorSpace (matrixUnitConcreteAlgebra E.units) J
  have hp : IsStarProjection p.val.val := p.property.map M.toStarSubalgebra.subtype
  have hq : IsStarProjection (conjugationOperator J p.val.val) :=
    (conjugateAlgebraProjection M M.commutant J hJ hright p).property.map
      M.commutant.toStarSubalgebra.subtype
  have hc : Commute p.val.val (conjugationOperator J p.val.val) :=
    VonNeumannAlgebra.mem_commutant_iff.mp (hright p.val) p.val.val p.val.property
  have hK (ξ : H) (hξ : ξ ∈ K) : p.val.val ξ = conjugationOperator J p.val.val ξ := by
    have h := hξ (⟨p.val.val,hmem⟩ : Algebra (matrixUnitConcreteAlgebra E.units))
    change p.val.val ξ = conjugationOperator J (star p.val.val) ξ at h
    rwa [hp.isSelfAdjoint.star_eq] at h
  exact centralProjection_contraction_of_gap K hp hq hc hK η γ hgap

theorem centralProjection_displacement_le_of_central_vector
    (K : Submodule ℂ H) [CompleteSpace K] (ξ ζ : H) (hζ : ζ ∈ K) :
    ‖ξ - K.starProjection ξ‖ ≤ ‖ξ - ζ‖ := by
  have hp := isStarProjection_starProjection (U := K)
  have he : (1 - K.starProjection) (ξ - ζ) = ξ - K.starProjection ξ := by
    simp only [map_sub,sub_apply,one_apply_eq_self,
      Submodule.starProjection_eq_self_iff.mpr hζ,sub_self,sub_zero]
  rw [← he]
  exact projection_apply_norm_le hp.one_sub (ξ - ζ)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixCentralResidual
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The part of a matrix-central vector orthogonal to the reference line -/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem matrixCentralResidual_coefficient
    (E : FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H) :
    ∃ c : ℂ, matrixCentralResidual E J ξ η =
      matrixStageCentralProjection E J η - c • matrixStageCentralProjection E J ξ := by
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp
    ((Submodule.span ℂ {matrixStageCentralProjection E J ξ}).starProjection_apply_mem
      (matrixStageCentralProjection E J η))
  exact ⟨c,by rw [matrixCentralResidual,← hc]⟩

theorem matrixCentralResidual_mem
    (E : FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H) :
    matrixCentralResidual E J ξ η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E.units) J := by
  obtain ⟨c,hc⟩ := matrixCentralResidual_coefficient E J ξ η
  rw [hc]
  exact Submodule.sub_mem _ (Submodule.starProjection_apply_mem _ _)
    (Submodule.smul_mem _ c (Submodule.starProjection_apply_mem _ _))

theorem matrixCentralResidual_orthogonal
    (E : FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H) :
    inner ℂ (matrixCentralResidual E J ξ η) (matrixStageCentralProjection E J ξ) = 0 :=
  (Submodule.span ℂ {matrixStageCentralProjection E J ξ}).starProjection_inner_eq_zero
    _ _ (Submodule.mem_span_singleton_self _)

theorem matrixCentralResidual_norm_le
    (E : FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H) (c : ℂ) :
    ‖matrixCentralResidual E J ξ η‖ ≤
      ‖matrixStageCentralProjection E J η - c • matrixStageCentralProjection E J ξ‖ :=
  centralProjection_displacement_le_of_central_vector
    (Submodule.span ℂ {matrixStageCentralProjection E J ξ}) _ _
    (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _))

theorem matrixCentralResidual_refinement_le
    (E F : FiniteMatrixStage M) (hEF : E.units.concreteAlgebra ≤ F.units.concreteAlgebra)
    (J : H ≃ₗᵢ⋆[ℂ] H) (ξ η : H) :
    ‖matrixCentralResidual F J ξ η‖ ≤
      ‖matrixStageCentralProjection F J (matrixCentralResidual E J ξ η)‖ := by
  obtain ⟨c,hc⟩ := matrixCentralResidual_coefficient E J ξ η
  have hcomp : matrixStageCentralProjection F J ∘L matrixStageCentralProjection E J =
      matrixStageCentralProjection F J :=
    Submodule.starProjection_comp_starProjection_of_le (centralVectorSpace_antitone hEF J)
  have he (x : H) : matrixStageCentralProjection F J (matrixStageCentralProjection E J x) =
      matrixStageCentralProjection F J x :=
    congrArg (fun T : H →L[ℂ] H => T x) hcomp
  rw [hc,map_sub,map_smul,he,he]
  exact matrixCentralResidual_norm_le F J ξ η c

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CentralContractionIteration
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.centralRefinementIterates_succ _root_.OAI.KadisonKastler.centralRefinementIterates_zero _root_.OAI.KadisonKastler.centralSpaceConjugation_coe _root_.OAI.KadisonSimilarity.concreteStageEquiv_apply _root_.OAI.KadisonSimilarity.generatedMatrixVector_apply _root_.OAI.KadisonSimilarity.generatedStageEmbedding_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A fixed contraction gives arbitrary one-vector refinement

The reference vector may move by a summable prescribed amount. Each
step contracts only the residual orthogonal to its current central line;
projection onto the new line can only improve that estimate.
-/

namespace KadisonKastler

open Generator Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem exists_central_refinement_geometric
    (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) (q : ℝ) (hq : 0 ≤ q)
    (hstep : ∀ (E : FiniteMatrixStage M) (η : H),
      η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E.units) J →
      inner ℂ η (matrixStageCentralProjection E J ξ) = 0 →
      ∀ δ : ℝ, 0 < δ → ∃ F : FiniteMatrixStage M,
        E.units.concreteAlgebra ≤ F.units.concreteAlgebra ∧
        ‖matrixStageCentralProjection E J ξ - matrixStageCentralProjection F J ξ‖ ≤ δ ∧
        ‖matrixStageCentralProjection F J η‖ ≤ q * ‖η‖)
    (n : ℕ) (E : FiniteMatrixStage M) (η : H) (δ : ℝ) (hδ : 0 < δ) :
    ∃ F : FiniteMatrixStage M, E.units.concreteAlgebra ≤ F.units.concreteAlgebra ∧
      ‖matrixStageCentralProjection E J ξ - matrixStageCentralProjection F J ξ‖ ≤ δ ∧
      ‖matrixCentralResidual F J ξ η‖ ≤ q ^ n * ‖matrixCentralResidual E J ξ η‖ := by
  induction n generalizing E δ with
  | zero => exact ⟨E,le_rfl,by simpa using hδ.le,by simp⟩
  | succ n ih =>
    obtain ⟨F,hEF,hFdisp,hF⟩ := ih E (δ / 2) (half_pos hδ)
    obtain ⟨G,hFG,hGdisp,hG⟩ := hstep F (matrixCentralResidual F J ξ η)
      (matrixCentralResidual_mem F J ξ η) (matrixCentralResidual_orthogonal F J ξ η)
      (δ / 2) (half_pos hδ)
    refine ⟨G,hEF.trans hFG,?_,?_⟩
    · exact (norm_sub_le_norm_sub_add_norm_sub (matrixStageCentralProjection E J ξ)
        (matrixStageCentralProjection F J ξ) (matrixStageCentralProjection G J ξ)).trans
        ((add_le_add hFdisp hGdisp).trans_eq (add_halves δ))
    · calc
        ‖matrixCentralResidual G J ξ η‖ ≤
            ‖matrixStageCentralProjection G J (matrixCentralResidual F J ξ η)‖ :=
          matrixCentralResidual_refinement_le F G hFG J ξ η
        _ ≤ q * ‖matrixCentralResidual F J ξ η‖ := hG
        _ ≤ q * (q ^ n * ‖matrixCentralResidual E J ξ η‖) :=
          mul_le_mul_of_nonneg_left hF hq
        _ = q ^ (n+1) * ‖matrixCentralResidual E J ξ η‖ := by rw [pow_succ]; ring

theorem exists_central_refinement_of_contraction
    (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hstep : ∀ (E : FiniteMatrixStage M) (η : H),
      η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E.units) J →
      inner ℂ η (matrixStageCentralProjection E J ξ) = 0 →
      ∀ δ : ℝ, 0 < δ → ∃ F : FiniteMatrixStage M,
        E.units.concreteAlgebra ≤ F.units.concreteAlgebra ∧
        ‖matrixStageCentralProjection E J ξ - matrixStageCentralProjection F J ξ‖ ≤ δ ∧
        ‖matrixStageCentralProjection F J η‖ ≤ q * ‖η‖)
    (E : FiniteMatrixStage M) (η : H) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ F : FiniteMatrixStage M, E.units.concreteAlgebra ≤ F.units.concreteAlgebra ∧
      ‖matrixStageCentralProjection E J ξ - matrixStageCentralProjection F J ξ‖ ≤ δ ∧
      ∃ c : ℂ, ‖matrixStageCentralProjection F J η -
        c • matrixStageCentralProjection F J ξ‖ ≤ ε := by
  have ht : Tendsto (fun n : ℕ => q ^ n * ‖matrixCentralResidual E J ξ η‖)
      atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq hq1).mul_const ‖matrixCentralResidual E J ξ η‖
  obtain ⟨n,hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  obtain ⟨F,hEF,hdisp,hres⟩ := exists_central_refinement_geometric J ξ q hq hstep n E η δ hδ
  obtain ⟨c,hc⟩ := matrixCentralResidual_coefficient F J ξ η
  exact ⟨F,hEF,hdisp,c,by rw [← hc]; exact hres.trans hn.le⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GeometricCorrectionScale
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The summable error scale for multiplication correction -/

namespace KadisonKastler

open Filter Topology

noncomputable section

theorem correctionScale_nonneg {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    0 ≤ correctionScale q n := by
  unfold correctionScale
  positivity

theorem correctionScale_summable (q : ℝ) : Summable (correctionScale q) :=
  (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1)).mul_left q

theorem correctionScale_tsum (q : ℝ) : ∑' n, correctionScale q n = 2 * q := by
  change (∑' n : ℕ, q * (1/2 : ℝ)^n) = 2*q
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
  · ring
  · norm_num

theorem correctionScale_tendsto (q : ℝ) : Tendsto (correctionScale q) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => q * (1/2 : ℝ)^n) atTop (𝓝 0)
  simpa only [mul_zero] using tendsto_const_nhds.mul
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1))

theorem correctionScale_partial_sum {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    ∑ i ∈ Finset.range n, correctionScale q i ≤ 2 * q := by
  rw [← correctionScale_tsum]
  exact (correctionScale_summable q).sum_le_tsum _
    (fun i _ => correctionScale_nonneg hq i)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CentralRefinementSequence
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.concreteStageEquiv_apply _root_.OAI.KadisonSimilarity.generatedMatrixVector_apply _root_.OAI.KadisonSimilarity.generatedStageEmbedding_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The increasing central-vector refinement sequence

Summable displacement budgets keep the limit vector nonzero. Successive
finite tests give a single increasing matrix sequence with vanishing
distance-to-line errors on the prescribed countable dense family.
-/

namespace KadisonKastler

open Generator Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem centralRefinementIterates_mono (E₀ : FiniteMatrixStage M)
    (F : ℕ → FiniteMatrixStage M → FiniteMatrixStage M)
    (hF : ∀ n E, E.units.concreteAlgebra ≤ (F n E).units.concreteAlgebra) :
    Monotone (fun n => (centralRefinementIterates E₀ F n).units.concreteAlgebra) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [centralRefinementIterates_succ]
  exact hF n _

theorem centralRefinementIterates_displacement
    (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) (E₀ : FiniteMatrixStage M)
    (hfix : matrixStageCentralProjection E₀ J ξ = ξ)
    (F : ℕ → FiniteMatrixStage M → FiniteMatrixStage M) (d : ℕ → ℝ)
    (hmove : ∀ n E, ‖matrixStageCentralProjection E J ξ -
      matrixStageCentralProjection (F n E) J ξ‖ ≤ d n) (n : ℕ) :
    ‖ξ - matrixStageCentralProjection (centralRefinementIterates E₀ F n) J ξ‖ ≤
      ∑ i ∈ Finset.range n, d i := by
  induction n with
  | zero => simp only [centralRefinementIterates_zero,hfix,sub_self,norm_zero,
      Finset.sum_range_zero,le_refl]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hm := hmove n (centralRefinementIterates E₀ F n)
    have ht := dist_triangle ξ
      (matrixStageCentralProjection (centralRefinementIterates E₀ F n) J ξ)
      (matrixStageCentralProjection (centralRefinementIterates E₀ F (n+1)) J ξ)
    rw [centralRefinementIterates_succ] at ht ⊢
    simp only [dist_eq_norm] at ht
    exact ht.trans (add_le_add ih hm)

theorem central_refinement_sequence_of_refiners
    (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) (E₀ : FiniteMatrixStage M)
    (hfix : matrixStageCentralProjection E₀ J ξ = ξ)
    (η : ℕ → H) (δ : ℝ) (hδ : 0 < δ)
    (F : ℕ → FiniteMatrixStage M → FiniteMatrixStage M)
    (hF : ∀ n E, E.units.concreteAlgebra ≤ (F n E).units.concreteAlgebra)
    (hmove : ∀ n E, ‖matrixStageCentralProjection E J ξ -
      matrixStageCentralProjection (F n E) J ξ‖ ≤ correctionScale (δ / 2) n)
    (htest : ∀ n E i, i < n + 1 → ∃ c : ℂ,
      ‖matrixStageCentralProjection (F n E) J (η i) -
        c • matrixStageCentralProjection (F n E) J ξ‖ ≤ correctionScale 1 n) :
    ∃ A : ℕ → FiniteMatrixStage M,
      Monotone (fun n => (A n).units.concreteAlgebra) ∧
      (∀ n, ‖ξ - matrixStageCentralProjection (A n) J ξ‖ ≤ δ) ∧
      ∀ n i, i ≤ n → ∃ c : ℂ,
        ‖matrixStageCentralProjection (A n) J (η i) -
          c • matrixStageCentralProjection (A n) J ξ‖ ≤ correctionScale 1 n := by
  refine ⟨fun n => centralRefinementIterates E₀ F (n+1),?_,?_,?_⟩
  · intro m n hmn
    exact centralRefinementIterates_mono E₀ F hF (Nat.add_le_add_right hmn 1)
  · intro n
    exact (centralRefinementIterates_displacement J ξ E₀ hfix F _ hmove (n+1)).trans
      ((correctionScale_partial_sum (half_pos hδ).le (n+1)).trans_eq (by ring))
  · intro n i hi
    dsimp only
    rw [centralRefinementIterates_succ]
    exact htest n _ i (Nat.lt_succ_iff.mpr hi)

theorem exists_central_refinement_sequence
    (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H)
    (hstep : ∀ (E : FiniteMatrixStage M) (η : H) (δ ε : ℝ), 0 < δ → 0 < ε →
      ∃ F : FiniteMatrixStage M, E.units.concreteAlgebra ≤ F.units.concreteAlgebra ∧
        ‖matrixStageCentralProjection E J ξ - matrixStageCentralProjection F J ξ‖ ≤ δ ∧
        ∃ c : ℂ, ‖matrixStageCentralProjection F J η -
          c • matrixStageCentralProjection F J ξ‖ ≤ ε)
    (E₀ : FiniteMatrixStage M) (hfix : matrixStageCentralProjection E₀ J ξ = ξ)
    (η : ℕ → H) (δ : ℝ) (hδ : 0 < δ) :
    ∃ A : ℕ → FiniteMatrixStage M,
      Monotone (fun n => (A n).units.concreteAlgebra) ∧
      (∀ n, ‖ξ - matrixStageCentralProjection (A n) J ξ‖ ≤ δ) ∧
      ∀ n i, i ≤ n → ∃ c : ℂ,
        ‖matrixStageCentralProjection (A n) J (η i) -
          c • matrixStageCentralProjection (A n) J ξ‖ ≤ correctionScale 1 n := by
  have hdpos (n : ℕ) : 0 < correctionScale (δ / 2) n := by
    dsimp [correctionScale]
    positivity
  have hepos (n : ℕ) : 0 < correctionScale 1 n := by
    dsimp [correctionScale]
    positivity
  have hall (n : ℕ) (E : FiniteMatrixStage M) :=
    exists_finite_central_refinement J ξ hstep η (n + 1) E
      (correctionScale (δ / 2) n) (correctionScale 1 n) (hdpos n) (hepos n)
  choose F hF hmove htest using hall
  exact central_refinement_sequence_of_refiners J ξ E₀ hfix η δ hδ F hF hmove htest

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConjugateHilbertProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Conjugation and central-vector projections -/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem starProjection_conjugate (K : Submodule ℂ H) [CompleteSpace K]
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hK : ∀ ξ ∈ K, J ξ ∈ K) (ξ : H) :
    K.starProjection (J ξ) = J (K.starProjection ξ) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (hK _ (K.starProjection_apply_mem ξ))
  intro w hw
  rw [← map_sub J]
  have hi := conjugateIsometry_inner J (ξ - K.starProjection ξ) (J w)
  rw [hJ w] at hi
  rw [hi,K.starProjection_inner_eq_zero ξ (J w) (hK w hw),star_zero]

theorem matrixCentralVectorSpace_conjugate {M : VonNeumannAlgebra H}
    (A : ℕ → FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) {ξ : H} (hξ : ξ ∈ matrixCentralVectorSpace A J) :
    J ξ ∈ matrixCentralVectorSpace A J := by
  apply (Submodule.mem_iInf _).mpr
  intro n
  exact centralVectorSpace_conjugate _ J hJ (matrixCentralVectorSpace_le A J n hξ)

theorem matrixCentralVectorSpace_projection_fixed {M : VonNeumannAlgebra H}
    (A : ℕ → FiniteMatrixStage M) (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) (ξ : H) (hξ : J ξ = ξ) :
    J ((matrixCentralVectorSpace A J).starProjection ξ) =
      (matrixCentralVectorSpace A J).starProjection ξ := by
  rw [← starProjection_conjugate _ J hJ (fun _ h => matrixCentralVectorSpace_conjugate A J hJ h),hξ]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormalizeCentralLine
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Normalizing a nonzero symmetric central line -/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem exists_unit_symmetric_line (K : Submodule ℂ H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (ξ : H) (hne : ξ ≠ 0)
    (hJξ : J ξ = ξ) (hξ : ξ ∈ K) (hline : K ≤ Submodule.span ℂ {ξ}) :
    ∃ η : H, ‖η‖ = 1 ∧ J η = η ∧ η ∈ K ∧ K ≤ Submodule.span ℂ {η} := by
  let c : ℂ := ((‖ξ‖⁻¹ : ℝ) : ℂ)
  let η := c • ξ
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hne
  have hc : c ≠ 0 := by
    change ((‖ξ‖⁻¹ : ℝ) : ℂ) ≠ 0
    exact_mod_cast (ne_of_gt (inv_pos.mpr hn))
  have hη : ‖η‖ = 1 := by
    dsimp [η,c]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),
      inv_mul_cancel₀ hn.ne']
  refine ⟨η,hη,?_,K.smul_mem c hξ,?_⟩
  · change J (c • ξ) = c • ξ
    rw [J.map_smulₛₗ,hJξ]
    change star c • ξ = c • ξ
    have hcstar : star c = c := Complex.conj_ofReal _
    rw [hcstar]
  · apply le_trans hline
    apply Submodule.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    have he : ξ = c⁻¹ • η := by
      dsimp [η]
      rw [smul_smul,inv_mul_cancel₀ hc,one_smul]
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ExpectedFromCentralTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.selfAdjointVectorSpace_complete _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # From finite central-vector tests to the expected subfactor

Uniform displacement below one keeps the strong-limit vector nonzero.
Vanishing errors on a dense sequence force the central line. Normalization
and the support transfer then give all expected-subfactor data.
-/

namespace KadisonKastler

open Generator Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

theorem expectedMatrixSubfactorModel_of_central_tests
    (hM : TypeIIIFactor M) (A : ℕ → FiniteMatrixStage M)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hleft : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hright : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hunit : ‖ξ‖ = 1) (hJξ : J ξ = ξ)
    (η : ℕ → H) (hdense : DenseRange η) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0)) (δ : ℝ) (hδ : δ < 1)
    (hdisp : ∀ n, ‖ξ - (centralVectorSpace (matrixUnitConcreteAlgebra (A n).units) J).starProjection ξ‖ ≤ δ)
    (htest : ∀ n i, i ≤ n → ∃ c : ℂ,
      ‖(centralVectorSpace (matrixUnitConcreteAlgebra (A n).units) J).starProjection (η i) -
        c • (centralVectorSpace (matrixUnitConcreteAlgebra (A n).units) J).starProjection ξ‖ ≤ ε n) :
    Nonempty (ExpectedMatrixSubfactorModel M) := by
  let K := matrixCentralVectorSpace A J
  let ζ := K.starProjection ξ
  have hζ : ζ ∈ K := K.starProjection_apply_mem ξ
  have hne : ζ ≠ 0 := by
    intro hz
    have hb := matrixCentralVectorSpace_displacement_le A hA J ξ δ hdisp
    change ‖ξ - ζ‖ ≤ δ at hb
    rw [hz,sub_zero,hunit] at hb
    exact (not_le_of_gt hδ) hb
  have hJζ : J ζ = ζ := matrixCentralVectorSpace_projection_fixed A J hJ ξ hJξ
  have hline : K ≤ Submodule.span ℂ {ζ} :=
    matrixCentralVectorSpace_le_line_of_dense_tests A J ξ η hdense ε hε htest
  obtain ⟨Ω,hΩ,hJΩ,hΩK,hK⟩ := exists_unit_symmetric_line K J ζ hne hJζ hζ hline
  exact expectedMatrixSubfactorModel_of_supported_central_line hM A hA J hJ hleft hright
    Ω hΩ hJΩ hΩK hK

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ExpectedFromRefinement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.matrixSignedGroup_finite _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexDecidableEq _root_.OAI.KadisonKastler.spectralPartitionNonzeroIndexFintype _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraConstantField_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.centralVectorDefect_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.constantAlgebraUnitaryFamily_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.cyclicOrbitEquiv_val _root_.OAI.KadisonKastler.cyclicOrbitHom_apply _root_.OAI.KadisonKastler.faithfulCyclicEquiv_coe _root_.OAI.KadisonKastler.faithfulCyclicHom_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.mem_projectionFamilyCommutationSpace _root_.OAI.KadisonKastler.normalCyclicEquiv_val _root_.OAI.KadisonKastler.normalCyclicHom_apply _root_.OAI.KadisonKastler.normalPairEquiv_coe _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.spatialLeftAlgebraHom_val _root_.OAI.KadisonKastler.spatialTransportEquiv_vector _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_apply _root_.OAI.KadisonKastler.tomitaLinearPolarUnitary_symm_apply _root_.OAI.KadisonKastler.tomitaPolarCoordinates_root _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonKastler.vectorStateCommutator_add _root_.OAI.KadisonKastler.vectorStateCommutator_apply _root_.OAI.KadisonKastler.vectorStateCommutator_one _root_.OAI.KadisonKastler.vectorStateCommutator_smul _root_.OAI.KadisonKastler.vectorStateCommutator_sub _root_.OAI.KadisonKastler.vectorStateCommutator_zero _root_.OAI.KadisonSimilarity.concreteStageEquiv_apply _root_.OAI.KadisonSimilarity.generatedMatrixVector_apply _root_.OAI.KadisonSimilarity.generatedStageEmbedding_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The expected-subfactor construction from one-vector refinement

This is the closing construction in Haagerup's Lemma 3.8: finite tests,
a summable increasing sequence, the central line, and the support corner.
The local one-vector refinement hypothesis is kept explicit here; proving
it from the absorbing type III₁ hypotheses remains a separate step.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem scalarStage_centralProjection (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) (ξ : H) :
    matrixStageCentralProjection (FiniteMatrixStage.scalarStage M) J ξ = ξ := by
  apply Submodule.starProjection_eq_self_iff.mpr
  apply (mem_centralVectorSpace_matrix_iff _ J ξ).mpr
  intro i j
  change ξ = conjugationOperator J (star (1 : H →L[ℂ] H)) ξ
  rw [star_one,conjugationOperator_one J hJ]
  rfl

theorem expectedMatrixSubfactorModel_of_local_refinement
    [Nontrivial H] [TopologicalSpace.SeparableSpace H]
    (hM : TypeIIIFactor M)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hleft : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hright : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hunit : ‖ξ‖ = 1) (hJξ : J ξ = ξ)
    (hstep : ∀ (E : FiniteMatrixStage M) (η : H) (δ ε : ℝ), 0 < δ → 0 < ε →
      ∃ F : FiniteMatrixStage M, E.units.concreteAlgebra ≤ F.units.concreteAlgebra ∧
        ‖matrixStageCentralProjection E J ξ - matrixStageCentralProjection F J ξ‖ ≤ δ ∧
        ∃ c : ℂ, ‖matrixStageCentralProjection F J η -
          c • matrixStageCentralProjection F J ξ‖ ≤ ε) :
    Nonempty (ExpectedMatrixSubfactorModel M) := by
  obtain ⟨η,hdense⟩ := TopologicalSpace.exists_dense_seq (α := H)
  obtain ⟨A,hA,hdisp,htest⟩ := exists_central_refinement_sequence J ξ hstep
    (FiniteMatrixStage.scalarStage M) (scalarStage_centralProjection J hJ ξ) η (1 / 2)
    (by norm_num)
  exact expectedMatrixSubfactorModel_of_central_tests hM A hA J hJ hleft hright ξ hunit hJξ
    η hdense (correctionScale 1) (correctionScale_tendsto 1) (1 / 2) (by norm_num) hdisp htest

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StandardTypeIIIVector
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Modular conjugation on the original type III representation -/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem ModularConjugationData.left_mem {M : VonNeumannAlgebra H} {ξ : H}
    (d : ModularConjugationData M ξ) (a : Algebra M.commutant) :
    conjugationOperator d.conjugation a.val ∈ M := by
  have ha : a.val ∈ (conjugateRightAlgebra d.conjugation d.involutive M :
      Set (H →L[ℂ] H)) := by
    rw [d.commutant]
    exact a.property
  obtain ⟨b,hb,hba⟩ := ha
  rw [← hba,conjugationOperator_twice _ d.involutive]
  exact hb

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ExpectedFromContraction
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Expected matrix subfactors from a uniform central-vector contraction

A strict contraction on the orthogonal residual, with arbitrarily
small displacement of the projected reference vector, gives the
expected matrix subfactor by iteration and passage to a strong limit.
-/

namespace KadisonKastler

open Generator

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

theorem expectedMatrixSubfactorModel_of_central_contraction
    (hM : TypeIIIFactor M) (ξ : H) (hunit : ‖ξ‖ = 1)
    (d : ModularConjugationData M ξ) (q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1)
    (hstep : ∀ (E : FiniteMatrixStage M) (η : H),
      η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E.units) d.conjugation →
      inner ℂ η (matrixStageCentralProjection E d.conjugation ξ) = 0 →
      ∀ δ : ℝ, 0 < δ → ∃ F : FiniteMatrixStage M,
        E.units.concreteAlgebra ≤ F.units.concreteAlgebra ∧
        ‖matrixStageCentralProjection E d.conjugation ξ -
          matrixStageCentralProjection F d.conjugation ξ‖ ≤ δ ∧
        ‖matrixStageCentralProjection F d.conjugation η‖ ≤ q * ‖η‖) :
    Nonempty (ExpectedMatrixSubfactorModel M) := by
  exact expectedMatrixSubfactorModel_of_local_refinement hM d.conjugation d.involutive
    (d.right_mem le_rfl) d.left_mem ξ hunit d.fixes_vector
    (exists_central_refinement_of_contraction d.conjugation ξ q hq hq1 hstep)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ExpectedFromProjectionCuts
attribute [-instance] _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.centralSequenceAlgebra_complete _root_.OAI.KadisonKastler.centralSequenceAlgebra_cstar _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.centralSpaceConjugation_coe _root_.OAI.KadisonKastler.centralVectorDefect_apply _root_.OAI.KadisonKastler.mem_projectionFamilyCommutationSpace _root_.OAI.KadisonKastler.mem_projectionFamilyRemainderSpace _root_.OAI.KadisonSimilarity.concreteStageEquiv_apply _root_.OAI.KadisonSimilarity.dyadicCornerHom_coe _root_.OAI.KadisonSimilarity.generatedMatrixVector_apply _root_.OAI.KadisonSimilarity.generatedStageEmbedding_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Projection cuts close the expected-subfactor construction

Inserting a projection with a fixed commutator gap into a finite matrix
algebra contracts the discarded energy. A nearby reference vector in
the central-vector space allows geometric iteration.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Nontrivial H] [TopologicalSpace.SeparableSpace H] {M : VonNeumannAlgebra H}

theorem expectedMatrixSubfactorModel_of_projection_cuts_with_gap_oai
    (hM : TypeIIIFactor M) (ξ : H) (hunit : ‖ξ‖ = 1)
    (d : ModularConjugationData M ξ)
    (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1)
    (hcut : ∀ (E : FiniteMatrixStage M) (η : H),
      η ∈ centralVectorSpace (matrixUnitConcreteAlgebra E.units) d.conjugation →
      inner ℂ η (matrixStageCentralProjection E d.conjugation ξ) = 0 →
      ∀ δ : ℝ, 0 < δ → ∃ (F : FiniteMatrixStage M) (p : AlgebraProjection M) (ζ : H),
        E.units.concreteAlgebra ≤ F.units.concreteAlgebra ∧
        p.val.val ∈ F.units.concreteAlgebra ∧
        ζ ∈ centralVectorSpace (matrixUnitConcreteAlgebra F.units) d.conjugation ∧
        ‖matrixStageCentralProjection E d.conjugation ξ - ζ‖ ≤ δ ∧
        γ * ‖η‖ ^ 2 ≤
          ‖p.val.val η - conjugationOperator d.conjugation p.val.val η‖ ^ 2) :
    Nonempty (ExpectedMatrixSubfactorModel M) := by
  apply expectedMatrixSubfactorModel_of_central_contraction hM ξ hunit d
    (Real.sqrt (1-γ)) (Real.sqrt_nonneg _)
    ((Real.sqrt_lt (sub_nonneg.mpr hγ1.le) (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (by linarith))
  intro E η hη horth δ hδ
  obtain ⟨F,p,ζ,hEF,hp,hζ,hclose,hgap⟩ := hcut E η hη horth δ hδ
  refine ⟨F,hEF,?_,?_⟩
  · have hcomp : matrixStageCentralProjection F d.conjugation ∘L
        matrixStageCentralProjection E d.conjugation = matrixStageCentralProjection F d.conjugation :=
      Submodule.starProjection_comp_starProjection_of_le
        (centralVectorSpace_antitone hEF d.conjugation)
    have hn := centralProjection_displacement_le_of_central_vector
      (centralVectorSpace (matrixUnitConcreteAlgebra F.units) d.conjugation)
      (matrixStageCentralProjection E d.conjugation ξ) ζ hζ
    have he := congrArg (fun T : H →L[ℂ] H => T ξ) hcomp
    change matrixStageCentralProjection F d.conjugation
      (matrixStageCentralProjection E d.conjugation ξ) =
        matrixStageCentralProjection F d.conjugation ξ at he
    change ‖matrixStageCentralProjection E d.conjugation ξ -
      matrixStageCentralProjection F d.conjugation
        (matrixStageCentralProjection E d.conjugation ξ)‖ ≤ _ at hn
    rw [he] at hn
    exact hn.trans hclose
  · have he := matrixStageCentralProjection_contraction F d.conjugation d.involutive
      (d.right_mem le_rfl) p hp η γ hgap
    have hroot : Real.sqrt (1-γ) ^ 2 = 1-γ := Real.sq_sqrt (sub_nonneg.mpr hγ1.le)
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow,hroot]
    exact he

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.expectedMatrixSubfactorModel_of_projection_cuts_with_gap_oai.{u_1} := @OAI.KadisonKastler.expectedMatrixSubfactorModel_of_projection_cuts_with_gap_oai.{u_1}
