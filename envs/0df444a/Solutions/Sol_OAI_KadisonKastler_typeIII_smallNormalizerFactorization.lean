-- Prove2me | solution 1 for OAI.KadisonKastler.typeIII_smallNormalizerFactorization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:54:32.877927+00:00
-- url     : https://prove2.me/submissions/532a55dd-64a8-4b1e-8389-ac3e2ed9495c

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
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
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.AddCircle
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
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
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
import Mathlib.LinearAlgebra.Dual.Lemmas
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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
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
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K069
import Theorems.Thm_OAI_KadisonKastler_TypeIIIFactor_exists_centered_selfAdjoint_implementer
import Theorems.Thm_OAI_KadisonKastler_exists_small_normalizer_log

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
-- module Solutions.OAIQ075_KS.KadisonKastler_UnitaryExponentialBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A quantitative exponential bound for the normalizer path argument -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem exponentialPath_deriv (h : selfAdjoint (H →L[ℂ] H)) (t : ℝ) :
    HasDerivAt (fun s => (exponentialPath h s : H →L[ℂ] H))
      ((exponentialPath h t : H →L[ℂ] H) * (Complex.I • (h : H →L[ℂ] H))) t := by
  have he (s : ℝ) : (exponentialPath h s : H →L[ℂ] H) =
      NormedSpace.exp (s • (Complex.I • (h : H →L[ℂ] H))) := by
    change NormedSpace.exp (Complex.I • (s • (h : H →L[ℂ] H))) = _
    rw [smul_comm Complex.I s]
  simp_rw [he]
  exact hasDerivAt_exp_smul_const (Complex.I • (h : H →L[ℂ] H)) t

private theorem exponentialPath_deriv_left (h : selfAdjoint (H →L[ℂ] H)) (t : ℝ) :
    HasDerivAt (fun s => (exponentialPath h s : H →L[ℂ] H))
      ((Complex.I • (h : H →L[ℂ] H)) * (exponentialPath h t : H →L[ℂ] H)) t := by
  have he (s : ℝ) : (exponentialPath h s : H →L[ℂ] H) =
      NormedSpace.exp (s • (Complex.I • (h : H →L[ℂ] H))) := by
    change NormedSpace.exp (Complex.I • (s • (h : H →L[ℂ] H))) = _
    rw [smul_comm Complex.I s]
  simp_rw [he]
  exact hasDerivAt_exp_smul_const' (Complex.I • (h : H →L[ℂ] H)) t

theorem norm_expUnitary_sub_expUnitary_le (h k : selfAdjoint (H →L[ℂ] H)) :
    ‖(selfAdjoint.expUnitary h : H →L[ℂ] H) - selfAdjoint.expUnitary k‖ ≤
      ‖(h : H →L[ℂ] H) - k‖ := by
  let f (t : ℝ) := (exponentialPath h t : H →L[ℂ] H) * exponentialPath k (1 - t)
  let f' (t : ℝ) := (exponentialPath h t : H →L[ℂ] H) *
    (Complex.I • ((h : H →L[ℂ] H) - k)) * exponentialPath k (1 - t)
  have hf (t : ℝ) : HasDerivAt f (f' t) t := by
    have hk := (exponentialPath_deriv_left k (1 - t)).scomp t
      ((hasDerivAt_id t).const_sub (1 : ℝ))
    have hd := (exponentialPath_deriv h t).mul hk
    refine hd.congr_deriv ?_
    simp only [f', Function.comp_apply, one_smul, neg_smul, smul_sub]
    noncomm_ring
  have hn (t : ℝ) : ‖f' t‖ ≤ ‖(h : H →L[ℂ] H) - k‖ := by
    dsimp [f']
    rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
      norm_smul, Complex.norm_I, one_mul]
  have hb := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hf t).hasDerivWithinAt) (fun t _ => hn t)
  have hzero (a : selfAdjoint (H →L[ℂ] H)) :
      (exponentialPath a 0 : H →L[ℂ] H) = 1 := by
    change NormedSpace.exp (Complex.I • ((0 : ℝ) • (a : H →L[ℂ] H))) = 1
    rw [zero_smul, smul_zero, NormedSpace.exp_zero]
  have hone (a : selfAdjoint (H →L[ℂ] H)) :
      exponentialPath a 1 = selfAdjoint.expUnitary a := by
    apply Subtype.ext
    change NormedSpace.exp (Complex.I • ((1 : ℝ) • (a : H →L[ℂ] H))) = _
    rw [one_smul]
    rfl
  simpa only [f, sub_self, sub_zero, hzero, hone, one_mul, mul_one] using hb

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_InfinitesimalExponentiation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Exponentiating the infinitesimal normalizer estimate -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem expUnitary_mem_vonNeumann (M : VonNeumannAlgebra H)
    (a : selfAdjoint (H →L[ℂ] H)) (ha : (a : H →L[ℂ] H) ∈ M) :
    (selfAdjoint.expUnitary a : H →L[ℂ] H) ∈ M := by
  let : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
  change NormedSpace.exp (Complex.I • (a : H →L[ℂ] H)) ∈ M.toStarSubalgebra
  exact NormedSpace.exp_mem (R := ℂ) (S := StarSubalgebra ℂ (H →L[ℂ] H))
    (s := M.toStarSubalgebra) (isClosed_algebra M) (M.smul_mem ha _)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedSimpleDerivation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Sakai's inner-derivation theorem, in its needed unital form

S. Sakai, *Derivations of simple C*-algebras II*, Bulletin de la Société
Mathématique de France 99 (1971), 259--263, §2, unnumbered theorem on p.260,
together with the unital specialization explained in §1 on p.259.
DOI: 10.24033/bsmf.1719. The only input is innerness of bounded derivations
of a simple unital C-star algebra. Self-adjointness of an implementer is
derived below, not included in that input.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {A : Type u} [CStarAlgebra A]

/-- A commutator with a self-adjoint ambient element is anti-star
compatible. Taking the real part of any inner implementer preserves it. -/
theorem selfAdjoint_inner_implementer (D : A →L[ℂ] A)
    (hstar : ∀ x, D (star x) = -star (D x))
    {a : A} (ha : ∀ x, D x = a * x - x * a) :
    ∃ b : A, IsSelfAdjoint b ∧ ∀ x, D x = b * x - x * b := by
  have has : ∀ x, D x = star a * x - x * star a := by
    intro x
    have h := congrArg star (ha (star x))
    rw [hstar, star_neg, star_star, star_sub, star_mul, star_mul, star_star] at h
    exact neg_injective (by simpa only [neg_sub] using h)
  refine ⟨(1 / 2 : ℂ) • (a + star a),
    (show IsSelfAdjoint (1 / 2 : ℂ) by norm_num [isSelfAdjoint_iff]).smul
      (IsSelfAdjoint.add_star_self a), ?_⟩
  intro x
  calc
    D x = (1 / 2 : ℂ) • (D x + D x) := by
      rw [← two_smul ℂ (D x), smul_smul]
      norm_num
    _ = (1 / 2 : ℂ) • ((a * x - x * a) + (star a * x - x * star a)) := by
      conv_lhs => arg 2; arg 1; rw [ha]
      conv_lhs => arg 2; arg 2; rw [has]
    _ = ((1 / 2 : ℂ) • (a + star a)) * x -
        x * ((1 / 2 : ℂ) • (a + star a)) := by
      simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, smul_sub, smul_add]
      abel

theorem exists_selfAdjoint_implementer_of_published
    [Nontrivial A] (hPublished : PublishedSimpleDerivationInner.{u})
    (hSimple : CStarSimple A) (D : A →L[ℂ] A)
    (hderiv : ∀ x y, D (x * y) = D x * y + x * D y)
    (hstar : ∀ x, D (star x) = -star (D x)) :
    ∃ a : A, IsSelfAdjoint a ∧ ∀ x, D x = a * x - x * a := by
  obtain ⟨a, ha⟩ := hPublished A hSimple D hderiv
  exact selfAdjoint_inner_implementer D hstar ha

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveCompressionFullness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Uniform algebraic fullness from a positive compression

The type III spectral-projection argument produces an isometry `v` for
which `v* x* x v` is bounded below. Inverting a normalized compression
gives explicit left and right factors with controlled norms.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
  [PartialOrder A] [StarOrderedRing A]

theorem exists_fullness_factors_of_positive_compression
    (x v : A) (hv : star v * v = 1) {t : ℝ} (ht : 0 < t)
    (hq : algebraMap ℝ A t ≤ star v * (star x * x) * v) :
    ∃ b c : A, ‖b‖ ≤ t⁻¹ * ‖x‖ ∧ ‖c‖ ≤ 1 ∧ b * x * c = 1 := by
  let q := star v * (star x * x) * v
  let qn : A := t⁻¹ • q
  have hqn : (1 : A) ≤ qn := by
    have h := smul_le_smul_of_nonneg_left hq (inv_nonneg.mpr ht.le)
    simpa only [Algebra.algebraMap_eq_smul_one, smul_smul,
      inv_mul_cancel₀ ht.ne', one_smul] using h
  have hunit : IsUnit qn := CStarAlgebra.isUnit_of_le 1 hqn
  let r : A := CFC.rpow qn (-1)
  have hr_nonneg : 0 ≤ r := CFC.rpow_nonneg
  have hr_le : r ≤ 1 := CStarAlgebra.rpow_neg_one_le_one hqn
  have hr_norm : ‖r‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg r hr_nonneg).mpr hr_le
  have hrq : r * qn = 1 := by
    obtain ⟨u, hu⟩ := hunit
    have hpos : 0 ≤ (u : A) := by simpa only [hu] using (zero_le_one.trans hqn)
    dsimp [r]
    rw [← hu, CFC.rpow_neg_one_eq_inv u hpos]
    exact u.inv_val
  have hvnorm : ‖v‖ ≤ 1 := by
    have h : ‖star v * v‖ = ‖v‖ * ‖v‖ := CStarRing.norm_star_mul_self
    rw [hv, norm_one] at h
    nlinarith [norm_nonneg v]
  refine ⟨(t⁻¹ : ℝ) • (r * star v * star x), v, ?_, hvnorm, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ht.le)
    calc
      ‖r * star v * star x‖ ≤ ‖r‖ * ‖v‖ * ‖x‖ := by
        simpa only [norm_star] using (norm_mul_le (r * star v) (star x)).trans
          (mul_le_mul_of_nonneg_right (norm_mul_le r (star v)) (norm_nonneg (star x)))
      _ ≤ 1 * 1 * ‖x‖ := by gcongr
      _ = ‖x‖ := by ring
  · calc
      ((t⁻¹ : ℝ) • (r * star v * star x)) * x * v = r * qn := by
        simp only [qn, q, smul_mul_assoc, mul_smul_comm, mul_assoc]
      _ = 1 := hrq

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedTypeIIIProjection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CommonTracialPositionData.rightEquiv_transportEquiv _root_.OAI.KadisonKastler.FiniteInnerAverage.algebraApply_sub _root_.OAI.KadisonKastler.FullMatrixCorner.ofEquivalentProjectionFamily_entry _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.StandardTracialPosition.conjugation_algebraVector _root_.OAI.KadisonKastler.StandardTracialPosition.diagonalRepresentation_vector _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.concreteDerivation_apply _root_.OAI.KadisonKastler.concreteDiagonalSequenceUnitary_coe _root_.OAI.KadisonKastler.concreteDiagonalSequence_apply _root_.OAI.KadisonKastler.concreteDiagonalUnitary_coe _root_.OAI.KadisonKastler.concreteTraceEmbedding_inner _root_.OAI.KadisonKastler.concreteTraceLeftAction_embedding _root_.OAI.KadisonKastler.concreteTraceLeftUnitary_coe _root_.OAI.KadisonKastler.concreteTraceRightAction_embedding _root_.OAI.KadisonKastler.concreteTraceRightUnitary_coe _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrixAlgebraEquiv_apply _root_.OAI.KadisonKastler.matrixLiftUnitaryAt_coe _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.minimalCyclicRetraction_compression _root_.OAI.KadisonKastler.productBoundaryRepresentation_coe _root_.OAI.KadisonKastler.projectionFamilyEntry_star _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.rescaledGraphMap_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.concretePredualEquiv_symm_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.KadisonSimilarity.normalCoefficient_apply _root_.OAI.KadisonSimilarity.predualCoefficient_apply _root_.OAI.KadisonSimilarity.predualEvaluation_apply _root_.OAI.KadisonSimilarity.predualRestriction_apply _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The two projection inputs needed for type III compression

Blackadar, *Operator Algebras* (2006), I.6.1.2--5 and I.9.2.1(iv),
give a nonzero spectral projection above any positive threshold below
the norm of a positive element. III.1.3.5--7 and III.1.4.2 give equivalence
of every nonzero projection to the identity in a countably decomposable
type III factor. Only these projection statements are assumed below.
Neither input asserts simplicity of an ultraproduct or a perturbation bound.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.typeIIIAlgebraLE
attribute [local instance] OAI.KadisonKastler.typeIIIAlgebraOrder
local instance typeIIIAlgebraStarOrder (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _

theorem typeIII_positive_compression
    [TopologicalSpace.SeparableSpace H]
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (M : VonNeumannAlgebra H) (hM : TypeIIIFactor M)
    (x : Algebra M) {ε : ℝ} (hε : 0 < ε) (hx : ε ≤ ‖x‖) :
    ∃ v : Algebra M, star v * v = 1 ∧
      algebraMap ℝ (Algebra M) (ε ^ 2 / 2) ≤ star v * (star x * x) * v := by
  have ht : 0 < ε ^ 2 / 2 := by positivity
  have hlt : ε ^ 2 / 2 < ‖star x * x‖ := by
    rw [CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg x]
  obtain ⟨p, hp, hpne, hpx⟩ := hSpectral H M x (ε ^ 2 / 2) ht hlt
  obtain ⟨v, hv, hvp⟩ := hCompare H M hM p hp hpne
  refine ⟨v, hv, ?_⟩
  have h := star_left_conjugate_le_conjugate hpx v
  have hvpv : star v * p * v = 1 := by
    rw [← hvp]
    calc
      star v * (v * star v) * v = (star v * v) * (star v * v) := by simp [mul_assoc]
      _ = 1 := by rw [hv, one_mul]
  simpa only [mul_smul_comm, smul_mul_assoc, hvpv, Algebra.algebraMap_eq_smul_one] using h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RestrictedInnerDerivation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Restricting a spatial commutator to an invariant C-star subalgebra

An injective star homomorphism reflects the algebraic identities and the
norm bound. Thus invariance under an ambient commutator gives an actual
bounded derivation on the source algebra.
-/

namespace KadisonKastler

noncomputable section

universe u v

variable {A : Type u} {E : Type v} [CStarAlgebra A] [CStarAlgebra E]

theorem exists_restricted_inner_derivation (φ : A →⋆ₐ[ℂ] E)
    (hφ : Function.Injective φ) (T : E)
    (hrange : ∀ x : A, ∃ y : A, φ y = T * φ x - φ x * T) :
    ∃ D : A →L[ℂ] A,
      (∀ x, φ (D x) = T * φ x - φ x * T) ∧
      (∀ x y, D (x * y) = D x * y + x * D y) ∧
      (IsSelfAdjoint T → ∀ x, D (star x) = -star (D x)) := by
  choose f hf using hrange
  let L : A →ₗ[ℂ] A :=
    { toFun := f
      map_add' := by
        intro x y
        apply hφ
        simp only [hf, map_add]
        noncomm_ring
      map_smul' := by
        intro c x
        apply hφ
        simp only [hf, map_smul, smul_mul_assoc, mul_smul_comm, smul_sub]
        rfl }
  have hL : ∀ x, φ (L x) = T * φ x - φ x * T := hf
  have hbound : ∀ x, ‖L x‖ ≤ (2 * ‖T‖) * ‖x‖ := by
    intro x
    rw [← NonUnitalStarAlgHom.norm_map φ hφ (L x), hL]
    calc
      ‖T * φ x - φ x * T‖ ≤ ‖T * φ x‖ + ‖φ x * T‖ := norm_sub_le _ _
      _ ≤ ‖T‖ * ‖φ x‖ + ‖φ x‖ * ‖T‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ = (2 * ‖T‖) * ‖x‖ := by
        rw [NonUnitalStarAlgHom.norm_map φ hφ x]
        ring
  let D := L.mkContinuous (2 * ‖T‖) hbound
  have hD : ∀ x, φ (D x) = T * φ x - φ x * T := hL
  refine ⟨D, hD, ?_, ?_⟩
  · intro x y
    apply hφ
    simp only [map_add, map_mul, hD]
    noncomm_ring
  · intro hT x
    apply hφ
    simp only [map_neg, map_star, hD, star_sub, star_mul, hT.star_eq, neg_sub]

theorem exists_selfAdjoint_ambient_correction
    [Nontrivial A] (hPublished : PublishedSimpleDerivationInner.{u})
    (hSimple : CStarSimple A) (φ : A →⋆ₐ[ℂ] E)
    (hφ : Function.Injective φ) (T : E) (hT : IsSelfAdjoint T)
    (hrange : ∀ x : A, ∃ y : A, φ y = T * φ x - φ x * T) :
    ∃ a : A, IsSelfAdjoint a ∧ ∀ x : A, Commute (T - φ a) (φ x) := by
  obtain ⟨D, hD, hderiv, hstar⟩ := exists_restricted_inner_derivation φ hφ T hrange
  obtain ⟨a, ha, hDa⟩ := exists_selfAdjoint_implementer_of_published
    hPublished hSimple D hderiv (hstar hT)
  refine ⟨a, ha, fun x => ?_⟩
  have h := hD x
  rw [hDa, map_sub, map_mul, map_mul] at h
  change (T - φ a) * φ x = φ x * (T - φ a)
  rw [sub_mul, mul_sub]
  calc
    T * φ x - φ a * φ x = (T * φ x - φ x * T) -
        (φ a * φ x - φ x * φ a) + (φ x * T - φ x * φ a) := by abel
    _ = φ x * T - φ x * φ a := by rw [← h, sub_self, zero_add]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIIICenteredImplementer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Constructed norm bounds for type III inner implementers -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H] [TopologicalSpace.SeparableSpace H]
  {P : VonNeumannAlgebra H}

/-- A bounded centered splitting for a type III normalizer. -/
theorem TypeIIIFactor.exists_bounded_selfAdjoint_split (hP : TypeIIIFactor P)
    (h : selfAdjoint (H →L[ℂ] H)) (a : Algebra P) (ha : IsSelfAdjoint a)
    (hb : (h : H →L[ℂ] H) - a.val ∈ P.commutant) :
    ∃ a' b' : selfAdjoint (H →L[ℂ] H),
      (a' : H →L[ℂ] H) ∈ P ∧ (b' : H →L[ℂ] H) ∈ P.commutant ∧
      h = a' + b' ∧ ‖(a' : H →L[ℂ] H)‖ ≤ 2 * ‖(h : H →L[ℂ] H)‖ ∧
      ‖(b' : H →L[ℂ] H)‖ ≤ 3 * ‖(h : H →L[ℂ] H)‖ := by
  obtain ⟨z, hnorm⟩ := hP.exists_centered_selfAdjoint_implementer h a ha hb
  let w : H →L[ℂ] H := z • 1
  have hw : w ∈ concreteCenter P := (concreteCenter P).smul_mem (concreteCenter P).one_mem z
  let a' := realPart (a.val - w)
  let b' := realPart ((h : H →L[ℂ] H) - a.val + w)
  have he : (a' : H →L[ℂ] H) + b' = h := by
    have he' : (a.val - w) + ((h : H →L[ℂ] H) - a.val + w) = h := by abel
    change ((realPart (a.val - w) + realPart ((h : H →L[ℂ] H) - a.val + w) :
      selfAdjoint (H →L[ℂ] H)) : H →L[ℂ] H) = h
    rw [← map_add, he', h.property.coe_realPart]
  have han : ‖(a' : H →L[ℂ] H)‖ ≤ 2 * ‖(h : H →L[ℂ] H)‖ :=
    (realPart.norm_le (a.val - w)).trans hnorm
  refine ⟨a', b', realPart_mem_vonNeumann P (P.sub_mem a.property hw.1),
    realPart_mem_vonNeumann P.commutant (P.commutant.add_mem hb hw.2),
    Subtype.ext he.symm, han, ?_⟩
  have hb' : (b' : H →L[ℂ] H) = h - a' := by rw [← he]; abel
  rw [hb']
  exact (norm_sub_le _ _).trans (by linarith)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIIISmallNormalizer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Small exact normalizers of the type III factors used by stability

Sakai innerness, logarithms, simplicity, finite spectral centering, and
exponential factorization give small exact normalizers.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

attribute [local instance] OAI.KadisonKastler.smallNormalizerOrder
local instance smallNormalizerStarOrder (P : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra P) := CStarAlgebra.spectralOrderedRing _

theorem typeIII_algebra_simple
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (P : VonNeumannAlgebra H) (hP : TypeIIIFactor P) : CStarSimple (Algebra P) := by
  let _ : Nontrivial (Algebra P) := hP.algebraNontrivial
  intro I _
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  have hex : ∃ a : Algebra P, a ∈ I ∧ a ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hI
    apply le_antisymm _ bot_le
    intro a ha
    simpa only [TwoSidedIdeal.mem_bot] using hn a ha
  obtain ⟨a, ha, hane⟩ := hex
  have hpos : 0 < ‖a‖ := norm_pos_iff.mpr hane
  obtain ⟨v, hv, hq⟩ := typeIII_positive_compression hSpectral hCompare P hP a hpos le_rfl
  obtain ⟨b, c, _, _, hbc⟩ :=
    exists_fullness_factors_of_positive_compression a v hv (by positivity) hq
  apply I.eq_top
  rw [← hbc]
  exact I.mul_mem_right _ _ (I.mul_mem_left _ _ ha)

/-- The precise type III local factorization needed in modular correction.
Both constants are absolute. -/
theorem exists_small_typeIII_normalizer_factors
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (hSakai : PublishedSimpleDerivationInner.{u})
    (P : VonNeumannAlgebra H) (hP : TypeIIIFactor P)
    (v : unitary (H →L[ℂ] H)) (hv : Conjugates (H := H) v P P)
    (hsmall : ‖(v : H →L[ℂ] H) - 1‖ < 1 / 64) :
    ∃ a b : unitary (H →L[ℂ] H),
      (a : H →L[ℂ] H) ∈ P ∧ (b : H →L[ℂ] H) ∈ P.commutant ∧
      v = a * b ∧
      ‖(a : H →L[ℂ] H) - 1‖ + ‖(b : H →L[ℂ] H) - 1‖ ≤
        10 * ‖(v : H →L[ℂ] H) - 1‖ := by
  let _ : Nontrivial (Algebra P) := hP.algebraNontrivial
  let _ : Nontrivial H := by
    rcases subsingleton_or_nontrivial H with hs | hn
    · let := hs
      exact (hP.nonzero (Subsingleton.elim _ _)).elim
    · exact hn
  obtain ⟨h, hh, hn, hrange⟩ := exists_small_normalizer_log P v hv hsmall
  obtain ⟨a, ha, hcomm⟩ := exists_selfAdjoint_ambient_correction hSakai
    (typeIII_algebra_simple hSpectral hCompare P hP) P.toStarSubalgebra.subtype
    Subtype.val_injective (h : H →L[ℂ] H) h.property
    (fun x => ⟨⟨_, hrange x x.property⟩, rfl⟩)
  have hb : (h : H →L[ℂ] H) - a.val ∈ P.commutant := by
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro x hx
    exact (hcomm ⟨x, hx⟩).eq.symm
  obtain ⟨a', b', ha', hb', hab, han, hbn⟩ :=
    hP.exists_bounded_selfAdjoint_split h a ha hb
  have hc : Commute (a' : H →L[ℂ] H) (b' : H →L[ℂ] H) :=
    VonNeumannAlgebra.mem_commutant_iff.mp hb' _ ha'
  refine ⟨selfAdjoint.expUnitary a', selfAdjoint.expUnitary b',
    expUnitary_mem_vonNeumann P a' ha', expUnitary_mem_vonNeumann P.commutant b' hb', ?_, ?_⟩
  · rw [← hh, hab, hc.expUnitary_add]
  · have hna := norm_expUnitary_sub_expUnitary_le a' 0
    have hnb := norm_expUnitary_sub_expUnitary_le b' 0
    simp only [selfAdjoint.expUnitary_zero, OneMemClass.coe_one, ZeroMemClass.coe_zero,
      sub_zero] at hna hnb
    linarith

theorem typeIII_smallNormalizerFactorization_oai
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (hSakai : PublishedSimpleDerivationInner.{u})
    (P : VonNeumannAlgebra H) (hP : TypeIIIFactor P) : SmallNormalizerFactorization P :=
  exists_small_typeIII_normalizer_factors hSpectral hCompare hSakai P hP

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.typeIII_smallNormalizerFactorization_oai.{u} := @OAI.KadisonKastler.typeIII_smallNormalizerFactorization_oai.{u}
