-- Prove2me | solution 1 for OAI.KadisonKastler.uniform_typeIII_normalizer_from_smoothing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:18:03.458438+00:00
-- url     : https://prove2.me/submissions/1d9324bf-1e50-4819-9c6d-ad31a94e134c

import Mathlib
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
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
import Mathlib.Analysis.Complex.Circle
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
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
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
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K066
import Theorems.Thm_OAI_KadisonKastler_uniform_typeIII_smoothed_normalizers

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.conjugationFamily_apply _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# The concrete Kadison–Kastler distance

The distance is the operator-norm Hausdorff distance between the closed unit
balls of two concrete, unital von Neumann algebras.  All Hilbert spaces are
allowed, including the zero space. The elementary estimates belong to §2 of
*Universal strong Kadison–Kastler stability* (2026).
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem unitaryConj_sub (v : unitary (H →L[ℂ] H)) (x y : H →L[ℂ] H) :
    unitaryConj v (x - y) = unitaryConj v x - unitaryConj v y := by
  simp [unitaryConj, mul_sub, sub_mul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NearInclusionDistance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Normalizing strict near-inclusion approximants -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M N : VonNeumannAlgebra H}

/-- An algebra approximant can be normalized into its unit ball with at
most twice the original error. -/
theorem exists_unitBall_approx_of_algebra_approx
    {x y : H →L[ℂ] H} (hx : ‖x‖ ≤ 1) (hy : y ∈ N) :
    ∃ z ∈ unitBall N, ‖x - z‖ ≤ 2 * ‖x - y‖ := by
  by_cases hy1 : ‖y‖ ≤ 1
  · exact ⟨y, ⟨hy, hy1⟩, by nlinarith [norm_nonneg (x - y)]⟩
  have hypos : 0 < ‖y‖ := by linarith
  let z : H →L[ℂ] H := (‖y‖⁻¹ : ℂ) • y
  have hznorm : ‖z‖ = 1 := norm_smul_inv_norm (norm_pos_iff.mp hypos)
  have hyz : ‖y - z‖ = ‖y‖ - 1 := by
    have hi : 0 ≤ 1 - ‖y‖⁻¹ := by
      have ht : ‖y‖⁻¹ ≤ 1 := (inv_le_one₀ hypos).mpr (lt_of_not_ge hy1).le
      linarith
    have he : y - z = ((1 - ‖y‖⁻¹ : ℝ) : ℂ) • y := by
      simp only [z, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_inv,
        sub_smul, one_smul]
    rw [he, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hi]
    rw [sub_mul, one_mul, inv_mul_cancel₀ hypos.ne']
  have hnorm : ‖y‖ - 1 ≤ ‖x - y‖ := by
    have ht := norm_add_le (y - x) x
    rw [sub_add_cancel, norm_sub_rev] at ht
    linarith
  refine ⟨z, ⟨N.toStarSubalgebra.smul_mem hy _, hznorm.le⟩, ?_⟩
  exact (norm_sub_le_norm_sub_add_norm_sub x y z).trans (by rw [hyz]; linarith)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ApproximateNormalizerComposition
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Composition of approximate normalizers with unit-ball normalization -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem infDist_unitaryConj_mul_le (M : VonNeumannAlgebra H)
    (u v : unitary (H →L[ℂ] H)) {e f : ℝ}
    (hu : ∀ x ∈ unitBall M, Metric.infDist (unitaryConj (H := H) u x)
      (M : Set (H →L[ℂ] H)) ≤ e)
    (hv : ∀ x ∈ unitBall M, Metric.infDist (unitaryConj (H := H) v x)
      (M : Set (H →L[ℂ] H)) ≤ f) (x : H →L[ℂ] H) (hx : x ∈ unitBall M) :
    Metric.infDist (unitaryConj (H := H) (u * v) x) (M : Set (H →L[ℂ] H)) ≤ e + 2 * f := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  have hnear : Metric.infDist (unitaryConj (H := H) v x) (M : Set (H →L[ℂ] H)) <
      (r - e) / 2 := (hv x hx).trans_lt (by linarith)
  obtain ⟨y, hy, hxy⟩ := (Metric.infDist_lt_iff
    (show (M : Set (H →L[ℂ] H)).Nonempty from ⟨0, M.zero_mem⟩)).mp hnear
  obtain ⟨z, hz, hxz⟩ := exists_unitBall_approx_of_algebra_approx
    (N := M) (x := unitaryConj (H := H) v x) (y := y) (by simpa only [norm_unitaryConj] using hx.2) hy
  have hbound : ‖unitaryConj (H := H) v x - z‖ < r - e := by
    rw [dist_eq_norm] at hxy
    exact hxz.trans_lt (by linarith)
  have h := Metric.infDist_le_infDist_add_dist
    (x := unitaryConj (H := H) (u * v) x) (y := unitaryConj (H := H) u z)
    (s := (M : Set (H →L[ℂ] H)))
  rw [unitaryConj_mul, dist_eq_norm, ← unitaryConj_sub, norm_unitaryConj] at h
  simpa only [unitaryConj_mul] using
    (h.trans (add_le_add (hu z hz) hbound.le)).trans_eq (show e + (r - e) = r by ring)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Polar
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Polar unitaries close to the identity

We construct the polar factor of an invertible element using the positive
square root supplied by continuous functional calculus.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {A : Type*} [CStarAlgebra A]

section Ordered

variable [PartialOrder A] [StarOrderedRing A]

/-- A positive unit with upper bounds on its norm and inverse lies within
the same radius of the identity. -/
theorem norm_positive_unit_sub_one_le [Nontrivial A] (s : Aˣ) (hs : 0 ≤ (s : A)) {r : ℝ}
    (hr : 0 ≤ r) (hr₁ : r < 1) (hnorm : ‖(s : A)‖ ≤ 1 + r)
    (hinv : ‖((s⁻¹ : Aˣ) : A)‖ ≤ (1 - r)⁻¹) :
    ‖(s : A) - 1‖ ≤ r := by
  have hrepr : cfc (fun x : ℝ => x - 1) (s : A) = (s : A) - 1 := by
    rw [cfc_sub (fun x : ℝ => x) (fun _ : ℝ => 1) (s : A),
      cfc_id' ℝ (s : A), cfc_const_one ℝ (s : A)]
  rw [← hrepr]
  apply norm_cfc_le hr
  intro x hx
  have hx₀ : 0 ≤ x := spectrum_nonneg_of_nonneg hs hx
  have hxne : x ≠ 0 := by
    intro hzero
    exact spectrum.zero_notMem ℝ s.isUnit (hzero ▸ hx)
  have hxpos : 0 < x := lt_of_le_of_ne hx₀ (Ne.symm hxne)
  have hxupper : x ≤ 1 + r :=
    (Real.le_norm_self x).trans ((spectrum.norm_le_norm_of_mem hx).trans hnorm)
  have hxinv : x⁻¹ ≤ (1 - r)⁻¹ :=
    (Real.le_norm_self (x⁻¹)).trans
      ((spectrum.norm_le_norm_of_mem (spectrum.inv₀_mem_inv hx)).trans hinv)
  have hxlower : 1 - r ≤ x :=
    (inv_le_inv₀ hxpos (sub_pos.mpr hr₁)).mp hxinv
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Ordered

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PolarSmoothing
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Quantitative polar smoothing from bounds on an operator and its inverse -/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem exists_polar_unitary_of_norm_bounds [Nontrivial A] (t : Aˣ) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (ht : ‖(t : A)‖ ≤ 1 + r)
    (hti : ‖((t⁻¹ : Aˣ) : A)‖ ≤ (1 - r)⁻¹) :
    ∃ u : unitary A, (u : A) * CFC.abs (t : A) = (t : A) ∧ ‖(u : A) - (t : A)‖ ≤ r := by
  obtain ⟨u, hu⟩ := exists_unitary_mul_abs t
  let s : Aˣ := (isUnit_abs t).unit
  have hs : (s : A) = CFC.abs (t : A) := (isUnit_abs t).unit_spec
  have hdecomp : (u : A) * (s : A) = (t : A) := by rwa [hs]
  have hinveq : ((s⁻¹ : Aˣ) : A) = ((t⁻¹ : Aˣ) : A) * (u : A) := by
    calc
      ((s⁻¹ : Aˣ) : A) =
          (((t⁻¹ : Aˣ) : A) * (t : A)) * ((s⁻¹ : Aˣ) : A) := by simp
      _ = (((t⁻¹ : Aˣ) : A) * ((u : A) * (s : A))) * ((s⁻¹ : Aˣ) : A) := by rw [hdecomp]
      _ = ((t⁻¹ : Aˣ) : A) * (u : A) := by
        simp only [mul_assoc, Units.mul_inv, mul_one]
  have hsinv : ‖((s⁻¹ : Aˣ) : A)‖ ≤ (1 - r)⁻¹ := by
    rw [hinveq, CStarRing.norm_mul_coe_unitary]
    exact hti
  have hsbound : ‖(s : A) - 1‖ ≤ r := norm_positive_unit_sub_one_le s
    (by rw [hs]; exact CFC.abs_nonneg _) hr hr1 (by simpa only [hs, CFC.norm_abs] using ht) hsinv
  refine ⟨u, hu, ?_⟩
  have hdiff : (u : A) - (t : A) = (u : A) * (1 - CFC.abs (t : A)) := by
    rw [mul_sub, mul_one, hu]
  rw [hdiff, CStarRing.norm_coe_unitary_mul, norm_sub_rev, ← hs]
  exact hsbound

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ContinuousPolarPath
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Continuous polar unitary paths

The polar decomposition identifies its unitary factor with
`a * inverse(abs a)`. This gives norm continuity for continuous paths
of invertible operators, together with quantitative smoothing bounds.
-/

namespace KadisonKastler

open scoped Topology CStarAlgebra

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem polarUnitary_mul_abs (t : Aˣ) :
    (polarUnitary t : A) * CFC.abs (t : A) = (t : A) :=
  (exists_unitary_mul_abs t).choose_spec

theorem polarUnitary_eq_mul_inverse_abs (t : Aˣ) :
    (polarUnitary t : A) = (t : A) * Ring.inverse (CFC.abs (t : A)) := by
  let s : Aˣ := (isUnit_abs t).unit
  have hs : (s : A) = CFC.abs (t : A) := (isUnit_abs t).unit_spec
  rw [← hs, Ring.inverse_unit]
  calc
    (polarUnitary t : A) = ((polarUnitary t : A) * (s : A)) * (s⁻¹ : Aˣ) := by
      simp only [mul_assoc, Units.mul_inv, mul_one]
    _ = (t : A) * (s⁻¹ : Aˣ) := by rw [hs, polarUnitary_mul_abs]

theorem polarUnitary_unique (t : Aˣ) (u : unitary A)
    (hu : (u : A) * CFC.abs (t : A) = (t : A)) : u = polarUnitary t := by
  apply Subtype.ext
  let s : Aˣ := (isUnit_abs t).unit
  have hs : (s : A) = CFC.abs (t : A) := (isUnit_abs t).unit_spec
  have he : (u : A) * (s : A) = (polarUnitary t : A) * s := by
    rw [hs, hu, polarUnitary_mul_abs]
  have hm := congrArg (fun a : A => a * (s⁻¹ : Aˣ)) he
  simpa only [mul_assoc, Units.mul_inv, mul_one] using hm

theorem continuous_polarUnitary : Continuous (polarUnitary : Aˣ → unitary A) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun t : Aˣ => (polarUnitary t : A))
  have he : (fun t : Aˣ => (polarUnitary t : A)) =
      (fun t : Aˣ => (t : A) * Ring.inverse (CFC.abs (t : A))) :=
    funext polarUnitary_eq_mul_inverse_abs
  rw [he]
  apply continuous_iff_continuousAt.mpr
  intro t
  let s : Aˣ := (isUnit_abs t).unit
  have hs : (s : A) = CFC.abs (t : A) := (isUnit_abs t).unit_spec
  have hi : ContinuousAt Ring.inverse (CFC.abs (t : A)) := by
    rw [← hs]
    exact NormedRing.inverse_continuousAt s
  have ha : Continuous (fun u : Aˣ => CFC.abs (u : A)) :=
    CFC.continuous_abs.comp Units.continuous_val
  exact Units.continuous_val.continuousAt.mul (hi.comp (f := fun u : Aˣ => CFC.abs (u : A)) ha.continuousAt)

/-- A continuous operator family known pointwise to be invertible gives
an actual norm-continuous family of polar unitaries. -/
theorem continuous_polarUnitary_of_isUnit {X : Type*} [TopologicalSpace X]
    (f : X → A) (hf : Continuous f) (hunit : ∀ x, IsUnit (f x)) :
    Continuous (fun x => polarUnitary (hunit x).unit) := by
  apply continuous_polarUnitary.comp
  apply Units.isOpenEmbedding_val.isEmbedding.continuous_iff.mpr
  have he : Units.val ∘ (fun x => (hunit x).unit) = f :=
    funext fun x => (hunit x).unit_spec
  rw [he]
  exact hf

theorem norm_polarUnitary_sub_le [Nontrivial A] (t : Aˣ) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r < 1) (ht : ‖(t : A)‖ ≤ 1 + r)
    (hti : ‖((t⁻¹ : Aˣ) : A)‖ ≤ (1 - r)⁻¹) :
    ‖(polarUnitary t : A) - t‖ ≤ r := by
  obtain ⟨u, hu, hclose⟩ := exists_polar_unitary_of_norm_bounds t hr hr1 ht hti
  rwa [polarUnitary_unique t u hu] at hclose

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SmoothingInverse
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Invertibility and inverse bounds for the smoothed pair -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

/-- Two approximate inverse identities give an actual inverse. The algebra
need not be directly finite. -/
theorem isUnit_of_two_approximate_inverses (a c : A)
    (hac : ‖a * c - 1‖ < 1) (hca : ‖c * a - 1‖ < 1) : IsUnit a := by
  let u : Aˣ := Units.oneSub (1 - a * c) (by simpa only [norm_sub_rev] using hac)
  let v : Aˣ := Units.oneSub (1 - c * a) (by simpa only [norm_sub_rev] using hca)
  have hu : (u : A) = a * c := by simp only [u, Units.val_oneSub, sub_sub_cancel]
  have hv : (v : A) = c * a := by simp only [v, Units.val_oneSub, sub_sub_cancel]
  let r : A := c * ((u⁻¹ : Aˣ) : A)
  let l : A := ((v⁻¹ : Aˣ) : A) * c
  have har : a * r = 1 := by
    dsimp only [r]
    rw [← mul_assoc, ← hu, Units.mul_inv]
  have hla : l * a = 1 := by
    dsimp only [l]
    rw [mul_assoc, ← hv, Units.inv_mul]
  have hlr : l = r := by
    calc
      l = l * (a * r) := by rw [har, mul_one]
      _ = (l * a) * r := (mul_assoc _ _ _).symm
      _ = r := by rw [hla, one_mul]
  exact ⟨⟨a, r, har, by rw [← hlr]; exact hla⟩, rfl⟩

/-- The inverse bound only needs the approximate right inverse once actual
invertibility has been established. -/
theorem norm_inverse_le_of_approximate_inverse (a : Aˣ) (c : A) {η : ℝ}
    (hη : η < 1) (hac : ‖(a : A) * c - 1‖ ≤ η) :
    ‖((a⁻¹ : Aˣ) : A)‖ ≤ ‖c‖ / (1 - η) := by
  have he : ((a⁻¹ : Aˣ) : A) = c + ((a⁻¹ : Aˣ) : A) * (1 - (a : A) * c) := by
    rw [mul_sub, mul_one, ← mul_assoc, Units.inv_mul, one_mul]
    abel
  have hh : ‖((a⁻¹ : Aˣ) : A)‖ ≤ ‖c‖ + ‖((a⁻¹ : Aˣ) : A)‖ * η := by
    calc
      _ = ‖c + ((a⁻¹ : Aˣ) : A) * (1 - (a : A) * c)‖ := congrArg norm he
      _ ≤ ‖c‖ + ‖((a⁻¹ : Aˣ) : A) * (1 - (a : A) * c)‖ := norm_add_le _ _
      _ ≤ ‖c‖ + ‖((a⁻¹ : Aˣ) : A)‖ * η := by
        exact add_le_add le_rfl ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
          (by simpa only [norm_sub_rev] using hac) (norm_nonneg _)))
  apply (le_div_iff₀ (sub_pos.mpr hη)).mpr
  nlinarith

theorem norm_unitary_star_sub_approximate_inverse_le
    (t : Aˣ) (u : unitary A) (c : A) {r η : ℝ}
    (hu : ‖(u : A) - (t : A)‖ ≤ r) (hc : ‖(t : A) * c - 1‖ ≤ η) :
    ‖star (u : A) - c‖ ≤ ‖((t⁻¹ : Aˣ) : A)‖ * (r + η) := by
  have he : star (u : A) - c =
      ((t⁻¹ : Aˣ) : A) * ((t : A) - u) * star (u : A) +
      ((t⁻¹ : Aˣ) : A) * (1 - (t : A) * c) := by
    rw [mul_sub, sub_mul, mul_sub, mul_one, ← mul_assoc,
      Units.inv_mul, one_mul, mul_assoc, Unitary.mul_star_self_of_mem u.property]
    simp only [mul_one, one_mul]
    abel
  rw [he]
  calc
    _ ≤ ‖((t⁻¹ : Aˣ) : A) * ((t : A) - u) * star (u : A)‖ +
        ‖((t⁻¹ : Aˣ) : A) * (1 - (t : A) * c)‖ := norm_add_le _ _
    _ = ‖((t⁻¹ : Aˣ) : A) * ((t : A) - u)‖ +
        ‖((t⁻¹ : Aˣ) : A) * (1 - (t : A) * c)‖ := by
      rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary]
    _ ≤ ‖((t⁻¹ : Aˣ) : A)‖ * ‖(t : A) - u‖ +
        ‖((t⁻¹ : Aˣ) : A)‖ * ‖1 - (t : A) * c‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ ‖((t⁻¹ : Aˣ) : A)‖ * r + ‖((t⁻¹ : Aˣ) : A)‖ * η :=
      add_le_add (mul_le_mul_of_nonneg_left (by simpa only [norm_sub_rev] using hu)
        (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (by simpa only [norm_sub_rev] using hc) (norm_nonneg _))
    _ = _ := by ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_QuantitativePolarPath
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Quantitative continuous polar paths from two approximate inverses -/

namespace KadisonKastler

noncomputable section

variable {A X : Type*} [CStarAlgebra A] [Nontrivial A]
    [PartialOrder A] [StarOrderedRing A] [TopologicalSpace X]

/-- The smoothing estimates produce a continuous unitary family with
explicit errors in both factors. Only the first family needs continuity. -/
theorem exists_continuous_polar_path (a c : X → A) (ha : Continuous a)
    {r : ℝ} (hr : 0 ≤ r) (hrsmall : r < 1 / 8)
    (hanorm : ∀ x, ‖a x‖ ≤ 1 + r) (hcnorm : ∀ x, ‖c x‖ ≤ 1 + r)
    (hac : ∀ x, ‖a x * c x - 1‖ ≤ r) (hca : ∀ x, ‖c x * a x - 1‖ ≤ r) :
    ∃ v : X → unitary A, Continuous v ∧
      (∀ x, ‖(v x : A) - a x‖ ≤ 4 * r) ∧
      (∀ x, ‖star (v x : A) - c x‖ ≤ 10 * r) := by
  have hr1 : r < 1 := by linarith
  have hinv (x : X) : IsUnit (a x) :=
    isUnit_of_two_approximate_inverses (a x) (c x)
      ((hac x).trans_lt hr1) ((hca x).trans_lt hr1)
  let t (x : X) : Aˣ := (hinv x).unit
  have ht (x : X) : (t x : A) = a x := (hinv x).unit_spec
  have htinverse (x : X) : ‖(((t x)⁻¹ : Aˣ) : A)‖ ≤ (1 + r) / (1 - r) := by
    exact (norm_inverse_le_of_approximate_inverse (t x) (c x) hr1
      (by simpa only [ht] using hac x)).trans
      (div_le_div_of_nonneg_right (hcnorm x) (by linarith))
  have hnum : (1 + r) / (1 - r) ≤ (1 - 4 * r)⁻¹ := by
    rw [inv_eq_one_div, div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [sq_nonneg r]
  have htwo : (1 + r) / (1 - r) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hpolar (x : X) : ‖(polarUnitary (t x) : A) - a x‖ ≤ 4 * r := by
    have hn := norm_polarUnitary_sub_le (t x) (show 0 ≤ 4 * r by positivity)
      (show 4 * r < 1 by linarith)
      (show ‖(t x : A)‖ ≤ 1 + 4 * r by rw [ht]; exact (hanorm x).trans (by linarith))
      ((htinverse x).trans hnum)
    simpa only [ht] using hn
  refine ⟨fun x => polarUnitary (t x), continuous_polarUnitary_of_isUnit a ha hinv,
    hpolar, ?_⟩
  intro x
  have hub := norm_unitary_star_sub_approximate_inverse_le (t x) (polarUnitary (t x))
    (c x) (by simpa only [ht] using hpolar x) (by simpa only [ht] using hac x)
  exact hub.trans (by
    have hn := (htinverse x).trans htwo
    nlinarith)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PolarNormalizerPath
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Polar paths preserve approximate algebra relations -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem norm_unitary_bilinear_error (v : unitary (H →L[ℂ] H))
    (a c x : H →L[ℂ] H) {p q r : ℝ} (hp : 0 ≤ p)
    (hva : ‖(v : H →L[ℂ] H) - a‖ ≤ p)
    (hvc : ‖star (v : H →L[ℂ] H) - c‖ ≤ q)
    (hc : ‖c‖ ≤ 1 + r) (hx : ‖x‖ ≤ 1) :
    ‖unitaryConj (H := H) v x - a * x * c‖ ≤ p * (1 + r) + q := by
  have he : unitaryConj (H := H) v x - a * x * c =
      ((v : H →L[ℂ] H) - a) * x * c + (v : H →L[ℂ] H) * x * (star (v : H →L[ℂ] H) - c) := by
    simp only [unitaryConj, sub_mul, mul_sub, mul_assoc]
    abel
  have hleft : ‖((v : H →L[ℂ] H) - a) * x‖ ≤ p := by
    exact (norm_mul_le _ _).trans ((mul_le_mul hva hx (norm_nonneg _) hp).trans_eq
      (mul_one _))
  have hleft' : ‖((v : H →L[ℂ] H) - a) * x * c‖ ≤ p * (1 + r) :=
    (norm_mul_le _ _).trans (mul_le_mul hleft hc (norm_nonneg _) hp)
  have hright : ‖(v : H →L[ℂ] H) * x * (star (v : H →L[ℂ] H) - c)‖ ≤ q := by
    rw [mul_assoc, CStarRing.norm_coe_unitary_mul]
    exact (norm_mul_le _ _).trans ((mul_le_mul hx hvc (norm_nonneg _) zero_le_one).trans_eq
      (one_mul _))
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hleft' hright)

theorem infDist_polar_conjugation_le (M : VonNeumannAlgebra H)
    (v : unitary (H →L[ℂ] H)) (a c x : H →L[ℂ] H) {r : ℝ}
    (hr : 0 ≤ r) (hrsmall : r < 1 / 8)
    (hva : ‖(v : H →L[ℂ] H) - a‖ ≤ 4 * r)
    (hvc : ‖star (v : H →L[ℂ] H) - c‖ ≤ 10 * r)
    (hc : ‖c‖ ≤ 1 + r) (hx : ‖x‖ ≤ 1)
    (halg : Metric.infDist (a * x * c) (M : Set (H →L[ℂ] H)) ≤ r) :
    Metric.infDist (unitaryConj (H := H) v x) (M : Set (H →L[ℂ] H)) ≤ 16 * r := by
  have h := Metric.infDist_le_infDist_add_dist
    (x := unitaryConj (H := H) v x) (y := a * x * c) (s := (M : Set (H →L[ℂ] H)))
  rw [dist_eq_norm] at h
  have hn := norm_unitary_bilinear_error v a c x (show 0 ≤ 4 * r by positivity)
    hva hvc hc hx
  exact h.trans ((add_le_add halg hn).trans (by nlinarith))

theorem infDist_polar_star_conjugation_le (M : VonNeumannAlgebra H)
    (v : unitary (H →L[ℂ] H)) (a c x : H →L[ℂ] H) {r : ℝ}
    (hr : 0 ≤ r) (hrsmall : r < 1 / 8)
    (hva : ‖(v : H →L[ℂ] H) - a‖ ≤ 4 * r)
    (hvc : ‖star (v : H →L[ℂ] H) - c‖ ≤ 10 * r)
    (ha : ‖a‖ ≤ 1 + r) (hx : ‖x‖ ≤ 1)
    (halg : Metric.infDist (c * x * a) (M : Set (H →L[ℂ] H)) ≤ r) :
    Metric.infDist (unitaryConj (H := H) (star v) x) (M : Set (H →L[ℂ] H)) ≤ 17 * r := by
  have hn := norm_unitary_bilinear_error (star v) c a x
    (show 0 ≤ 10 * r by positivity) hvc
    (by simpa only [Unitary.coe_star, star_star] using hva) ha hx
  have h := Metric.infDist_le_infDist_add_dist
    (x := unitaryConj (H := H) (star v) x) (y := c * x * a) (s := (M : Set (H →L[ℂ] H)))
  rw [dist_eq_norm] at h
  exact h.trans ((add_le_add halg hn).trans (by nlinarith))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormalizedPolarPath
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Based approximate-normalizer paths from smoothed algebra relations -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [Nontrivial H]

attribute [local instance] OAI.KadisonKastler.polarPathOrder
local instance polarPathStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

theorem exists_based_polar_normalizer_path (M : VonNeumannAlgebra H)
    (a c : ℝ → H →L[ℂ] H) (ha : Continuous a) {r : ℝ}
    (hr : 0 ≤ r) (hrsmall : r < 1 / 8)
    (hanorm : ∀ t, ‖a t‖ ≤ 1 + r) (hcnorm : ∀ t, ‖c t‖ ≤ 1 + r)
    (hac : ∀ t, ‖a t * c t - 1‖ ≤ r) (hca : ∀ t, ‖c t * a t - 1‖ ≤ r)
    (halg : ∀ t x, x ∈ unitBall M →
      Metric.infDist (a t * x * c t) (M : Set (H →L[ℂ] H)) ≤ r)
    (hcalg : ∀ t x, x ∈ unitBall M →
      Metric.infDist (c t * x * a t) (M : Set (H →L[ℂ] H)) ≤ r) :
    ∃ v E : ℝ → unitary (H →L[ℂ] H), Continuous v ∧ Continuous E ∧ E 0 = 1 ∧
      (∀ t, E t = v t * star (v 0)) ∧
      (∀ t, ‖(v t : H →L[ℂ] H) - a t‖ ≤ 4 * r) ∧
      (∀ t, ‖star (v t : H →L[ℂ] H) - c t‖ ≤ 10 * r) ∧
      (∀ t x, x ∈ unitBall M →
        Metric.infDist (unitaryConj (H := H) (E t) x) (M : Set (H →L[ℂ] H)) ≤ 50 * r) := by
  obtain ⟨v, hv, hva, hvc⟩ := exists_continuous_polar_path a c ha hr hrsmall
    hanorm hcnorm hac hca
  let E (t : ℝ) := v t * star (v 0)
  refine ⟨v, E, hv, hv.mul continuous_const, ?_, fun _ => rfl, hva, hvc, ?_⟩
  · exact Unitary.mul_star_self (v 0)
  · intro t x hx
    have hf (s : ℝ) (y : H →L[ℂ] H) (hy : y ∈ unitBall M) :
        Metric.infDist (unitaryConj (H := H) (v s) y) (M : Set (H →L[ℂ] H)) ≤ 16 * r :=
      infDist_polar_conjugation_le M (v s) (a s) (c s) y hr hrsmall
        (hva s) (hvc s) (hcnorm s) hy.2 (halg s y hy)
    have hb (y : H →L[ℂ] H) (hy : y ∈ unitBall M) :
        Metric.infDist (unitaryConj (H := H) (star (v 0)) y)
          (M : Set (H →L[ℂ] H)) ≤ 17 * r :=
      infDist_polar_star_conjugation_le M (v 0) (a 0) (c 0) y hr hrsmall
        (hva 0) (hvc 0) (hanorm 0) hy.2 (hcalg 0 y hy)
    exact (infDist_unitaryConj_mul_le M (v t) (star (v 0)) (hf t) hb x hx).trans_eq (by ring)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PoissonBoundaryLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The strong-star boundary comparison used in modular smoothing

The demodulated Cauchy averages are actual bounded operators. Their products
converge strongly-* even though the polar smoothing paths need not converge.
-/

namespace KadisonKastler

open Filter MeasureTheory
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Multiplication is strongly continuous on a family with bounded left
operator norms; the right arguments may also vary. -/
theorem tendsto_operator_comp_of_uniform_bound {ι : Type*} {l : Filter ι}
    (A B : ι → H →L[ℂ] H) (T S : H →L[ℂ] H) (C : ℝ)
    (hbound : ∀ᶠ i in l, ‖A i‖ ≤ C)
    (hA : ∀ x, Tendsto (fun i => A i x) l (𝓝 (T x)))
    (hB : ∀ x, Tendsto (fun i => B i x) l (𝓝 (S x))) (x : H) :
    Tendsto (fun i => (A i * B i) x) l (𝓝 ((T * S) x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hconstS : Tendsto (fun _ : ι => S x) l (𝓝 (S x)) := tendsto_const_nhds
  have hconstT : Tendsto (fun _ : ι => T (S x)) l (𝓝 (T (S x))) := tendsto_const_nhds
  have h₁ : Tendsto (fun i => C * ‖B i x - S x‖) l (𝓝 0) := by
    simpa only [sub_self, norm_zero, mul_zero] using
      (((hB x).sub hconstS).norm.const_mul C)
  have h₂ : Tendsto (fun i => ‖A i (S x) - T (S x)‖) l (𝓝 0) := by
    simpa only [sub_self, norm_zero] using ((hA (S x)).sub hconstT).norm
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa only [add_zero] using h₁.add h₂)
  filter_upwards [hbound] with i hi
  have he : (A i * B i) x - (T * S) x =
      A i (B i x - S x) + (A i (S x) - T (S x)) := by
    simp only [mul_apply_eq_comp, map_sub]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add
    (((A i).le_opNorm _).trans (mul_le_mul_of_nonneg_right hi (norm_nonneg _))) le_rfl)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SmoothingProductComparison
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Products of smoothing comparisons -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

theorem norm_unitary_product_sub_le (u v : unitary A) (a b : A) {d B : ℝ}
    (hB : 0 ≤ B) (hu : ‖(u : A) - a‖ ≤ d)
    (hv : ‖(v : A) - b‖ ≤ d) (ha : ‖a‖ ≤ B) :
    ‖(u : A) * star (v : A) - a * star b‖ ≤ (1 + B) * d := by
  have he : (u : A) * star (v : A) - a * star b =
      ((u : A) - a) * star (v : A) + a * star ((v : A) - b) := by
    rw [star_sub, sub_mul, mul_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖((u : A) - a) * star (v : A)‖ + ‖a * star ((v : A) - b)‖ := norm_add_le _ _
    _ = ‖(u : A) - a‖ + ‖a * star ((v : A) - b)‖ := by
      rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary]
    _ ≤ d + B * d := add_le_add hu
      ((norm_mul_le _ _).trans (mul_le_mul ha (by simpa only [norm_star] using hv)
        (norm_nonneg _) hB))
    _ = _ := by ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_TypeIIISmoothing
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.ScalarInvariantMean.conjugationFamily_apply _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Uniform exact normalizers from quantitative smoothing data

All radii and constants are chosen before the Hilbert space and factor.
The smoothing hypotheses give continuous approximate inverses with
controlled algebra distance and strong-star convergence.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

private theorem exists_smoothing_radius {e0 L : ℝ} (he0 : 0 < e0) (hL : 0 < L) :
    ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r < r0 →
      r < 1 / 8 ∧ 50 * r < e0 ∧ L * r < 1 / 1000 ∧ 2 * r + L * r < 1 := by
  let r0 := min (1 / 8) (min (e0 / 50) (1 / (1000 * (L + 2))))
  have hp : 0 < r0 := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  refine ⟨r0, hp, ?_⟩
  intro r hr hsmall
  have h₁ := hsmall.trans_le (min_le_left _ _)
  have h₂ := hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have h₃ := hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  change r < 1 / (1000 * (L + 2)) at h₃
  have hmul := (lt_div_iff₀ (show 0 < 1000 * (L + 2) by positivity)).mp h₃
  refine ⟨h₁, ?_, ?_, ?_⟩ <;> change r < e0 / 50 at h₂ <;> nlinarith

attribute [local instance] OAI.KadisonKastler.smoothingInputOrder
attribute [local instance] OAI.KadisonKastler.smoothingInputStarOrder
theorem uniform_typeIII_normalizer_from_smoothing_oai
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (hSakai : PublishedSimpleDerivationInner.{u})
    (hDistance : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H], ∀ M : VonNeumannAlgebra H,
        PublishedBlockCommutantApproximation (Algebra M) H) :
    ∃ r0 C : ℝ, 0 < r0 ∧ 0 < C ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] [Nontrivial H] [TopologicalSpace.SeparableSpace H],
      ∀ (M : VonNeumannAlgebra H), TypeIIIFactor M →
      ∀ (W : ℝ → unitary (H →L[ℂ] H)), W 0 = 1 →
      (∀ t, PublishedMultiplicationCorrection (unitaryConjugateAlgebra (W t) M)) →
      ∀ (a c D : ℕ → ℝ → H →L[ℂ] H) (r : ℝ), 0 < r → r < r0 →
      (∀ n, Continuous (a n)) →
      (∀ n t, ‖a n t‖ ≤ 1 + r) → (∀ n t, ‖c n t‖ ≤ 1 + r) →
      (∀ n t, ‖a n t * c n t - 1‖ ≤ r) → (∀ n t, ‖c n t * a n t - 1‖ ≤ r) →
      (∀ n t x, x ∈ unitBall M →
        Metric.infDist (a n t * x * c n t) (M : Set (H →L[ℂ] H)) ≤ r) →
      (∀ n t x, x ∈ unitBall M →
        Metric.infDist (c n t * x * a n t) (M : Set (H →L[ℂ] H)) ≤ r) →
      (∀ n t, ‖D n t‖ ≤ 2) → (∀ n t, ‖a n t - D n t‖ ≤ r) →
      (∀ t x, Tendsto (fun n => D n t x) atTop (𝓝 ((W t : H →L[ℂ] H) x))) →
      (∀ t x, Tendsto (fun n => star (D n t) x) atTop (𝓝 (star (W t : H →L[ℂ] H) x))) →
      (∀ t, kkDistance (unitaryConjugateAlgebra (W t) M) M < 2 * r) →
      ∀ t, ∃ v : unitary (H →L[ℂ] H), Conjugates v M M ∧
        ‖(v : H →L[ℂ] H) - W t‖ ≤ C * r := by
  obtain ⟨e0, K, he0, hK, hnormalizer⟩ := uniform_typeIII_smoothed_normalizers
    hSpectral hCompare hSakai hDistance
  let L := 5 * (50 * (K + 1) + 15)
  have hL : 0 < L := by dsimp [L] <;> positivity
  obtain ⟨r0, hr0, hsmall⟩ := exists_smoothing_radius he0 hL
  refine ⟨r0, 128 * L, hr0, by positivity, ?_⟩
  intro H _ _ _ _ _ M hM W hW0 hCorrection a c D r hr hrr ha han hcn hac hca
    halg hcalg hDn haD hD hDs hgap t
  obtain ⟨hrsmall, he, hLs, hgs⟩ := hsmall r hr hrr
  choose v E hv hE hE0 hEv hva hvc hdef using fun n =>
    exists_based_polar_normalizer_path M (a n) (c n) (ha n) hr.le hrsmall
      (han n) (hcn n) (hac n) (hca n) (halg n) (hcalg n)
  let Q (n : ℕ) := D n t * star (D n 0)
  have hQn (n : ℕ) : ‖Q n‖ ≤ 4 := by
    exact (norm_mul_le _ _).trans ((mul_le_mul (hDn n t)
      ((norm_star _).le.trans (hDn n 0)) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num))
  have hQstar (x : H) : Tendsto (fun n => star (Q n) x) atTop
      (𝓝 (star (W t : H →L[ℂ] H) x)) := by
    have hh := tendsto_operator_comp_of_uniform_bound
      (fun n => D n 0) (fun n => star (D n t))
      (W 0) (star (W t : H →L[ℂ] H)) 2 (Eventually.of_forall fun n => hDn n 0)
      (hD 0) (hDs t) x
    simpa only [Q, star_mul, star_star, hW0, OneMemClass.coe_one, one_mul] using hh
  have hvD (n : ℕ) (s : ℝ) : ‖(v n s : H →L[ℂ] H) - D n s‖ ≤ 5 * r :=
    (norm_sub_le_norm_sub_add_norm_sub _ (a n s) _).trans
      ((add_le_add (hva n s) (haD n s)).trans_eq (by ring))
  have hEQ (n : ℕ) : ‖(E n t : H →L[ℂ] H) - Q n‖ ≤ 15 * r := by
    rw [hEv]
    exact (norm_unitary_product_sub_le (v n t) (v n 0) (D n t) (D n 0)
      (by norm_num) (hvD n t) (hvD n 0) (hDn n t)).trans_eq (by ring)
  have hsmall' : (1 + 4) * ((K + 1) * (50 * r) + 15 * r) < 1 / 1000 := by
    convert hLs using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [L]
    ring
  have hge' : 2 * r + (1 + 4) * ((K + 1) * (50 * r) + 15 * r) < 1 := by
    convert hgs using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [L]
    ring
  obtain ⟨p, hp, hpn⟩ := hnormalizer H M hM (W t) (hCorrection t) E Q t (50 * r)
    (15 * r) 4 (2 * r) (by positivity) he (by positivity) (by norm_num)
    hE hE0 hdef hQstar hEQ hQn hsmall' hge' (hgap t)
  refine ⟨p, hp, ?_⟩
  convert hpn using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [L]
  ring

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.uniform_typeIII_normalizer_from_smoothing_oai.{u} := @OAI.KadisonKastler.uniform_typeIII_normalizer_from_smoothing_oai.{u}
