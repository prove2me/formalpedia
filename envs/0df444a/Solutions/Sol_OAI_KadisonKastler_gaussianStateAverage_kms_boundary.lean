-- Prove2me | solution 1 for OAI.KadisonKastler.gaussianStateAverage_kms_boundary
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T11:42:56.619129+00:00
-- url     : https://prove2.me/submissions/bca8d007-4e5f-4a60-b67a-92282fbf9637

import Mathlib
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Continuous
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
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
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
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
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
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
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
import Definitions.Def_Q260K019

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GaussianStateKernel
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Gaussian kernels for analytic smearing of a state-preserving action -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

theorem gaussianStateKernel_translate (r : ℝ) (z : ℂ) (s t : ℝ) :
    gaussianStateKernel r (z + s) t = gaussianStateKernel r z (t - s) := by
  unfold gaussianStateKernel
  congr 2
  push_cast
  ring

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GaussianStateAverage
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Gaussian averages of strongly continuous algebra actions -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem gaussianStateAverage_mem (M : VonNeumannAlgebra H)
    (hnormal : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)
    (a : H →L[ℂ] H) (ha : a ∈ M) (r : ℝ) (hr : 0 < r) (z : ℂ) :
    gaussianStateAverage U hU a r hr z ∈ M :=
  weightedOperatorIntegral_mem volume (gaussianStateKernel r z) (gaussianStateKernel_integrable hr z)
    (stateActionOrbit U a) (fun x => (stateActionOrbit_continuous U hU a x).aestronglyMeasurable)
    ‖a‖ (Filter.Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le) M
    (Filter.Eventually.of_forall fun _ => hnormal _ _ ha)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GaussianStateBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Locally uniform bounds for analytic Gaussian kernels -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

theorem gaussianStateKernel_hasDerivAt (r : ℝ) (t : ℝ) (z : ℂ) :
    HasDerivAt (fun w => gaussianStateKernel r w t) (gaussianStateKernelDeriv r z t) z := by
  have h0 : HasDerivAt (fun w : ℂ => (t : ℂ) - w) (-1) z := by
    exact (hasDerivAt_id z).const_sub (t : ℂ)
  have h1 : HasDerivAt (fun w : ℂ => -(r : ℂ) * ((t : ℂ) - w) ^ 2)
      (-(r : ℂ) * (2 * ((t : ℂ) - z) ^ 1 * (-1))) z :=
    (h0.pow 2).const_mul (-(r : ℂ))
  have h : HasDerivAt (fun w : ℂ => -(r : ℂ) * ((t : ℂ) - w) ^ 2)
      (2 * (r : ℂ) * ((t : ℂ) - z)) z := by
    convert h1 using 1 <;> first | rfl | ring
  simpa only [gaussianStateKernel, gaussianStateKernelDeriv, mul_comm] using h.cexp

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GaussianVectorAnalytic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Entire vector-valued Gaussian smearing -/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
  (F : ℝ → H) (hF : Continuous F) (C : ℝ) (hbound : ∀ t, ‖F t‖ ≤ C)
  (r : ℝ) (hr : 0 < r)

omit [CompleteSpace H] in
include hF hbound hr in
theorem gaussianVector_integrable (z : ℂ) :
    Integrable (fun t => gaussianStateKernel r z t • F t) := by
  have hc : Continuous (gaussianStateKernel r z) := by unfold gaussianStateKernel; fun_prop
  apply ((gaussianStateKernel_integrable hr z).norm.mul_const C).mono'
    (hc.aestronglyMeasurable.smul hF.aestronglyMeasurable)
  exact Eventually.of_forall fun t => by
    change ‖gaussianStateKernel r z t • F t‖ ≤ _
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hbound t) (norm_nonneg _)

omit [CompleteSpace H] in
include hF hbound hr in
theorem gaussianVector_hasDerivAt (z : ℂ) :
    HasDerivAt (fun w : ℂ => ∫ t : ℝ, gaussianStateKernel r w t • F t)
      (∫ t : ℝ, gaussianStateKernelDeriv r z t • F t) z := by
  let R := ‖z‖ + 1
  let S := Metric.ball z 1
  have hR : 0 ≤ R := by dsimp [R] <;> positivity
  have hS : S ∈ 𝓝 z := Metric.ball_mem_nhds z zero_lt_one
  have hnorm {w : ℂ} (hw : w ∈ S) : ‖w‖ ≤ R := by
    have hd : dist w z < 1 := hw
    have hn : ‖w‖ ≤ ‖z‖ + dist w z := by
      calc
        ‖w‖ = ‖z + (w - z)‖ := by rw [add_sub_cancel]
        _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
        _ = ‖z‖ + dist w z := by rw [dist_eq_norm]
    dsimp [R]
    linarith
  let B : ℝ → ℝ := fun t =>
    (2 * r * Real.exp (2 * r * R ^ 2)) *
      ((|t| + R) * Real.exp (-(r / 2) * t ^ 2))
  have hB : Integrable (fun t => B t * C) :=
    (gaussianStateKernelDeriv_bound_integrable hr R).mul_const C
  have hm (w : ℂ) : AEStronglyMeasurable (fun t => gaussianStateKernel r w t • F t) := by
    have hc : Continuous (gaussianStateKernel r w) := by unfold gaussianStateKernel; fun_prop
    exact hc.aestronglyMeasurable.smul hF.aestronglyMeasurable
  have hmd : AEStronglyMeasurable (fun t => gaussianStateKernelDeriv r z t • F t) := by
    have hc : Continuous (gaussianStateKernelDeriv r z) := by
      unfold gaussianStateKernelDeriv gaussianStateKernel
      fun_prop
    exact hc.aestronglyMeasurable.smul hF.aestronglyMeasurable
  have hb : ∀ᵐ t : ℝ, ∀ w ∈ S, ‖gaussianStateKernelDeriv r w t • F t‖ ≤ B t * C := by
    filter_upwards [] with t w hw
    rw [norm_smul]
    exact mul_le_mul (gaussianStateKernelDeriv_local_bound hr hR (hnorm hw) t)
      (hbound t) (norm_nonneg _) (by dsimp [B] <;> positivity)
  have hd : ∀ᵐ t : ℝ, ∀ w ∈ S,
      HasDerivAt (fun w => gaussianStateKernel r w t • F t)
        (gaussianStateKernelDeriv r w t • F t) w := by
    filter_upwards [] with t w _
    exact (gaussianStateKernel_hasDerivAt r t w).smul_const (F t)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hS
    (Eventually.of_forall hm) (gaussianVector_integrable F hF C hbound r hr z)
    hmd hb hB hd).2

omit [CompleteSpace H] in
include hF hbound hr in
theorem gaussianVector_differentiable :
    Differentiable ℂ (fun z : ℂ => ∫ t : ℝ, gaussianStateKernel r z t • F t) :=
  fun z => (gaussianVector_hasDerivAt F hF C hbound r hr z).differentiableAt

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GaussianStateAnalytic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Entire coefficients of the concrete Gaussian operator average -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem gaussianStateAverage_vector_differentiable
    (a : H →L[ℂ] H) (r : ℝ) (hr : 0 < r) (x : H) :
    Differentiable ℂ (fun z : ℂ => gaussianStateAverage U hU a r hr z x) := by
  apply gaussianVector_differentiable
    (fun t => stateActionOrbit U a t x) (stateActionOrbit_continuous U hU a x)
    (‖a‖ * ‖x‖) ?_ r hr
  intro t
  exact ((stateActionOrbit U a t).le_opNorm x).trans_eq (by rw [stateActionOrbit_norm])

theorem gaussianStateAverage_coefficient_differentiable
    (a : H →L[ℂ] H) (r : ℝ) (hr : 0 < r) (x y : H) :
    Differentiable ℂ (fun z : ℂ => inner ℂ y (gaussianStateAverage U hU a r hr z x)) :=
  (innerSL ℂ y).differentiable.comp (gaussianStateAverage_vector_differentiable U hU a r hr x)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GaussianStateCovariance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Real-translation covariance of the Gaussian analytic orbit -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem stateActionOrbit_add (a : H →L[ℂ] H) (s t : ℝ) :
    stateActionOrbit U a (s + t) =
      unitaryConj (U (Multiplicative.ofAdd s)) (stateActionOrbit U a t) := by
  change unitaryConj (U (Multiplicative.ofAdd s * Multiplicative.ofAdd t)) a = _
  rw [map_mul, unitaryConj_mul]
  rfl

theorem gaussianStateAverage_covariance
    (a : H →L[ℂ] H) (r : ℝ) (hr : 0 < r) (z : ℂ) (s : ℝ) :
    unitaryConj (U (Multiplicative.ofAdd s)) (gaussianStateAverage U hU a r hr z) =
      gaussianStateAverage U hU a r hr (z + s) := by
  apply ContinuousLinearMap.ext
  intro x
  let u := U (Multiplicative.ofAdd s)
  have hI := integrable_weighted_operator_vector volume (gaussianStateKernel r z)
    (gaussianStateKernel_integrable hr z) (stateActionOrbit U a)
    (fun y => (stateActionOrbit_continuous U hU a y).aestronglyMeasurable)
    ‖a‖ (Filter.Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le)
    (star (u : H →L[ℂ] H) x)
  change (u : H →L[ℂ] H) (∫ t : ℝ, gaussianStateKernel r z t •
      stateActionOrbit U a t (star (u : H →L[ℂ] H) x)) =
    ∫ t : ℝ, gaussianStateKernel r (z + s) t • stateActionOrbit U a t x
  rw [← (u : H →L[ℂ] H).integral_comp_comm hI]
  calc
    (∫ t : ℝ, (u : H →L[ℂ] H) (gaussianStateKernel r z t •
        stateActionOrbit U a t (star (u : H →L[ℂ] H) x))) =
      ∫ t : ℝ, gaussianStateKernel r z t • stateActionOrbit U a (s + t) x := by
        apply integral_congr_ae
        filter_upwards [] with t
        rw [map_smul, stateActionOrbit_add]
        rfl
    _ = ∫ t : ℝ, gaussianStateKernel r (z + s) (s + t) • stateActionOrbit U a (s + t) x := by
        apply integral_congr_ae
        filter_upwards [] with t
        rw [gaussianStateKernel_translate, add_sub_cancel_left]
    _ = _ := integral_add_left_eq_self
      (fun t : ℝ => gaussianStateKernel r (z + s) t • stateActionOrbit U a t x) s

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StripBoundaryUniqueness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Uniqueness from one boundary of a holomorphic strip -/

namespace KadisonKastler

open Complex Set Filter
open scoped Topology

noncomputable section

/-- A continuous holomorphic strip is determined by its lower boundary. -/
theorem strip_eq_zero_of_lower_boundary {f : ℂ → ℂ}
    (hc : ContinuousOn f {z | 0 ≤ z.im ∧ z.im ≤ 1})
    (hd : DifferentiableOn ℂ f {z | 0 < z.im ∧ z.im < 1})
    (hzero : ∀ t : ℝ, f t = 0) :
    ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 1 → f z = 0 := by
  let S : Set ℂ := {z | -1 < z.im ∧ z.im < 1}
  have hopen : IsOpen S := isOpen_Ioo.preimage continuous_im
  have hseam {z : ℂ} (hz : z.im = 0) : f z = 0 := by
    have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz]
    rw [he, hzero]
  have hcont : ContinuousOn (stripZeroExtension f) S := by
    apply ContinuousOn.if
    · intro z hz
      have hz' : z.im = 0 := by
        have hf := hz.2
        change z ∈ frontier (im ⁻¹' Ici (0 : ℝ)) at hf
        rw [frontier_preimage_im, frontier_Ici] at hf
        exact hf
      exact hseam hz'
    · apply hc.mono
      intro z hz
      have hcl : 0 ≤ z.im := by
        have hh : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_Ici.preimage continuous_im
        have hhx := hz.2
        rw [hh.closure_eq] at hhx
        exact hhx
      exact ⟨hcl, hz.1.2.le⟩
    · exact continuousOn_const
  have hdiff : DifferentiableOn ℂ (stripZeroExtension f) S := by
    apply differentiableOn_horizontal_strip_glue (s := 0) (by norm_num) (by norm_num) hcont
    intro z hzlo hzhi hzne
    by_cases hz : 0 < z.im
    · apply (hd.differentiableAt ((isOpen_Ioo.preimage continuous_im).mem_nhds
        ⟨hz, hzhi⟩)).congr_of_eventuallyEq
      filter_upwards [(isOpen_Ioi.preimage continuous_im).mem_nhds hz] with w hw
      exact ite_eq_left hw.le
    · have hneg : z.im < 0 := lt_of_le_of_ne (le_of_not_gt hz) hzne
      apply (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq
      filter_upwards [(isOpen_Iio.preimage continuous_im).mem_nhds hneg] with w hw
      exact ite_eq_right (not_le.mpr hw)
  have hconn : IsPreconnected S := by
    exact ((convex_Ioo (-1 : ℝ) 1).linear_preimage imLm).isPreconnected
  have hbase : (-I / 2 : ℂ) ∈ S := by norm_num [S]
  have hevent : stripZeroExtension f =ᶠ[𝓝 (-I / 2 : ℂ)] 0 := by
    filter_upwards [(isOpen_Iio.preimage continuous_im).mem_nhds
      (show (-I / 2 : ℂ).im < 0 by norm_num)] with w hw
    exact ite_eq_right (not_le.mpr hw)
  have hall := (hdiff.analyticOnNhd hopen).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    hconn hbase hevent
  have hinner : EqOn f 0 (im ⁻¹' Ioo (0 : ℝ) 1) := by
    intro z hz
    have h := hall (show z ∈ S from ⟨by linarith [hz.1], hz.2⟩)
    simpa only [stripZeroExtension, ite_eq_left hz.1.le] using h
  have hclosure : closure (im ⁻¹' Ioo (0 : ℝ) 1) = {z : ℂ | 0 ≤ z.im ∧ z.im ≤ 1} := by
    rw [closure_preimage_im, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    rfl
  have he := hinner.of_subset_closure hc continuousOn_const
    (fun z hz => ⟨hz.1.le, hz.2.le⟩) (by rw [hclosure])
  intro z hzlo hzhi
  exact he ⟨hzlo, hzhi⟩

theorem strip_eq_of_lower_boundary {f g : ℂ → ℂ}
    (hfc : ContinuousOn f {z | 0 ≤ z.im ∧ z.im ≤ 1})
    (hfd : DifferentiableOn ℂ f {z | 0 < z.im ∧ z.im < 1})
    (hgc : ContinuousOn g {z | 0 ≤ z.im ∧ z.im ≤ 1})
    (hgd : DifferentiableOn ℂ g {z | 0 < z.im ∧ z.im < 1})
    (he : ∀ t : ℝ, f t = g t) :
    ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 1 → f z = g z := by
  have h := strip_eq_zero_of_lower_boundary (hfc.sub hgc) (hfd.sub hgd)
    (fun t => sub_eq_zero.mpr (he t))
  intro z hzlo hzhi
  exact sub_eq_zero.mp (h z hzlo hzhi)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GaussianKMSBoundary
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The KMS identity on concrete entire Gaussian elements -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (Ω : H)
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem gaussianStateAverage_kms_boundary_oai
    (hnormal : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)
    (hkms : VectorStateKMS M Ω U) (a : H →L[ℂ] H) (ha : a ∈ M)
    (b : H →L[ℂ] H) (hb : b ∈ M) (r : ℝ) (hr : 0 < r) (t : ℝ) :
    productVectorState Ω (gaussianStateAverage U hU a r hr ((t : ℂ) + Complex.I) * b) =
      productVectorState Ω (b * gaussianStateAverage U hU a r hr t) := by
  let A := gaussianStateAverage U hU a r hr
  let f : ℂ → ℂ := fun z => productVectorState Ω (A z * b)
  have hfd : Differentiable ℂ f :=
    gaussianStateAverage_coefficient_differentiable U hU a r hr (b Ω) Ω
  obtain ⟨g, hgc, hgd, _, hlo, hhi⟩ := hkms (A 0)
    (gaussianStateAverage_mem U hU M hnormal a ha r hr 0) b hb
  have hreal (s : ℝ) : g s = f s := by
    rw [hlo]
    dsimp [f, A]
    rw [gaussianStateAverage_covariance, zero_add]
  have he := strip_eq_of_lower_boundary hgc hgd hfd.continuous.continuousOn
    hfd.differentiableOn hreal ((t : ℂ) + Complex.I) (by simp) (by simp)
  change f ((t : ℂ) + Complex.I) = _
  rw [← he, hhi]
  dsimp [A]
  rw [gaussianStateAverage_covariance, zero_add]

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.gaussianStateAverage_kms_boundary_oai.{u_1} := @OAI.KadisonKastler.gaussianStateAverage_kms_boundary_oai.{u_1}
