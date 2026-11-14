-- Prove2me | solution 1 for OAI.KadisonKastler.doubleGaussianStateAverage_second_shift
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T11:42:54.52572+00:00
-- url     : https://prove2.me/submissions/c213ef9d-39b5-4ce0-ad30-00e16765a819

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
import Mathlib.Analysis.Complex.CauchyIntegral
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
import Theorems.Thm_OAI_KadisonKastler_gaussianStateAverage_kms_boundary

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConjugationIntegral
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Conjugating a vectorwise weighted operator integral -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {S H : Type*} [MeasurableSpace S]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem unitaryConj_weightedOperatorIntegral
    (μ : Measure S) (w : S → ℂ) (hw : Integrable w μ)
    (F : S → H →L[ℂ] H)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (C : ℝ) (hb : ∀ᵐ t ∂μ, ‖F t‖ ≤ C) (u : unitary (H →L[ℂ] H)) (x : H) :
    unitaryConj u (weightedOperatorIntegral μ w hw F hm C hb) x =
      ∫ t, w t • unitaryConj u (F t) x ∂μ := by
  change (u : H →L[ℂ] H) (∫ t, w t • F t (star (u : H →L[ℂ] H) x) ∂μ) = _
  rw [← (u : H →L[ℂ] H).integral_comp_comm
    (integrable_weighted_operator_vector μ w hw F hm C hb _)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => (u : H →L[ℂ] H).map_smul (w t) _

theorem unitaryConj_commute (u v : unitary (H →L[ℂ] H))
    (hc : Commute (u : H →L[ℂ] H) (v : H →L[ℂ] H)) (a : H →L[ℂ] H) :
    unitaryConj u (unitaryConj v a) = unitaryConj v (unitaryConj u a) := by
  rw [← unitaryConj_mul, ← unitaryConj_mul]
  have he : u * v = v * u := Subtype.ext hc.eq
  rw [he]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_EntireRealUniqueness
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Equality of entire functions from their real restrictions -/

namespace KadisonKastler

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem entire_eq_of_real {f g : ℂ → E} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (he : ∀ t : ℝ, f t = g t) : f = g := by
  apply (Complex.analyticOnNhd_univ_iff_differentiable.mpr hf).eq_of_frequently_eq
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hg) (z₀ := 0)
  apply mem_closure_ne_iff_frequently_within.mp
  rw [Metric.mem_closure_iff]
  intro ε hε
  refine ⟨((ε / 2 : ℝ) : ℂ), ⟨he _, ?_⟩, ?_⟩
  · simp only [Set.mem_singleton_iff, Complex.ofReal_eq_zero]
    positivity
  · simpa only [dist_zero_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < ε / 2)] using (half_lt_self hε)

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
-- module Solutions.OAIQ075_KS.KadisonKastler_GaussianKMSShift
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The imaginary KMS shift for all points of an entire Gaussian orbit -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (Ω : H)
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem gaussianStateAverage_kms_shift
    (hnormal : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)
    (hkms : VectorStateKMS M Ω U) (a : H →L[ℂ] H) (ha : a ∈ M)
    (b : H →L[ℂ] H) (hb : b ∈ M) (r : ℝ) (hr : 0 < r) (z : ℂ) :
    productVectorState Ω (gaussianStateAverage U hU a r hr (z + Complex.I) * b) =
      productVectorState Ω (b * gaussianStateAverage U hU a r hr z) := by
  have hl := (gaussianStateAverage_coefficient_differentiable U hU a r hr (b Ω) Ω).comp
    (show Differentiable ℂ (fun w : ℂ => w + Complex.I) from differentiable_id.add_const _)
  have hr' := (innerSL ℂ Ω).differentiable.comp
    (b.differentiable.comp (gaussianStateAverage_vector_differentiable U hU a r hr Ω))
  have he := entire_eq_of_real hl hr' (fun t =>
    gaussianStateAverage_kms_boundary Ω U hU hnormal hkms a ha b hb r hr t)
  exact congrFun he z

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GaussianStateCoefficient
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Scalar coefficients and equivariance of Gaussian averages -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem gaussianStateAverage_mul_right (Ω : H) (a b : H →L[ℂ] H)
    (r : ℝ) (hr : 0 < r) (z : ℂ) :
    productVectorState Ω (gaussianStateAverage U hU a r hr z * b) =
      ∫ t : ℝ, gaussianStateKernel r z t * productVectorState Ω (stateActionOrbit U a t * b) := by
  have hi := integrable_weighted_operator_vector volume (gaussianStateKernel r z)
    (gaussianStateKernel_integrable hr z) (stateActionOrbit U a)
    (fun x => (stateActionOrbit_continuous U hU a x).aestronglyMeasurable)
    ‖a‖ (Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le) (b Ω)
  change (innerSL ℂ Ω) (∫ t, gaussianStateKernel r z t • stateActionOrbit U a t (b Ω)) = _
  rw [← (innerSL ℂ Ω).integral_comp_comm hi]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => inner_smul_right _ _ _

theorem gaussianStateAverage_mul_left (Ω : H) (a b : H →L[ℂ] H)
    (r : ℝ) (hr : 0 < r) (z : ℂ) :
    productVectorState Ω (b * gaussianStateAverage U hU a r hr z) =
      ∫ t : ℝ, gaussianStateKernel r z t * productVectorState Ω (b * stateActionOrbit U a t) := by
  have hi := integrable_weighted_operator_vector volume (gaussianStateKernel r z)
    (gaussianStateKernel_integrable hr z) (stateActionOrbit U a)
    (fun x => (stateActionOrbit_continuous U hU a x).aestronglyMeasurable)
    ‖a‖ (Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le) Ω
  change ((innerSL ℂ Ω).comp b) (∫ t, gaussianStateKernel r z t • stateActionOrbit U a t Ω) = _
  rw [← ((innerSL ℂ Ω).comp b).integral_comp_comm hi]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => ((innerSL ℂ Ω).comp b).map_smul (gaussianStateKernel r z t) _

theorem gaussianStateAverage_conjugate (a : H →L[ℂ] H)
    (u : unitary (H →L[ℂ] H)) (hc : ∀ t, Commute (u : H →L[ℂ] H) (U t : H →L[ℂ] H))
    (r : ℝ) (hr : 0 < r) (z : ℂ) :
    unitaryConj u (gaussianStateAverage U hU a r hr z) =
      gaussianStateAverage U hU (unitaryConj u a) r hr z := by
  apply ContinuousLinearMap.ext
  intro x
  rw [gaussianStateAverage, unitaryConj_weightedOperatorIntegral]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [stateActionOrbit, unitaryConj_commute u _ (hc _) a]
  rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DoubleGaussianKMS
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # KMS shifts in both coordinates of a doubly averaged element -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (Ω : H)
  (U V : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (hV : ∀ x, Continuous (fun t : ℝ => (V (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem doubleGaussianStateAverage_second_shift_oai
    (hnU : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)
    (hcomm : ∀ s t, Commute (U s : H →L[ℂ] H) (V t : H →L[ℂ] H))
    (hnV : ∀ t a, a ∈ M → unitaryConj (V t) a ∈ M)
    (hKV : VectorStateKMS M Ω V) (a b : H →L[ℂ] H) (ha : a ∈ M) (hb : b ∈ M)
    (r : ℝ) (hr : 0 < r) (z w : ℂ) :
    productVectorState Ω (doubleGaussianStateAverage U V hU hV a r hr z (w + Complex.I) * b) =
      productVectorState Ω (b * doubleGaussianStateAverage U V hU hV a r hr z w) := by
  unfold doubleGaussianStateAverage
  rw [gaussianStateAverage_mul_right, gaussianStateAverage_mul_left]
  apply integral_congr_ae
  filter_upwards [] with t
  unfold stateActionOrbit
  rw [gaussianStateAverage_conjugate V hV a _ (hcomm _) r hr (w + Complex.I),
    gaussianStateAverage_conjugate V hV a _ (hcomm _) r hr w]
  rw [gaussianStateAverage_kms_shift Ω V hV hnV hKV _ (hnU _ a ha) b hb r hr w]

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.doubleGaussianStateAverage_second_shift_oai.{u_1} := @OAI.KadisonKastler.doubleGaussianStateAverage_second_shift_oai.{u_1}
