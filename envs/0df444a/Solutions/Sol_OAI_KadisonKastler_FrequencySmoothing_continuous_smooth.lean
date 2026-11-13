-- Prove2me | solution 1 for OAI.KadisonKastler.FrequencySmoothing.continuous_smooth
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:58:21.413199+00:00
-- url     : https://prove2.me/submissions/5394545d-2bac-4df3-9070-2fe78afa41ee

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
import Definitions.Def_Q260K012
import Definitions.Def_Q260K013

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PoissonKernelContinuity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Quantitative translation continuity of the Poisson kernel -/

namespace KadisonKastler

open MeasureTheory ProbabilityTheory

noncomputable section

theorem realPoissonKernel_nonneg (t s : ℝ) {r : ℝ} (hr : 0 < r) :
    0 ≤ realPoissonKernel t r s := by
  unfold realPoissonKernel
  positivity

theorem integral_realPoissonKernel (t : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ s, realPoissonKernel t r s) = 1 := by
  have he : realPoissonKernel t r = cauchyPDFReal t (NNReal.mk r hr.le) :=
    funext fun s => realPoissonKernel_eq_cauchyPDFReal t s hr.le
  rw [he]
  exact integral_cauchyPDFReal_eq_one t (by
    intro h
    have hh : r = 0 := congrArg (fun (z : NNReal) => (z : ℝ)) h
    exact hr.ne' hh)

/-- A pointwise integrable bound for changing the center while keeping
positive height fixed. -/
theorem abs_realPoissonKernel_sub_le (t u s : ℝ) {r : ℝ} (hr : 0 < r) :
    |realPoissonKernel t r s - realPoissonKernel u r s| ≤
      (|t - u| / r) * (realPoissonKernel t r s + realPoissonKernel u r s) := by
  let a := (t - s) ^ 2 + r ^ 2
  let b := (u - s) ^ 2 + r ^ 2
  have ha : 0 < a := by dsimp [a] <;> positivity
  have hb : 0 < b := by dsimp [b] <;> positivity
  have hden : 0 < Real.pi * a * b := by positivity
  have hsum : r * |(u - s) + (t - s)| ≤ a + b := by
    have habs := mul_le_mul_of_nonneg_left (abs_add_le (u - s) (t - s)) hr.le
    have h₁ := sq_nonneg (|t - s| - r)
    have h₂ := sq_nonneg (|u - s| - r)
    dsimp [a, b]
    nlinarith [sq_abs (t - s), sq_abs (u - s), sq_nonneg (t - s), sq_nonneg (u - s)]
  have hab : r * |b - a| ≤ |t - u| * (a + b) := by
    have he : b - a = ((u - s) - (t - s)) * ((u - s) + (t - s)) := by dsimp [a, b] <;> ring
    have hd : (u - s) - (t - s) = u - t := by ring
    rw [he, abs_mul, hd, abs_sub_comm u t]
    nlinarith [mul_le_mul_of_nonneg_left hsum (abs_nonneg (t - u))]
  have hf : realPoissonKernel t r s - realPoissonKernel u r s =
      (r / (Real.pi * a * b)) * (b - a) := by
    change r / (Real.pi * a) - r / (Real.pi * b) = _
    field_simp
  have hg : (|t - u| / r) * (realPoissonKernel t r s + realPoissonKernel u r s) =
      (1 / (Real.pi * a * b)) * (|t - u| * (a + b)) := by
    change (|t - u| / r) * (r / (Real.pi * a) + r / (Real.pi * b)) = _
    field_simp
    ring
  rw [hf, abs_mul, abs_of_pos (div_pos hr hden), hg]
  calc
    (r / (Real.pi * a * b)) * |b - a| =
        (1 / (Real.pi * a * b)) * (r * |b - a|) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hab (by positivity)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MeasurablePoisson
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Poisson integration of bounded vector-measurable operator fields

The analytic multiplier fields need only be measurable on each vector.
These averages therefore use vector integrals, without asserting norm
measurability of a field valued in the bounded operators.
-/

namespace KadisonKastler

open MeasureTheory ProbabilityTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem measurablePoissonAverage_apply (F : ℝ → H →L[ℂ] H)
    (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    (C : ℝ) (hC : ∀ᵐ s, ‖F s‖ ≤ C) (t r : ℝ) (hr : 0 < r) (x : H) :
    measurablePoissonAverage F hF C hC t r hr x =
      ∫ s, realPoissonKernel t r s • F s x := by
  change (∫ s, F s x ∂cauchyMeasure t (NNReal.mk r hr.le)) = _
  rw [cauchyMeasure_of_scale_ne_zero t (by
    intro h
    exact hr.ne' (congrArg (fun (z : NNReal) => (z : ℝ)) h)),
    integral_withDensity_eq_integral_toReal_smul (measurable_cauchyPDF t (NNReal.mk r hr.le))
      (ae_of_all _ fun s => ENNReal.ofReal_lt_top)]
  congr 1
  funext s
  rw [cauchyPDF, ENNReal.toReal_ofReal (cauchyPDF_pos t (by
    intro h
    exact hr.ne' (congrArg (fun (z : NNReal) => (z : ℝ)) h)) s).le,
    ← realPoissonKernel_eq_cauchyPDFReal t s hr.le]

omit [CompleteSpace H] in
private theorem integrable_measurablePoisson_vector
    (F : ℝ → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    {C : ℝ} (hC : ∀ᵐ s, ‖F s‖ ≤ C) (t : ℝ) {r : ℝ} (hr : 0 < r) (x : H) :
    Integrable (fun s => realPoissonKernel t r s • F s x) := by
  have hm : AEStronglyMeasurable (realPoissonKernel t r) volume :=
    (integrable_realPoissonKernel t hr).aestronglyMeasurable
  apply ((integrable_realPoissonKernel t hr).mul_const (C * ‖x‖)).mono' (hm.smul (hF x))
  filter_upwards [hC] with s hs
  change ‖realPoissonKernel t r s • F s x‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (realPoissonKernel_nonneg t s hr)]
  exact mul_le_mul_of_nonneg_left
    (((F s).le_opNorm x).trans (mul_le_mul_of_nonneg_right hs (norm_nonneg x)))
    (realPoissonKernel_nonneg t s hr)

omit [CompleteSpace H] in
/-- An essentially bounded vector-measurable boundary field yields an
operator-norm Lipschitz function on every horizontal line of positive height. -/
theorem norm_measurablePoissonAverage_translate_sub_le
    (F : ℝ → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ᵐ s, ‖F s‖ ≤ C)
    (t u r : ℝ) (hr : 0 < r) :
    ‖measurablePoissonAverage F hF C hC t r hr -
      measurablePoissonAverage F hF C hC u r hr‖ ≤ (2 * C / r) * |t - u| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  change ‖measurablePoissonAverage F hF C hC t r hr x -
    measurablePoissonAverage F hF C hC u r hr x‖ ≤ _
  rw [measurablePoissonAverage_apply, measurablePoissonAverage_apply,
    ← integral_sub (integrable_measurablePoisson_vector F hF hC t hr x)
      (integrable_measurablePoisson_vector F hF hC u hr x)]
  have hi := ((integrable_realPoissonKernel t hr).add
    (integrable_realPoissonKernel u hr)).const_mul (|t - u| / r)
  have hb : ‖∫ s, realPoissonKernel t r s • F s x -
      realPoissonKernel u r s • F s x‖ ≤
      ∫ s, ((|t - u| / r) * (realPoissonKernel t r s + realPoissonKernel u r s)) *
        (C * ‖x‖) := by
    apply norm_integral_le_of_norm_le (hi.mul_const (C * ‖x‖))
    filter_upwards [hC] with s hs
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (abs_realPoissonKernel_sub_le t u s hr)
      (((F s).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right hs (norm_nonneg x)))
      (norm_nonneg _) (mul_nonneg (div_nonneg (abs_nonneg _) hr.le)
        (add_nonneg (realPoissonKernel_nonneg t s hr) (realPoissonKernel_nonneg u s hr)))
  calc
    _ ≤ _ := hb
    _ = (2 * C / r) * |t - u| * ‖x‖ := by
      rw [integral_mul_const, integral_const_mul,
        integral_add (integrable_realPoissonKernel t hr) (integrable_realPoissonKernel u hr),
        integral_realPoissonKernel t hr, integral_realPoissonKernel u hr]
      ring

omit [CompleteSpace H] in
theorem continuous_measurablePoissonAverage
    (F : ℝ → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ᵐ s, ‖F s‖ ≤ C)
    (r : ℝ) (hr : 0 < r) :
    Continuous (fun t => measurablePoissonAverage F hF C hC t r hr) := by
  have h : LipschitzWith (NNReal.mk (2 * C / r) (by positivity))
      (fun t => measurablePoissonAverage F hF C hC t r hr) := by
    apply LipschitzWith.of_dist_le_mul
    intro t u
    rw [dist_eq_norm, Real.dist_eq]
    exact norm_measurablePoissonAverage_translate_sub_le F hF hC0 hC t u r hr
  exact h.continuous

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DemodulatedPoisson
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The actual demodulated smoothing fields

These are the fields used before polar decomposition. An essential bound
on the boundary, or an essential comparison with the modulated modular
unitaries, passes to a uniform norm bound at every positive height.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem continuous_demodulatedPoissonAverage
    (F : ℝ → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ᵐ s, ‖F s‖ ≤ C) (r : ℝ) (hr : 0 < r) :
    Continuous (fun t => demodulatedPoissonAverage F hF C hC t r hr) := by
  have hc : Continuous (fun t : ℝ => (Real.exp r : ℂ) * star (Circle.exp t : ℂ)) :=
    continuous_const.mul (continuous_subtype_val.comp Circle.exp.continuous).star
  exact hc.smul (continuous_measurablePoissonAverage F hF hC0 hC r hr)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FrequencySmoothing
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

local instance frequencySmoothingOrder_rec8ac4_1 (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance frequencySmoothingStarOrder_rec8ac4_1 (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
variable {F G : ℝ → H →L[ℂ] H} {δ : ℝ}

theorem continuous_smooth_oai (A : FrequencySmoothing F δ) (hδ : 0 ≤ δ)
    (r : ℝ) (hr : 0 < r) : Continuous (fun t => A.smooth t r hr) :=
  continuous_demodulatedPoissonAverage A.boundary A.measurable (by positivity) A.bounded r hr

end FrequencySmoothing

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.FrequencySmoothing.continuous_smooth_oai.{u} := @OAI.KadisonKastler.FrequencySmoothing.continuous_smooth_oai.{u}
