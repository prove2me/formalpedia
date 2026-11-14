-- Prove2me | solution 1 for OAI.KadisonKastler.gaussianStateAverage_injective
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T11:42:55.631955+00:00
-- url     : https://prove2.me/submissions/ed5ec619-1dc0-4e29-868a-75d0ba27bb26

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
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
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
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
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
import Mathlib.Probability.Moments.ComplexMGF
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
-- module Solutions.OAIQ075_KS.KadisonKastler_ComplexLocalLaplace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Complex-valued local Laplace uniqueness -/

namespace KadisonKastler

open MeasureTheory Set

noncomputable section

theorem zero_of_complex_local_laplace (f : ℝ → ℂ) (hf : Continuous f)
    {a : ℝ} (ha : 0 < a)
    (hi : ∀ s ∈ Ioo (-a) a, Integrable (fun t => (Real.exp (s * t) : ℂ) * f t))
    (hz : ∀ s ∈ Ioo (-a) a, (∫ t, (Real.exp (s * t) : ℂ) * f t) = 0) :
    f = 0 := by
  have hre : (fun t => (f t).re) = 0 := zero_of_local_laplace _
    (Complex.continuous_re.comp hf) ha
    (fun s hs => by
      simpa only [RCLike.re_eq_complex_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero] using (hi s hs).re)
    (fun s hs => by
      have h := integral_re (hi s hs)
      change (∫ t, ((Real.exp (s * t) : ℂ) * f t).re) =
        (∫ t, (Real.exp (s * t) : ℂ) * f t).re at h
      rw [hz s hs] at h
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, Complex.zero_re] using h)
  have him : (fun t => (f t).im) = 0 := zero_of_local_laplace _
    (Complex.continuous_im.comp hf) ha
    (fun s hs => by
      simpa only [RCLike.im_eq_complex_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero] using (hi s hs).im)
    (fun s hs => by
      have h := integral_im (hi s hs)
      change (∫ t, ((Real.exp (s * t) : ℂ) * f t).im) =
        (∫ t, (Real.exp (s * t) : ℂ) * f t).im at h
      rw [hz s hs] at h
      simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, Complex.zero_im] using h)
  funext t
  exact Complex.ext (congrFun hre t) (congrFun him t)

end

end KadisonKastler

end OAI
end

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

theorem gaussianStateKernel_real (r s t : ℝ) :
    gaussianStateKernel r (s : ℂ) t = (Real.exp (-r * (t - s) ^ 2) : ℂ) := by
  rw [gaussianStateKernel, ← Complex.ofReal_sub, ← Complex.ofReal_pow,
    ← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_exp]

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
-- module Solutions.OAIQ075_KS.KadisonKastler_GaussianSeparation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Gaussian translates separate bounded continuous coefficients -/

namespace KadisonKastler

open MeasureTheory Set

noncomputable section

theorem gaussianStateKernel_tilt (r : ℝ) (hr : 0 < r) (s t : ℝ) :
    (Real.exp (s * t) : ℂ) * gaussianStateKernel r 0 t =
      (Real.exp (s ^ 2 / (4 * r)) : ℂ) * gaussianStateKernel r (s / (2 * r) : ℝ) t := by
  rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) from rfl, gaussianStateKernel_real,
    gaussianStateKernel_real, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  have hne : r ≠ 0 := hr.ne'
  field_simp
  ring

theorem zero_of_gaussian_averages (r : ℝ) (hr : 0 < r) (g : ℝ → ℂ)
    (hg : Continuous g) (B : ℝ) (hB : ∀ t, ‖g t‖ ≤ B)
    (hz : ∀ s : ℝ, (∫ t : ℝ, gaussianStateKernel r s t * g t) = 0) : g = 0 := by
  let f : ℝ → ℂ := fun t => gaussianStateKernel r 0 t * g t
  have hc : Continuous f := by
    apply Continuous.mul _ hg
    unfold gaussianStateKernel
    fun_prop
  have he (s : ℝ) :
      (fun t => (Real.exp (s * t) : ℂ) * f t) =
        fun t => (Real.exp (s ^ 2 / (4 * r)) : ℂ) *
          (gaussianStateKernel r (s / (2 * r) : ℝ) t * g t) := by
    funext t
    dsimp [f]
    rw [← mul_assoc, gaussianStateKernel_tilt r hr, mul_assoc]
  have hi (s : ℝ) : Integrable (fun t => (Real.exp (s * t) : ℂ) * f t) := by
    rw [he]
    exact ((gaussianStateKernel_integrable hr (s / (2 * r) : ℝ)).mul_bdd
      hg.aestronglyMeasurable (Filter.Eventually.of_forall hB)).const_mul _
  have hf : f = 0 := zero_of_complex_local_laplace f hc (a := 1) zero_lt_one
    (fun s _ => hi s) (fun s _ => by rw [he, integral_const_mul, hz, mul_zero])
  funext t
  have h := congrFun hf t
  change gaussianStateKernel r 0 t * g t = 0 at h
  exact (mul_eq_zero.mp h).resolve_left (Complex.exp_ne_zero _)

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
-- module Solutions.OAIQ075_KS.KadisonKastler_GaussianInjective
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Injectivity of Gaussian smearing for a strongly continuous unitary action -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem gaussianStateAverage_eq_zero (a : H →L[ℂ] H) (r : ℝ) (hr : 0 < r)
    (hzero : gaussianStateAverage U hU a r hr 0 = 0) : a = 0 := by
  have hz (s : ℝ) : gaussianStateAverage U hU a r hr s = 0 := by
    have he := gaussianStateAverage_covariance U hU a r hr 0 s
    rw [hzero] at he
    simpa [unitaryConj] using he.symm
  apply ContinuousLinearMap.ext
  intro x
  let y := a x
  let g : ℝ → ℂ := fun t => inner ℂ y (stateActionOrbit U a t x)
  have hg : Continuous g := continuous_const.inner (stateActionOrbit_continuous U hU a x)
  have hb (t : ℝ) : ‖g t‖ ≤ ‖y‖ * (‖a‖ * ‖x‖) := by
    apply (norm_inner_le_norm _ _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg y)
    exact ((stateActionOrbit U a t).le_opNorm x).trans_eq (by rw [stateActionOrbit_norm])
  have hgi (s : ℝ) : (∫ t : ℝ, gaussianStateKernel r s t * g t) = 0 := by
    have hi := integrable_weighted_operator_vector volume (gaussianStateKernel r s)
      (gaussianStateKernel_integrable hr s) (stateActionOrbit U a)
      (fun x => (stateActionOrbit_continuous U hU a x).aestronglyMeasurable)
      ‖a‖ (Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le) x
    calc
      _ = ∫ t : ℝ, (innerSL ℂ y) (gaussianStateKernel r s t • stateActionOrbit U a t x) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun t => (inner_smul_right _ _ _).symm
      _ = (innerSL ℂ y) (gaussianStateAverage U hU a r hr s x) :=
        (innerSL ℂ y).integral_comp_comm hi
      _ = 0 := by rw [hz]; simp
  have he := congrFun (zero_of_gaussian_averages r hr g hg _ hb hgi) 0
  have hv : inner ℂ (a x) (a x) = 0 := by
    simpa [g, y, stateActionOrbit, unitaryConj] using he
  exact inner_self_eq_zero.mp hv

theorem gaussianStateAverage_sub (a b : H →L[ℂ] H) (r : ℝ) (hr : 0 < r) (z : ℂ) :
    gaussianStateAverage U hU (a - b) r hr z =
      gaussianStateAverage U hU a r hr z - gaussianStateAverage U hU b r hr z := by
  apply ContinuousLinearMap.ext
  intro x
  have hi (c : H →L[ℂ] H) := integrable_weighted_operator_vector volume (gaussianStateKernel r z)
    (gaussianStateKernel_integrable hr z) (stateActionOrbit U c)
    (fun y => (stateActionOrbit_continuous U hU c y).aestronglyMeasurable)
    ‖c‖ (Eventually.of_forall fun t => (stateActionOrbit_norm U c t).le) x
  change (∫ t, gaussianStateKernel r z t • stateActionOrbit U (a - b) t x) =
    (∫ t, gaussianStateKernel r z t • stateActionOrbit U a t x) -
      (∫ t, gaussianStateKernel r z t • stateActionOrbit U b t x)
  rw [← integral_sub (hi a) (hi b)]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [stateActionOrbit, unitaryConj, mul_sub, sub_mul,
    sub_apply, smul_sub]

theorem gaussianStateAverage_injective_oai (r : ℝ) (hr : 0 < r) :
    Function.Injective (fun a => gaussianStateAverage U hU a r hr 0) := by
  intro a b hab
  change gaussianStateAverage U hU a r hr 0 = gaussianStateAverage U hU b r hr 0 at hab
  apply sub_eq_zero.mp
  apply gaussianStateAverage_eq_zero U hU (a - b) r hr
  rw [gaussianStateAverage_sub, hab, sub_self]

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.gaussianStateAverage_injective_oai.{u_1} := @OAI.KadisonKastler.gaussianStateAverage_injective_oai.{u_1}
