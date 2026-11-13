-- Prove2me | solution 1 for OAI.KadisonKastler.FrequencySmoothing.norm_product_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:01:25.447206+00:00
-- url     : https://prove2.me/submissions/f0c9b077-fbdc-4def-974d-14e549d2492a

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
import Definitions.Def_Q260K015
import Definitions.Def_Q260K018

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FourierLaplace
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Fourier transform of the two-sided exponential

This scalar calculation is the first half of the Cauchy-kernel character
formula needed for Poisson demodulation. It uses the existing half-line
exponential integrals and no additional published-input hypothesis.
-/

namespace KadisonKastler

open MeasureTheory
open scoped FourierTransform

noncomputable section

/-- The transform is the sum of the two elementary half-line resolvents. -/
theorem fourier_laplaceKernel_resolvents {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    𝓕 (laplaceKernel a) ξ =
      ((a : ℂ) - (2 * Real.pi * ξ : ℝ) * Complex.I)⁻¹ -
        (-(a : ℂ) - (2 * Real.pi * ξ : ℝ) * Complex.I)⁻¹ := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  change (∫ t : ℝ, laplaceFourierIntegrand a ξ t) = _
  rw [← intervalIntegral.integral_Iic_add_Ioi (laplaceFourierIntegrand_integrableOn_left ha ξ)
    (laplaceFourierIntegrand_integrableOn_right ha ξ)]
  have hleft : (∫ t in Set.Iic (0 : ℝ), laplaceFourierIntegrand a ξ t) =
      ((a : ℂ) - (2 * Real.pi * ξ : ℝ) * Complex.I)⁻¹ := by
    calc
      _ = ∫ t in Set.Iic (0 : ℝ),
          Complex.exp (((a : ℂ) - (2 * Real.pi * ξ : ℝ) * Complex.I) * t) := by
        apply setIntegral_congr_fun measurableSet_Iic
        intro t ht
        exact laplaceFourierIntegrand_nonpos a ξ t ht
      _ = _ := by
        rw [integral_exp_mul_complex_Iic (by simpa using ha)]
        simp
  have hright : (∫ t in Set.Ioi (0 : ℝ), laplaceFourierIntegrand a ξ t) =
      - (-(a : ℂ) - (2 * Real.pi * ξ : ℝ) * Complex.I)⁻¹ := by
    calc
      _ = ∫ t in Set.Ioi (0 : ℝ),
          Complex.exp ((-(a : ℂ) - (2 * Real.pi * ξ : ℝ) * Complex.I) * t) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        exact laplaceFourierIntegrand_nonneg a ξ t ht.le
      _ = _ := by
        rw [integral_exp_mul_complex_Ioi (by simpa using (neg_lt_zero.mpr ha))]
        simp [div_eq_mul_inv]
  simp only [hleft, hright, sub_eq_add_neg]

end

theorem continuous_laplaceKernel (a : ℝ) : Continuous (laplaceKernel a) := by
  unfold laplaceKernel
  fun_prop

private theorem complex_resolvent_pair {a b : ℝ} (ha : 0 < a) :
    ((a : ℂ) - (b : ℂ) * Complex.I)⁻¹ - (-(a : ℂ) - (b : ℂ) * Complex.I)⁻¹ =
      ((2 * a / (a ^ 2 + b ^ 2) : ℝ) : ℂ) := by
  have hminus : (a : ℂ) - (b : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, Complex.zero_re] at hh
    exact ha.ne' hh
  have hplus : (a : ℂ) + (b : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      Complex.zero_re] at hh
    exact ha.ne' hh
  have hn : -(a : ℂ) - (b : ℂ) * Complex.I = -((a : ℂ) + (b : ℂ) * Complex.I) := by ring
  rw [hn, inv_neg, sub_neg_eq_add]
  push_cast
  have hp : ((a : ℂ) - (b : ℂ) * Complex.I) *
      ((a : ℂ) + (b : ℂ) * Complex.I) = (a : ℂ) ^ 2 + (b : ℂ) ^ 2 := by
    calc
      _ = (a : ℂ) ^ 2 - (b : ℂ) ^ 2 * Complex.I ^ 2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [← hp]
  field_simp [hminus, hplus]
  ring

/-- The scalar rational form of the Fourier transform. -/
theorem fourier_laplaceKernel {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    𝓕 (laplaceKernel a) ξ = ((2 * a / (a ^ 2 + (2 * Real.pi * ξ) ^ 2) : ℝ) : ℂ) := by
  rw [fourier_laplaceKernel_resolvents ha]
  exact complex_resolvent_pair ha

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CauchyFourier
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The scalar Cauchy transform by Fourier inversion -/

namespace KadisonKastler

open MeasureTheory ProbabilityTheory
open scoped FourierTransform

noncomputable section

/-- In mathlib's Fourier convention the transform of the two-sided
exponential is exactly the normalized Cauchy density. -/
theorem fourier_laplaceKernel_cauchy {γ : NNReal} (hγ : 0 < γ) (ξ : ℝ) :
    𝓕 (laplaceKernel (2 * Real.pi * γ)) ξ = (cauchyPDFReal 0 γ ξ : ℂ) := by
  have ha : 0 < 2 * Real.pi * (γ : ℝ) := by positivity
  rw [fourier_laplaceKernel ha]
  apply congrArg (fun x : ℝ => (x : ℂ))
  rw [cauchyPDFReal_def]
  simp only [sub_zero]
  have hg : (γ : ℝ) ≠ 0 := ne_of_gt (show (0 : ℝ) < γ from hγ)
  have hd : ξ ^ 2 + (γ : ℝ) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

/-- The inverse transform of the Cauchy density is the two-sided
exponential. All integrability hypotheses follow from proved library
results and the explicit transform above. -/
theorem fourierInv_cauchyPDFReal {γ : NNReal} (hγ : 0 < γ) (t : ℝ) :
    𝓕⁻ (fun x : ℝ => (cauchyPDFReal 0 γ x : ℂ)) t =
      laplaceKernel (2 * Real.pi * γ) t := by
  have ha : 0 < 2 * Real.pi * (γ : ℝ) := by positivity
  have hF : (𝓕 (laplaceKernel (2 * Real.pi * γ)) : ℝ → ℂ) =
      fun x => (cauchyPDFReal 0 γ x : ℂ) :=
    funext (fourier_laplaceKernel_cauchy hγ)
  have hi : Integrable (𝓕 (laplaceKernel (2 * Real.pi * γ))) := by
    rw [hF]
    exact (integrable_cauchyPDFReal 0).ofReal
  have h := (integrable_laplaceKernel ha).fourierInv_fourier_eq hi
    ((continuous_laplaceKernel (2 * Real.pi * γ)).continuousAt (x := t))
  simpa only [hF] using h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CauchyCharacter
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The characteristic function of the Cauchy density

The frequency is expressed in radians, matching the characters used by
the modular comparison. Fourier inversion accounts for the `2*pi` change
from mathlib's Fourier convention.
-/

namespace KadisonKastler

open MeasureTheory ProbabilityTheory
open scoped FourierTransform

noncomputable section

private theorem laplaceKernel_rescale (γ s : ℝ) :
    laplaceKernel (2 * Real.pi * γ) (s / (2 * Real.pi)) =
      (Real.exp (-γ * |s|) : ℂ) := by
  rw [laplaceKernel, Complex.ofReal_exp]
  have hp : 0 < 2 * Real.pi := by positivity
  rw [abs_div, abs_of_pos hp]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

/-- The centered Cauchy characteristic function in the radian convention. -/
theorem integral_cauchyPDFReal_character_zero {γ : NNReal} (hγ : 0 < γ) (s : ℝ) :
    (∫ x : ℝ, (cauchyPDFReal 0 γ x : ℂ) * (Circle.exp (s * x) : ℂ)) =
      (Real.exp (-(γ : ℝ) * |s|) : ℂ) := by
  have h := fourierInv_cauchyPDFReal hγ (s / (2 * Real.pi))
  have harg (x : ℝ) : 2 * Real.pi * (x * (s / (2 * Real.pi))) = s * x := by
    field_simp [Real.pi_ne_zero]
  have hi : (∫ x : ℝ, (Circle.exp (s * x) : ℂ) * (cauchyPDFReal 0 γ x : ℂ)) =
      laplaceKernel (2 * Real.pi * γ) (s / (2 * Real.pi)) := by
    simpa only [Real.fourierInv_eq, Real.inner_apply, Circle.smul_def,
      Real.fourierChar_apply', harg, smul_eq_mul] using h
  calc
    _ = ∫ x : ℝ, (Circle.exp (s * x) : ℂ) * (cauchyPDFReal 0 γ x : ℂ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => mul_comm _ _
    _ = _ := hi.trans (laplaceKernel_rescale γ s)

/-- Translation of the density gives the phase factor for an arbitrary
center. -/
theorem integral_cauchyPDFReal_character {γ : NNReal} (hγ : 0 < γ) (t s : ℝ) :
    (∫ x : ℝ, (cauchyPDFReal t γ x : ℂ) * (Circle.exp (s * x) : ℂ)) =
      (Real.exp (-(γ : ℝ) * |s|) : ℂ) * (Circle.exp (s * t) : ℂ) := by
  rw [← integral_add_right_eq_self
    (fun x : ℝ => (cauchyPDFReal t γ x : ℂ) * (Circle.exp (s * x) : ℂ)) t]
  have hpdf (x : ℝ) : cauchyPDFReal t γ (x + t) = cauchyPDFReal 0 γ x := by
    simp only [cauchyPDFReal_def, add_sub_cancel_right, sub_zero]
  simp_rw [hpdf, mul_add, Circle.exp_add, Circle.coe_mul, ← mul_assoc]
  rw [integral_mul_const, integral_cauchyPDFReal_character_zero hγ]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PoissonVectorAverage
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Vector integration for Poisson smoothing

The averages are taken on each Hilbert-space vector. No norm measurability
of an operator-valued field is required. The fixed standard Cauchy measure
allows dominated convergence at every point of strong continuity.
-/

namespace KadisonKastler

open MeasureTheory Filter Topology

noncomputable section

variable {S H : Type*} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem norm_probabilityOperatorIntegral_sub_le (μ : Measure S) [IsProbabilityMeasure μ]
    (F G : S → H →L[ℂ] H)
    (hmF : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    (hmG : ∀ x, AEStronglyMeasurable (fun s => G s x) μ)
    (C D : ℝ) (hF : ∀ᵐ s ∂μ, ‖F s‖ ≤ C) (hG : ∀ᵐ s ∂μ, ‖G s‖ ≤ D)
    {e : ℝ} (he : 0 ≤ e) (hFG : ∀ᵐ s ∂μ, ‖F s - G s‖ ≤ e) :
    ‖probabilityOperatorIntegral μ F hmF C hF -
      probabilityOperatorIntegral μ G hmG D hG‖ ≤ e := by
  apply ContinuousLinearMap.opNorm_le_bound _ he
  intro x
  change ‖(∫ s, F s x ∂μ) - ∫ s, G s x ∂μ‖ ≤ e * ‖x‖
  rw [← integral_sub (integrable_vectorField μ F hmF hF x)
    (integrable_vectorField μ G hmG hG x)]
  have h := norm_integral_le_of_norm_le_const (μ := μ) (C := e * ‖x‖)
    (by
      filter_upwards [hFG] with s hs
      exact ((F s - G s).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right hs (norm_nonneg x)))
  simpa only [sub_apply, probReal_univ, mul_one] using h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MeasurablePoisson
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
/-- Averaging preserves an essential uniform approximation bound. -/
theorem norm_measurablePoissonAverage_sub_le (F G : ℝ → H →L[ℂ] H)
    (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    (hG : ∀ x, AEStronglyMeasurable (fun s => G s x) volume)
    (C D : ℝ) (hC : ∀ᵐ s, ‖F s‖ ≤ C) (hD : ∀ᵐ s, ‖G s‖ ≤ D)
    {e : ℝ} (he : 0 ≤ e) (hFG : ∀ᵐ s, ‖F s - G s‖ ≤ e)
    (t r : ℝ) (hr : 0 < r) :
    ‖measurablePoissonAverage F hF C hC t r hr -
      measurablePoissonAverage G hG D hD t r hr‖ ≤ e :=
  norm_probabilityOperatorIntegral_sub_le _ _ _ _ _ C D _ _ he
    ((cauchyMeasure_absolutelyContinuous t hr).ae_le hFG)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PoissonCharacter
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Actual Poisson averages of scalar characters -/

namespace KadisonKastler

open MeasureTheory ProbabilityTheory

noncomputable section

theorem integral_realPoissonKernel_character (t s : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ x : ℝ, (realPoissonKernel t r x : ℂ) * (Circle.exp (s * x) : ℂ)) =
      (Real.exp (-r * |s|) : ℂ) * (Circle.exp (s * t) : ℂ) := by
  have hγ : (0 : NNReal) < NNReal.mk r hr.le := hr
  simpa only [← realPoissonKernel_eq_cauchyPDFReal t _ hr.le, NNReal.coe_mk] using
    integral_cauchyPDFReal_character hγ t s

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The explicit Cauchy character formula for the vector-defined Poisson
average, with the same field and integral used by analytic smoothing. -/
theorem measurablePoissonAverage_character (s t : ℝ) {r : ℝ} (hr : 0 < r) :
    measurablePoissonAverage (poissonCharacterField (H := H) s)
      (poissonCharacterField_measurable s) 1
      (Filter.Eventually.of_forall (norm_poissonCharacterField_le s)) t r hr =
      ((Real.exp (-r * |s|) : ℂ) * (Circle.exp (s * t) : ℂ)) •
        (1 : H →L[ℂ] H) := by
  apply ContinuousLinearMap.ext
  intro x
  rw [measurablePoissonAverage_apply]
  change (∫ u : ℝ, realPoissonKernel t r u • ((Circle.exp (s * u) : ℂ) • x)) = _
  have he (u : ℝ) : realPoissonKernel t r u • ((Circle.exp (s * u) : ℂ) • x) =
      ((realPoissonKernel t r u : ℂ) * (Circle.exp (s * u) : ℂ)) • x := by
    exact (smul_assoc (realPoissonKernel t r u) (Circle.exp (s * u) : ℂ) x).symm.trans
      (congrArg (fun z : ℂ => z • x)
        (RCLike.real_smul_eq_coe_mul (realPoissonKernel t r u) (Circle.exp (s * u) : ℂ)))
  simp_rw [he]
  rw [integral_smul_const, integral_realPoissonKernel_character t s hr]
  rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PoissonProductEstimates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Quantitative estimates for the two analytic smoothing fields

Boundary products of two approximate unitary fields have quadratic error.
Once the Hardy product identity identifies their positive-height product
with its Poisson integral, positivity of that integral retains the error.
The product identity is a hypothesis of these estimates.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

section Product

variable {A : Type*} [NormedRing A]

theorem norm_product_sub_product_of_contractions
    (a b u v : A) {δ : ℝ} (hδ : 0 ≤ δ)
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (ha : ‖a - u‖ ≤ δ) (hb : ‖b - v‖ ≤ δ) :
    ‖a * b - u * v‖ ≤ 2 * δ + δ ^ 2 := by
  have han : ‖a‖ ≤ 1 + δ := by
    have h := norm_sub_le_norm_sub_add_norm_sub a u (0 : A)
    simp only [sub_zero] at h
    linarith
  have he : a * b - u * v = a * (b - v) + (a - u) * v := by
    rw [mul_sub, sub_mul]
    abel
  rw [he]
  calc
    _ ≤ ‖a * (b - v)‖ + ‖(a - u) * v‖ := norm_add_le _ _
    _ ≤ (1 + δ) * δ + δ * 1 := add_le_add
      ((norm_mul_le _ _).trans (mul_le_mul han hb (norm_nonneg _) (by positivity)))
      ((norm_mul_le _ _).trans (mul_le_mul ha hv (norm_nonneg _) hδ))
    _ = _ := by ring

end Product

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Uniform contraction targets give an essential product error. -/
theorem ae_product_error
    (B S U V : ℝ → H →L[ℂ] H) {δ : ℝ} (hδ : 0 ≤ δ)
    (hU : ∀ᵐ s, ‖U s‖ ≤ 1) (hV : ∀ᵐ s, ‖V s‖ ≤ 1)
    (hB : ∀ᵐ s, ‖B s - U s‖ ≤ δ) (hS : ∀ᵐ s, ‖S s - V s‖ ≤ δ) :
    ∀ᵐ s, ‖B s * S s - U s * V s‖ ≤ 2 * δ + δ ^ 2 := by
  filter_upwards [hU, hV, hB, hS] with s hu hv hb hs
  exact norm_product_sub_product_of_contractions _ _ _ _ hδ hu hv hb hs

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DemodulatedCharacter
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Exact cancellation of the Poisson modulation

The modulation of a unitary field and its inverse has scalar frequency two.
The Cauchy character formula therefore cancels the two demodulating factors
exactly. This is proved for the actual vector-defined averages.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

theorem demodulation_scalar_cancel (t r : ℝ) :
    (((Real.exp r : ℂ) * star (Circle.exp t : ℂ)) ^ 2) *
      ((Real.exp (-2 * r) : ℂ) * (Circle.exp (2 * t) : ℂ)) = 1 := by
  have hc : star (Circle.exp t : ℂ) * (Circle.exp t : ℂ) = 1 := by
    rw [Complex.star_def, Complex.conj_mul']
    simp only [Circle.norm_coe, one_pow, Complex.ofReal_one]
  have he : (Real.exp r : ℂ) ^ 2 * (Real.exp (-2 * r) : ℂ) = 1 := by
    rw [pow_two, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
      ← Real.exp_add, ← Real.exp_add]
    rw [show r + r + -2 * r = 0 by ring, Real.exp_zero, Complex.ofReal_one]
  have hd : (Circle.exp (2 * t) : ℂ) = (Circle.exp t : ℂ) ^ 2 := by
    rw [two_mul, Circle.exp_add, Circle.coe_mul, pow_two]
  rw [hd]
  calc
    _ = ((Real.exp r : ℂ) ^ 2 * (Real.exp (-2 * r) : ℂ)) *
        (star (Circle.exp t : ℂ) * (Circle.exp t : ℂ)) ^ 2 := by ring
    _ = 1 := by rw [hc, he]; norm_num

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem measurablePoissonAverage_congr_ae
    (F G : ℝ → H →L[ℂ] H)
    (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    (hG : ∀ x, AEStronglyMeasurable (fun s => G s x) volume)
    (C D : ℝ) (hC : ∀ᵐ s, ‖F s‖ ≤ C) (hD : ∀ᵐ s, ‖G s‖ ≤ D)
    (hFG : ∀ᵐ s, F s = G s) (t r : ℝ) (hr : 0 < r) :
    measurablePoissonAverage F hF C hC t r hr =
      measurablePoissonAverage G hG D hD t r hr := by
  apply ContinuousLinearMap.ext
  intro x
  rw [measurablePoissonAverage_apply, measurablePoissonAverage_apply]
  apply integral_congr_ae
  filter_upwards [hFG] with s hs
  rw [hs]

/-- Cancellation for any bounded measurable field agreeing with the
frequency-two character almost everywhere. -/
theorem measurablePoissonAverage_phase_cancel
    (F : ℝ → H →L[ℂ] H)
    (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    (C : ℝ) (hC : ∀ᵐ s, ‖F s‖ ≤ C)
    (hFchar : ∀ᵐ s, F s = poissonCharacterField 2 s)
    (t r : ℝ) (hr : 0 < r) :
    (((Real.exp r : ℂ) * star (Circle.exp t : ℂ)) ^ 2) •
      measurablePoissonAverage F hF C hC t r hr = 1 := by
  rw [measurablePoissonAverage_congr_ae F (poissonCharacterField 2) hF
    (poissonCharacterField_measurable 2) C 1 hC
    (Filter.Eventually.of_forall (norm_poissonCharacterField_le 2)) hFchar t r hr,
    measurablePoissonAverage_character, smul_smul]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [show -r * 2 = -2 * r by ring, demodulation_scalar_cancel, one_smul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DirectIntegralConjugacy
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Assembling fiber conjugacies on the actual direct-integral space

`OperatorFieldDecomposition` records the decomposition and reconstruction
properties of a given constant-fiber direct integral. It is data, not a
published theorem or an existence assertion. The assembly argument below
uses actual multiplication unitaries on `L²(X,H)`.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem RepresentsOperatorField.unique {μ : Measure X} {F : X → H →L[ℂ] H}
    {T S : Lp H 2 μ →L[ℂ] Lp H 2 μ}
    (hT : RepresentsOperatorField μ F T) (hS : RepresentsOperatorField μ F S) : T = S := by
  apply ContinuousLinearMap.ext
  intro f
  exact Lp.ext ((hT f).trans (hS f).symm)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RealNestMultiplier
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Real character averaging of a bounded multiplier

The real group is made discrete only for its invariant mean. Its unitary
representation is the actual character multiplication on L²(real,H).
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem regularFieldOperator_commutes_character
    (F : ℝ → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun t => F t x) volume)
    (C : ℝ) (hC : ∀ᵐ t, ‖F t‖ ≤ C) (a : ℝ) :
    Commute (regularFieldOperator volume F hF C hC)
      (regularCharacterUnitary (H := H) a :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) := by
  change _ * _ = _ * _
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [regularFieldOperator_represents volume F hF C hC
      ((regularCharacterUnitary (H := H) a :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f),
    regularCharacterUnitary_apply_ae a f,
    regularCharacterUnitary_apply_ae a (regularFieldOperator volume F hF C hC f),
    regularFieldOperator_represents volume F hF C hC f] with t h₁ h₂ h₃ h₄
  change (regularFieldOperator volume F hF C hC
      ((regularCharacterUnitary (H := H) a :
        RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H) f)) t =
    ((regularCharacterUnitary (H := H) a :
      RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
        (regularFieldOperator volume F hF C hC f)) t
  rw [h₁, h₂, h₃, h₄, map_smul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PositiveFrequencyAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The concrete algebra of positive-frequency multipliers -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A nest-preserving represented field is an element of the concrete
positive-frequency multiplier algebra. -/
theorem regularFieldOperator_mem_positiveFrequencyAlgebra
    (F : ℝ → H →L[ℂ] H)
    (hF : ∀ x, MeasureTheory.AEStronglyMeasurable (fun t => F t x) MeasureTheory.volume)
    (C : ℝ) (hC : ∀ᵐ t ∂MeasureTheory.volume, ‖F t‖ ≤ C)
    (hpres : PreservesProjectionNest regularFrequencyNest
      (regularFieldOperator MeasureTheory.volume F hF C hC)) :
    regularFieldOperator MeasureTheory.volume F hF C hC ∈
      positiveFrequencyAlgebra (H := H) := by
  refine ⟨regularFieldOperator_commutes_character F hF C hC, ?_⟩
  have hp := hpres 0
  simp only [regularFrequencyNest, neg_zero] at hp
  rw [sub_mul, one_mul, sub_mul, sub_eq_zero] at hp
  exact hp.symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HardyPoissonProducts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Poisson products from the published Hardy evaluation

The boundary multiplication operators and their positive-frequency algebra
are concrete. Multiplicativity is obtained by applying the precisely cited
published evaluation homomorphism, including for constant middle factors.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem RepresentsOperatorField.mul
    {B S : ℝ → H →L[ℂ] H}
    {T V : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hB : RepresentsOperatorField volume B T) (hS : RepresentsOperatorField volume S V) :
    RepresentsOperatorField volume (fun t => B t * S t) (T * V) := by
  intro f
  filter_upwards [hB (V f), hS f] with t h₁ h₂
  change (T (V f)) t = B t (S t (f t))
  rw [h₁, h₂]

theorem RepresentsOperatorField.mem_positiveFrequencyAlgebra
    {B : ℝ → H →L[ℂ] H} {T : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H}
    (hB : ∀ x, AEStronglyMeasurable (fun t => B t x) volume)
    {C : ℝ} (hC : ∀ᵐ t, ‖B t‖ ≤ C)
    (hBT : RepresentsOperatorField volume B T)
    (hT : PreservesProjectionNest regularFrequencyNest T) :
    T ∈ positiveFrequencyAlgebra (H := H) := by
  have he := RepresentsOperatorField.unique hBT (regularFieldOperator_represents volume B hB C hC)
  rw [he] at hT ⊢
  exact regularFieldOperator_mem_positiveFrequencyAlgebra B hB C hC hT

variable [TopologicalSpace.SeparableSpace H]

/-- Exact multiplication of Poisson extensions of positive-frequency
preserving, bounded measurable multiplication operators. -/
theorem measurablePoissonAverage_mul_of_hardy
    (hHardy : PublishedHardyMultiplierEvaluation.{u})
    (B S : ℝ → H →L[ℂ] H)
    (hB : ∀ x, AEStronglyMeasurable (fun t => B t x) volume)
    (hS : ∀ x, AEStronglyMeasurable (fun t => S t x) volume)
    (CB CS : ℝ) (hb : ∀ᵐ t, ‖B t‖ ≤ CB) (hs : ∀ᵐ t, ‖S t‖ ≤ CS)
    (hBS : ∀ᵐ t, ‖B t * S t‖ ≤ CB * CS)
    (T V : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H)
    (hBT : RepresentsOperatorField volume B T) (hSV : RepresentsOperatorField volume S V)
    (hT : PreservesProjectionNest regularFrequencyNest T)
    (hV : PreservesProjectionNest regularFrequencyNest V)
    (t r : ℝ) (hr : 0 < r) :
    measurablePoissonAverage B hB CB hb t r hr *
        measurablePoissonAverage S hS CS hs t r hr =
      measurablePoissonAverage (fun s => B s * S s)
        (operator_product_vector_measurable B S hB hS) (CB * CS) hBS t r hr := by
  let A : positiveFrequencyAlgebra (H := H) :=
    ⟨T, hBT.mem_positiveFrequencyAlgebra hB hb hT⟩
  let D : positiveFrequencyAlgebra (H := H) :=
    ⟨V, hSV.mem_positiveFrequencyAlgebra hS hs hV⟩
  obtain ⟨ev, he⟩ := hHardy H t r hr
  rw [← he B hB CB hb A hBT hr, ← he S hS CS hs D hSV hr,
    ← he _ (operator_product_vector_measurable B S hB hS) _ hBS (A * D) (hBT.mul hSV) hr]
  exact (ev.map_mul A D).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DemodulatedInverseBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Approximate inverses after Poisson demodulation

The Hardy product identity follows from the published evaluation input
on the concrete positive-frequency algebra. The scalar Poisson character
formula is proved, and inverse estimates use the actual boundary product.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem norm_demodulatedPoisson_product_sub_one_le_of_product_identity
    (B S U V : ℝ → H →L[ℂ] H)
    (hB : ∀ x, AEStronglyMeasurable (fun s => B s x) volume)
    (hS : ∀ x, AEStronglyMeasurable (fun s => S s x) volume)
    (hU : ∀ x, AEStronglyMeasurable (fun s => U s x) volume)
    (hV : ∀ x, AEStronglyMeasurable (fun s => V s x) volume)
    {CB CS : ℝ}
    (hb : ∀ᵐ s, ‖B s‖ ≤ CB) (hs : ∀ᵐ s, ‖S s‖ ≤ CS)
    (hBS : ∀ᵐ s, ‖B s * S s‖ ≤ CB * CS)
    (hUV : ∀ᵐ s, ‖U s * V s‖ ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hu : ∀ᵐ s, ‖U s‖ ≤ 1) (hv : ∀ᵐ s, ‖V s‖ ≤ 1)
    (hBU : ∀ᵐ s, ‖B s - U s‖ ≤ δ) (hSV : ∀ᵐ s, ‖S s - V s‖ ≤ δ)
    (t r : ℝ) (hr : 0 < r)
    (hproduct : measurablePoissonAverage B hB CB hb t r hr *
        measurablePoissonAverage S hS CS hs t r hr =
      measurablePoissonAverage (fun s => B s * S s)
        (operator_product_vector_measurable B S hB hS) (CB * CS) hBS t r hr)
    (hboundary : ∀ᵐ s, U s * V s = poissonCharacterField 2 s) :
    ‖demodulatedPoissonAverage B hB CB hb t r hr *
        demodulatedPoissonAverage S hS CS hs t r hr - 1‖ ≤
      Real.exp (2 * r) * (2 * δ + δ ^ 2) := by
  have hphase := measurablePoissonAverage_phase_cancel (fun s => U s * V s)
    (operator_product_vector_measurable U V hU hV) 1 hUV hboundary t r hr
  let z : ℂ := (Real.exp r : ℂ) * star (Circle.exp t : ℂ)
  have hz : ‖z‖ = Real.exp r := by
    change ‖(Real.exp r : ℂ) * star (Circle.exp t : ℂ)‖ = Real.exp r
    rw [norm_mul, norm_star, Circle.norm_coe, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos r)]
  have herror := norm_measurablePoissonAverage_sub_le
    (fun s => B s * S s) (fun s => U s * V s)
    (operator_product_vector_measurable B S hB hS)
    (operator_product_vector_measurable U V hU hV)
    (CB * CS) 1 hBS hUV (by positivity)
    (ae_product_error B S U V hδ hu hv hBU hSV) t r hr
  have hid : demodulatedPoissonAverage B hB CB hb t r hr *
        demodulatedPoissonAverage S hS CS hs t r hr - 1 =
      z ^ 2 • (measurablePoissonAverage (fun s => B s * S s)
          (operator_product_vector_measurable B S hB hS) (CB * CS) hBS t r hr -
        measurablePoissonAverage (fun s => U s * V s)
          (operator_product_vector_measurable U V hU hV) 1 hUV t r hr) := by
    rw [smul_sub, hphase]
    unfold demodulatedPoissonAverage
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, hproduct]
    simp only [z, pow_two]
  rw [hid, norm_smul, norm_pow, hz]
  have he : (Real.exp r) ^ 2 = Real.exp (2 * r) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_left herror (Real.exp_pos _).le


theorem norm_demodulatedPoisson_product_sub_one_le
    [TopologicalSpace.SeparableSpace H]
    (hHardy : PublishedHardyMultiplierEvaluation.{u})
    (B S U V : ℝ → H →L[ℂ] H)
    (hB : ∀ x, AEStronglyMeasurable (fun s => B s x) volume)
    (hS : ∀ x, AEStronglyMeasurable (fun s => S s x) volume)
    (hU : ∀ x, AEStronglyMeasurable (fun s => U s x) volume)
    (hV : ∀ x, AEStronglyMeasurable (fun s => V s x) volume)
    {CB CS : ℝ}
    (hb : ∀ᵐ s, ‖B s‖ ≤ CB) (hs : ∀ᵐ s, ‖S s‖ ≤ CS)
    (hBS : ∀ᵐ s, ‖B s * S s‖ ≤ CB * CS)
    (hUV : ∀ᵐ s, ‖U s * V s‖ ≤ 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hu : ∀ᵐ s, ‖U s‖ ≤ 1) (hv : ∀ᵐ s, ‖V s‖ ≤ 1)
    (hBU : ∀ᵐ s, ‖B s - U s‖ ≤ δ) (hSV : ∀ᵐ s, ‖S s - V s‖ ≤ δ)
    (t r : ℝ) (hr : 0 < r)
    (hBpres : PreservesProjectionNest (regularFrequencyNest (H := H))
      (regularFieldOperator volume B hB CB hb))
    (hSpres : PreservesProjectionNest (regularFrequencyNest (H := H))
      (regularFieldOperator volume S hS CS hs))
    (hboundary : ∀ᵐ s, U s * V s = poissonCharacterField 2 s) :
    ‖demodulatedPoissonAverage B hB CB hb t r hr *
        demodulatedPoissonAverage S hS CS hs t r hr - 1‖ ≤
      Real.exp (2 * r) * (2 * δ + δ ^ 2) := by
  let TB : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
    regularFieldOperator volume B hB CB hb
  let TS : RegularCoreHilbert H →L[ℂ] RegularCoreHilbert H :=
    regularFieldOperator volume S hS CS hs
  have hBT : RepresentsOperatorField volume B TB := regularFieldOperator_represents volume B hB CB hb
  have hST : RepresentsOperatorField volume S TS := regularFieldOperator_represents volume S hS CS hs
  have hproduct := measurablePoissonAverage_mul_of_hardy hHardy B S hB hS CB CS hb hs hBS
    TB TS hBT hST hBpres hSpres t r hr
  exact norm_demodulatedPoisson_product_sub_one_le_of_product_identity
    B S U V hB hS hU hV hb hs hBS hUV hδ hu hv hBU hSV t r hr hproduct hboundary
/-- A small boundary error and a no-larger positive height give a linear
inverse error with an absolute constant. -/
theorem exp_two_mul_product_error_le {r δ : ℝ}
    (hr : 0 ≤ r) (hrδ : r ≤ δ) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 8) :
    Real.exp (2 * r) * (2 * δ + δ ^ 2) ≤ 6 * δ := by
  have hrsmall : |2 * r| ≤ 1 := by rw [abs_of_nonneg (by positivity)]; linarith
  have he := Real.abs_exp_sub_one_le (x := 2 * r) hrsmall
  have he' : Real.exp (2 * r) ≤ 2 := by
    rw [abs_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hr)] at he
    linarith [le_abs_self (Real.exp (2 * r) - 1)]
  calc
    Real.exp (2 * r) * (2 * δ + δ ^ 2) ≤ 2 * (2 * δ + δ ^ 2) :=
      mul_le_mul_of_nonneg_right he' (by positivity)
    _ ≤ 6 * δ := by nlinarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FrequencySmoothing
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

local instance frequencySmoothingOrder_r315035_1 (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance frequencySmoothingStarOrder_r315035_1 (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
variable {F G : ℝ → H →L[ℂ] H} {δ : ℝ}

theorem norm_product_sub_one_le_oai [TopologicalSpace.SeparableSpace H]
    (hHardy : PublishedHardyMultiplierEvaluation.{u})
    (A : FrequencySmoothing F δ) (B : FrequencySmoothing G δ)
    (hF : ∀ x, AEStronglyMeasurable (fun t => F t x) volume)
    (hG : ∀ x, AEStronglyMeasurable (fun t => G t x) volume)
    (hFn : ∀ᵐ t, ‖F t‖ ≤ 1) (hGn : ∀ᵐ t, ‖G t‖ ≤ 1)
    (hFG : ∀ᵐ t, F t * G t = poissonCharacterField 2 t)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 16)
    (t r : ℝ) (hr : 0 < r) (hrδ : r ≤ δ) :
    ‖A.smooth t r hr * B.smooth t r hr - 1‖ ≤ 12 * δ := by
  have hab : ∀ᵐ s, ‖A.boundary s * B.boundary s‖ ≤ (1 + 2 * δ) * (1 + 2 * δ) := by
    filter_upwards [A.bounded, B.bounded] with s ha hb
    exact (norm_mul_le _ _).trans (mul_le_mul ha hb (norm_nonneg _) (by positivity))
  have hfg : ∀ᵐ s, ‖F s * G s‖ ≤ 1 := by
    filter_upwards [hFn, hGn] with s hf hg
    exact (norm_mul_le _ _).trans ((mul_le_mul hf hg (norm_nonneg _) zero_le_one).trans_eq
      (one_mul 1))
  have hi := norm_demodulatedPoisson_product_sub_one_le hHardy A.boundary B.boundary F G
    A.measurable B.measurable hF hG A.bounded B.bounded hab hfg
    (show 0 ≤ 2 * δ by positivity) hFn hGn A.close B.close t r hr A.preserves B.preserves hFG
  exact hi.trans ((exp_two_mul_product_error_le hr.le (by linarith)
    (by positivity) (by linarith : 2 * δ ≤ 1 / 8)).trans_eq (by ring))

end FrequencySmoothing

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.FrequencySmoothing.norm_product_sub_one_le_oai.{u} := @OAI.KadisonKastler.FrequencySmoothing.norm_product_sub_one_le_oai.{u}
