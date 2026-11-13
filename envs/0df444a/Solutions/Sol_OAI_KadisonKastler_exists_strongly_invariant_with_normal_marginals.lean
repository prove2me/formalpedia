-- Prove2me | solution 1 for OAI.KadisonKastler.exists_strongly_invariant_with_normal_marginals
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:36:12.635496+00:00
-- url     : https://prove2.me/submissions/6d2df403-5d8e-4a09-acd1-21487ff8d35a

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
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Projection
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Fourier.AddCircle
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
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
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
import Mathlib.LinearAlgebra.Complex.Module
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
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Prod
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
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K025
import Theorems.Thm_OAI_KadisonKastler_normal_marginal_product_agreement

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProbabilityOperatorAlgebra
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Algebra membership of vectorwise probability averages -/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {S H : Type*} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Every fixed commutation relation passes to the actual vector integral. -/
theorem probabilityOperatorIntegral_commutes (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H) (hm : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    (C : ℝ) (hb : ∀ᵐ s ∂μ, ‖F s‖ ≤ C) (T : H →L[ℂ] H)
    (hT : ∀ᵐ s ∂μ, F s * T = T * F s) :
    probabilityOperatorIntegral μ F hm C hb * T =
      T * probabilityOperatorIntegral μ F hm C hb := by
  ext x
  change (∫ s, F s (T x) ∂μ) = T (∫ s, F s x ∂μ)
  rw [← T.integral_comp_comm (integrable_bounded_operator_vector μ F hm hb x)]
  apply integral_congr_ae
  filter_upwards [hT] with s hs
  exact congrArg (fun A : H →L[ℂ] H => A x) hs

/-- Von Neumann algebra membership is retained without any norm
measurability hypothesis on the field. -/
theorem probabilityOperatorIntegral_mem (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H) (hm : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    (C : ℝ) (hb : ∀ᵐ s ∂μ, ‖F s‖ ≤ C) (M : VonNeumannAlgebra H)
    (hM : ∀ᵐ s ∂μ, F s ∈ M) : probabilityOperatorIntegral μ F hm C hb ∈ M := by
  change probabilityOperatorIntegral μ F hm C hb ∈ (M : Set (H →L[ℂ] H))
  rw [← M.centralizer_centralizer]
  intro T hT
  apply (probabilityOperatorIntegral_commutes μ F hm C hb T ?_).symm
  filter_upwards [hM] with s hs
  exact hT (F s) hs

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GaussianStateCovariance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PoissonKernelFormula
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The actual half-plane Poisson kernel

The fixed-law vector averages agree with integration against
`r / (π ((t-s)²+r²))` for every positive height.
-/

namespace KadisonKastler

open MeasureTheory ProbabilityTheory

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem integral_standardCauchy (f : ℝ → E) :
    (∫ s, f s ∂cauchyMeasure 0 1) =
      ∫ s, realPoissonKernel 0 1 s • f s := by
  rw [cauchyMeasure_of_scale_ne_zero 0 (by norm_num),
    integral_withDensity_eq_integral_toReal_smul (measurable_cauchyPDF 0 1)
      (ae_of_all _ fun s => ENNReal.ofReal_lt_top)]
  congr 1
  funext s
  congr 1
  rw [cauchyPDF, ENNReal.toReal_ofReal (cauchyPDF_pos 0 (by norm_num) s).le]
  simp only [cauchyPDFReal, NNReal.coe_one, sub_zero, mul_one, one_pow,
    realPoissonKernel, zero_sub, neg_sq, one_div, mul_inv_rev]
  ring

private theorem realPoissonKernel_affine {r : ℝ} (hr : 0 < r) (t s : ℝ) :
    r * realPoissonKernel t r (t + r * s) = realPoissonKernel 0 1 s := by
  have h₁ : (t - (t + r * s)) ^ 2 + r ^ 2 ≠ 0 := by positivity
  have h₂ : (0 - s) ^ 2 + (1 : ℝ) ^ 2 ≠ 0 := by positivity
  unfold realPoissonKernel
  field_simp [Real.pi_ne_zero, h₁, h₂]
  ring

omit [CompleteSpace E] in
theorem integral_standardCauchy_affine (f : ℝ → E) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫ s, f (t + r * s) ∂cauchyMeasure 0 1) =
      ∫ s, realPoissonKernel t r s • f s := by
  rw [integral_standardCauchy]
  let g : ℝ → E := fun s => realPoissonKernel t r s • f s
  have he (s : ℝ) : realPoissonKernel 0 1 s • f (t + r * s) =
      r • g (t + r * s) := by
    dsimp only [g]
    rw [smul_smul, realPoissonKernel_affine hr]
  simp_rw [he]
  rw [integral_smul, Measure.integral_comp_mul_left (fun s => g (t + s)) r,
    integral_add_left_eq_self, smul_smul, abs_of_pos (inv_pos.mpr hr),
    mul_inv_cancel₀ hr.ne', one_smul]

theorem poissonVectorAverage_apply_eq_integral {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (F : ℝ → H →L[ℂ] H) (hF : ∀ x, Continuous (fun s => F s x))
    (C : ℝ) (hC : ∀ s, ‖F s‖ ≤ C) (t : ℝ) {r : ℝ} (hr : 0 < r) (x : H) :
    poissonVectorAverage F hF C hC t r x =
      ∫ s, realPoissonKernel t r s • F s x :=
  integral_standardCauchy_affine (fun s => F s x) t hr

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PoissonKernelContinuity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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
-- module Solutions.OAIQ075_KS.KadisonKastler_PoissonNormContinuity
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Norm continuity of vectorwise Poisson averages

Although the boundary field is only strongly continuous, translating the
integrable scalar kernel gives norm continuity of each positive-height
operator average.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem continuous_realPoissonKernel (t : ℝ) {r : ℝ} (hr : 0 < r) :
    Continuous (realPoissonKernel t r) := by
  unfold realPoissonKernel
  apply continuous_const.div
    (continuous_const.mul (((continuous_const.sub continuous_id).pow 2).add continuous_const))
  intro s
  exact ne_of_gt (mul_pos Real.pi_pos
    (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hr)))

omit [CompleteSpace H] in
private theorem integrable_poisson_vector
    (F : ℝ → H →L[ℂ] H) (hF : ∀ x, Continuous (fun s => F s x))
    {C : ℝ} (hC : ∀ s, ‖F s‖ ≤ C) (t : ℝ) {r : ℝ} (hr : 0 < r) (x : H) :
    Integrable (fun s => realPoissonKernel t r s • F s x) := by
  apply ((integrable_realPoissonKernel t hr).mul_const (C * ‖x‖)).mono'
    (((continuous_realPoissonKernel t hr).smul (hF x)).aestronglyMeasurable)
  filter_upwards [] with s
  change ‖realPoissonKernel t r s • F s x‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (realPoissonKernel_nonneg t s hr)]
  exact mul_le_mul_of_nonneg_left
    (((F s).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hC s) (norm_nonneg x)))
    (realPoissonKernel_nonneg t s hr)

/-- A quantitative translation bound independent of the boundary field's
modulus of strong continuity. -/
theorem norm_poissonVectorAverage_sub_le
    (F : ℝ → H →L[ℂ] H) (hF : ∀ x, Continuous (fun s => F s x))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ s, ‖F s‖ ≤ C)
    (t u : ℝ) {r : ℝ} (hr : 0 < r) :
    ‖poissonVectorAverage F hF C hC t r - poissonVectorAverage F hF C hC u r‖ ≤
      (2 * C / r) * |t - u| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  change ‖poissonVectorAverage F hF C hC t r x -
    poissonVectorAverage F hF C hC u r x‖ ≤ _
  rw [poissonVectorAverage_apply_eq_integral F hF C hC t hr x,
    poissonVectorAverage_apply_eq_integral F hF C hC u hr x,
    ← integral_sub (integrable_poisson_vector F hF hC t hr x)
      (integrable_poisson_vector F hF hC u hr x)]
  have hi := ((integrable_realPoissonKernel t hr).add
    (integrable_realPoissonKernel u hr)).const_mul (|t - u| / r)
  have hbound : ‖∫ s, realPoissonKernel t r s • F s x -
      realPoissonKernel u r s • F s x‖ ≤
      ∫ s, ((|t - u| / r) * (realPoissonKernel t r s + realPoissonKernel u r s)) *
        (C * ‖x‖) := by
    apply norm_integral_le_of_norm_le (hi.mul_const (C * ‖x‖))
    filter_upwards [] with s
    rw [← sub_smul, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (abs_realPoissonKernel_sub_le t u s hr)
      (((F s).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (hC s) (norm_nonneg x)))
      (norm_nonneg _) (mul_nonneg (div_nonneg (abs_nonneg _) hr.le)
        (add_nonneg (realPoissonKernel_nonneg t s hr) (realPoissonKernel_nonneg u s hr)))
  calc
    _ ≤ _ := hbound
    _ = (2 * C / r) * |t - u| * ‖x‖ := by
      rw [integral_mul_const, integral_const_mul,
        integral_add (integrable_realPoissonKernel t hr) (integrable_realPoissonKernel u hr),
        integral_realPoissonKernel t hr, integral_realPoissonKernel u hr]
      ring

/-- Positive-height Poisson smoothing is continuous in operator norm. -/
theorem continuous_poissonVectorAverage
    (F : ℝ → H →L[ℂ] H) (hF : ∀ x, Continuous (fun s => F s x))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ s, ‖F s‖ ≤ C)
    {r : ℝ} (hr : 0 < r) :
    Continuous (fun t => poissonVectorAverage F hF C hC t r) := by
  have h : LipschitzWith ⟨2 * C / r, by positivity⟩
      (fun t => poissonVectorAverage F hF C hC t r) := by
    apply LipschitzWith.of_dist_le_mul
    intro t u
    rw [dist_eq_norm, Real.dist_eq]
    exact norm_poissonVectorAverage_sub_le F hF hC0 hC t u hr
  exact h.continuous

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StateActionAverages
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Probability averages of the implemented modular action

These maps are defined by vector integration. They are contractions and
preserve the reference vector state whenever the implementing group fixes
the reference vector.
-/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem stateActionAverage_mem (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (M : VonNeumannAlgebra H)
    (hnormal : ∀ t a, a ∈ M → stateActionOrbit U a t ∈ M)
    (a : H →L[ℂ] H) (ha : a ∈ M) : stateActionAverage U hU μ a ∈ M :=
  probabilityOperatorIntegral_mem μ (stateActionOrbit U a)
    (fun x => (stateActionOrbit_continuous U hU a x).aestronglyMeasurable)
    ‖a‖ (Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le) M
    (Eventually.of_forall fun t => hnormal t a ha)

theorem stateActionAverage_vectorState (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (Ω : H) (hΩ : ∀ t : ℝ, (U (Multiplicative.ofAdd t) : H →L[ℂ] H) Ω=Ω)
    (a : H →L[ℂ] H) :
    productVectorState Ω (stateActionAverage U hU μ a)=productVectorState Ω a := by
  have hi := integrable_bounded_operator_vector μ (stateActionOrbit U a)
    (fun x => (stateActionOrbit_continuous U hU a x).aestronglyMeasurable)
    (Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le) Ω
  change (innerSL ℂ Ω) (∫ t, stateActionOrbit U a t Ω ∂μ)=productVectorState Ω a
  rw [← (innerSL ℂ Ω).integral_comp_comm hi]
  have he (t : ℝ) : (innerSL ℂ Ω) (stateActionOrbit U a t Ω)=productVectorState Ω a :=
    productVectorState_unitaryConj_of_fixes Ω (U (Multiplicative.ofAdd t)) (hΩ t) a
  simp only [he,integral_const,probReal_univ,one_smul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StateActionFubini
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Commutation of probability averages of an abelian action -/

namespace KadisonKastler

open MeasureTheory Filter

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem stateActionOrbit_average_apply (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : H →L[ℂ] H) (s : ℝ) (x : H) :
    stateActionOrbit U (stateActionAverage U hU μ a) s x =
      ∫ t, stateActionOrbit U a (s+t) x ∂μ := by
  let u := U (Multiplicative.ofAdd s)
  have hi := integrable_bounded_operator_vector μ (stateActionOrbit U a)
    (fun y => (stateActionOrbit_continuous U hU a y).aestronglyMeasurable)
    (Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le)
    (star (u : H →L[ℂ] H) x)
  change (u : H →L[ℂ] H) (∫ t, stateActionOrbit U a t (star (u : H →L[ℂ] H) x) ∂μ)=_
  rw [← (u : H →L[ℂ] H).integral_comp_comm hi]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro t
  change (u : H →L[ℂ] H) (stateActionOrbit U a t (star (u : H →L[ℂ] H) x)) =
    stateActionOrbit U a (s+t) x
  rw [stateActionOrbit_add]
  rfl

theorem stateActionAverage_commute (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (a : H →L[ℂ] H) :
    stateActionAverage U hU μ (stateActionAverage U hU ν a) =
      stateActionAverage U hU ν (stateActionAverage U hU μ a) := by
  ext x
  change (∫ s, stateActionOrbit U (stateActionAverage U hU ν a) s x ∂μ)=
    ∫ t, stateActionOrbit U (stateActionAverage U hU μ a) t x ∂ν
  simp_rw [stateActionOrbit_average_apply]
  have hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => stateActionOrbit U a (p.1+p.2) x) (μ.prod ν) :=
    ((stateActionOrbit_continuous U hU a x).comp
      (continuous_fst.add continuous_snd)).aestronglyMeasurable
  have hi : Integrable (fun p : ℝ × ℝ => stateActionOrbit U a (p.1+p.2) x)
      (μ.prod ν) := by
    apply (integrable_const (‖a‖*‖x‖)).mono' hm
    apply Eventually.of_forall
    intro p
    exact ((stateActionOrbit U a (p.1+p.2)).le_opNorm x).trans_eq
      (by rw [stateActionOrbit_norm])
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro t
  apply integral_congr_ae
  apply Eventually.of_forall
  intro s
  change stateActionOrbit U a (s+t) x=stateActionOrbit U a (t+s) x
  rw [add_comm s t]

theorem invariant_functional_actionAverage
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ)
    (hφ : ∀ t a, φ (stateActionOrbit U a t)=φ a)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : H →L[ℂ] H) (ha : Continuous (stateActionOrbit U a)) :
    φ (stateActionAverage U hU μ a)=φ a := by
  have hi : Integrable (stateActionOrbit U a) μ := by
    apply (integrable_const ‖a‖).mono' ha.aestronglyMeasurable
    exact Eventually.of_forall fun t => (stateActionOrbit_norm U a t).le
  have he : stateActionAverage U hU μ a=∫ t, stateActionOrbit U a t ∂μ := by
    ext x
    exact (ContinuousLinearMap.apply ℂ H x).integral_comp_comm hi
  rw [he,← φ.integral_comp_comm hi]
  simp_rw [hφ]
  simp only [integral_const,probReal_univ,one_smul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StateActionStates
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # States composed with probability averages

Positivity is proved on vectors, so the initial state need not be normal.
-/

namespace KadisonKastler

open MeasureTheory Filter NaimarkZFC
open scoped ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem probabilityOperatorIntegral_positive
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H)
    (hm : ∀ x, AEStronglyMeasurable (fun t => F t x) μ)
    (C : ℝ) (hb : ∀ᵐ t ∂μ, ‖F t‖ ≤ C)
    (hp : ∀ᵐ t ∂μ, (F t).IsPositive) :
    (probabilityOperatorIntegral μ F hm C hb).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
  intro x
  have hi := integrable_bounded_operator_vector μ F hm hb x
  have he : inner ℂ x (probabilityOperatorIntegral μ F hm C hb x) =
      ∫ t, inner ℂ x (F t x) ∂μ := by
    exact ((innerSL ℂ x).integral_comp_comm hi).symm
  have hr : 0 ≤ inner ℂ x (probabilityOperatorIntegral μ F hm C hb x) := by
    rw [he]
    exact integral_nonneg_of_ae (hp.mono fun t ht => ht.inner_nonneg_right x)
  have hl : 0 ≤ inner ℂ (probabilityOperatorIntegral μ F hm C hb x) x := by
    rw [← inner_conj_symm]
    exact star_nonneg_iff.mpr hr
  exact ⟨Complex.ext rfl hl.2,hl.1⟩

variable (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem stateActionAverage_square_positive (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : H →L[ℂ] H) : (stateActionAverage U hU μ (star a*a)).IsPositive := by
  apply probabilityOperatorIntegral_positive
  apply Eventually.of_forall
  intro t
  let e : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H) :=
    Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (U (Multiplicative.ofAdd t))
  have he : e (star a*a)=star (e a)*e a := by
    calc
      _ = e (star a)*e a := e.map_mul _ _
      _ = _ := congrArg (fun b : H →L[ℂ] H => b*e a) (map_star e a)
  change (e (star a*a)).IsPositive
  rw [he]
  exact (ContinuousLinearMap.nonneg_iff_isPositive _).mp (star_mul_self_nonneg (e a))

theorem state_comp_actionAverage (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (hφ : IsState φ) :
    IsState (φ.comp (stateActionAverageMap U hU μ)) := by
  apply (isState_iff _).mpr
  constructor
  · change φ (stateActionAverage U hU μ 1)=1
    rw [stateActionAverage_one]
    exact ((isState_iff φ).mp hφ).1
  · intro a
    have hp := (positiveOfSquares φ hφ.2).map_nonneg
      ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr
        (stateActionAverage_square_positive U hU μ a))
    exact ⟨hp.2.symm,hp.1⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StrongInvariantState
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instIsProbabilityMeasureBilateralWalkPathBilateralWalkLaw _root_.OAI.KadisonKastler.instIsProbabilityMeasureRandomWalkBoundaryRandomWalkBoundaryMeasure _root_.OAI.KadisonKastler.randomWalkPathLaw_probability _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Strongly invariant states by Poisson smoothing

This proves the smoothing step of Marrakchi, arXiv:1811.10253v2,
Proposition 3.10. Preservation of a prescribed nonnormal restriction is
only asserted here on operators whose orbits are norm continuous.
-/

namespace KadisonKastler

open MeasureTheory NaimarkZFC

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem poissonActionAverage_orbit_continuous (a : H →L[ℂ] H) :
    Continuous (stateActionOrbit U
      (stateActionAverage U hU (ProbabilityTheory.cauchyMeasure 0 1) a)) := by
  have he (s : ℝ) :
      stateActionOrbit U (stateActionAverage U hU (ProbabilityTheory.cauchyMeasure 0 1) a) s =
        poissonVectorAverage (stateActionOrbit U a)
          (stateActionOrbit_continuous U hU a) ‖a‖
          (fun t => (stateActionOrbit_norm U a t).le) s 1 := by
    ext x
    rw [stateActionOrbit_average_apply]
    change (∫ t, stateActionOrbit U a (s+t) x ∂ProbabilityTheory.cauchyMeasure 0 1)=
      ∫ t, stateActionOrbit U a (s+1*t) x ∂ProbabilityTheory.cauchyMeasure 0 1
    simp only [one_mul]
  change Continuous (fun s : ℝ =>
    stateActionOrbit U (stateActionAverage U hU (ProbabilityTheory.cauchyMeasure 0 1) a) s)
  simp_rw [he]
  exact continuous_poissonVectorAverage (stateActionOrbit U a)
    (stateActionOrbit_continuous U hU a) (norm_nonneg a)
    (fun t => (stateActionOrbit_norm U a t).le) (by norm_num)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StrongProductStateExtension
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instIsProbabilityMeasureBilateralWalkPathBilateralWalkLaw _root_.OAI.KadisonKastler.instIsProbabilityMeasureRandomWalkBoundaryRandomWalkBoundaryMeasure _root_.OAI.KadisonKastler.randomWalkPathLaw_probability _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Strongly invariant extensions with normal marginals

This is the normal-marginal specialization of Marrakchi,
arXiv:1811.10253v2, Lemma 4.1 and Proposition 3.10. The initial product
state is an explicit hypothesis; its construction is a separate step.
-/

namespace KadisonKastler

open MeasureTheory NaimarkZFC

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem exists_strongly_invariant_with_normal_marginals_oai
    (M N : VonNeumannAlgebra H)
    (hM : ∀ t a, a ∈ M → stateActionOrbit U a t ∈ M)
    (hN : ∀ t a, a ∈ N → stateActionOrbit U a t ∈ N)
    (Ω : H) (hfix : ∀ t : ℝ, (U (Multiplicative.ofAdd t) : H →L[ℂ] H) Ω=Ω)
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (hφ : IsState φ)
    (hinv : ∀ t a, φ (stateActionOrbit U a t)=φ a)
    (hφM : ∀ a ∈ M, φ a=productVectorState Ω a)
    (hφN : ∀ a ∈ N, φ a=productVectorState Ω a) :
    ∃ ψ : (H →L[ℂ] H) →L[ℂ] ℂ, IsState ψ ∧
      (∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (a : H →L[ℂ] H),
        ψ (stateActionAverage U hU μ a)=ψ a) ∧
      ∀ a ∈ M, ∀ b ∈ N, ψ (a*b)=φ (a*b) := by
  let ν := ProbabilityTheory.cauchyMeasure 0 1
  let ψ := φ.comp (stateActionAverageMap U hU ν)
  have hψ : IsState ψ := state_comp_actionAverage U hU ν φ hφ
  have heq (a : H →L[ℂ] H) (ha : Continuous (stateActionOrbit U a)) : ψ a=φ a :=
    invariant_functional_actionAverage U hU φ hinv ν a ha
  have hψM (a : H →L[ℂ] H) (ha : a ∈ M) : ψ a=productVectorState Ω a := by
    change φ (stateActionAverage U hU ν a)=_
    rw [hφM _ (stateActionAverage_mem U hU ν M hM a ha)]
    exact stateActionAverage_vectorState U hU ν Ω hfix a
  have hψN (a : H →L[ℂ] H) (ha : a ∈ N) : ψ a=productVectorState Ω a := by
    change φ (stateActionAverage U hU ν a)=_
    rw [hφN _ (stateActionAverage_mem U hU ν N hN a ha)]
    exact stateActionAverage_vectorState U hU ν Ω hfix a
  refine ⟨ψ,hψ,?_,?_⟩
  · intro μ hμ a
    change φ (stateActionAverage U hU ν (stateActionAverage U hU μ a))=
      φ (stateActionAverage U hU ν a)
    rw [stateActionAverage_commute U hU ν μ a]
    exact invariant_functional_actionAverage U hU φ hinv μ _
      (poissonActionAverage_orbit_continuous U hU a)
  · intro a ha b hb
    exact (normal_marginal_product_agreement U hU M N hM hN Ω φ ψ hφ hψ
      hφM hψM hφN hψN (fun c hc => (heq c hc).symm) a b ha hb).symm

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.exists_strongly_invariant_with_normal_marginals_oai.{u_1} := @OAI.KadisonKastler.exists_strongly_invariant_with_normal_marginals_oai.{u_1}
