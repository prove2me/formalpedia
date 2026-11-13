-- Prove2me | solution 1 for OAI.KadisonKastler.normal_marginal_product_agreement
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:20:01.209173+00:00
-- url     : https://prove2.me/submissions/4f42cbe3-f6ab-4cc9-9d03-a1c5da737267

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
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

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PoissonVectorAverage
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instIsProbabilityMeasureBilateralWalkPathBilateralWalkLaw _root_.OAI.KadisonKastler.instIsProbabilityMeasureRandomWalkBoundaryRandomWalkBoundaryMeasure _root_.OAI.KadisonKastler.randomWalkPathLaw_probability _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem probabilityOperatorIntegral_star (μ : Measure S) [IsProbabilityMeasure μ]
    (F : S → H →L[ℂ] H) (hm : ∀ x, AEStronglyMeasurable (fun s => F s x) μ)
    (hmstar : ∀ x, AEStronglyMeasurable (fun s => star (F s) x) μ)
    (C : ℝ) (hb : ∀ᵐ s ∂μ, ‖F s‖ ≤ C) :
    probabilityOperatorIntegral μ (fun s => star (F s)) hmstar C
        (hb.mono fun s hs => (norm_star (F s)).le.trans hs) =
      star (probabilityOperatorIntegral μ F hm C hb) := by
  ext x
  apply ext_inner_left ℂ
  intro y
  rw [probabilityOperatorIntegral_apply, ← integral_inner
    (integrable_vectorField μ (fun s => star (F s)) hmstar
      (hb.mono fun s hs => (norm_star (F s)).le.trans hs) x)]
  simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  rw [probabilityOperatorIntegral_apply]
  calc
    (∫ s, inner ℂ (F s y) x ∂μ) =
        ∫ s, star (inner ℂ x (F s y)) ∂μ := by
      congr 1
      funext s
      exact (inner_conj_symm _ _).symm
    _ = star (∫ s, inner ℂ x (F s y) ∂μ) := integral_conj
    _ = star (inner ℂ x (∫ s, F s y ∂μ)) := by
      rw [integral_inner (integrable_vectorField μ F hm hb y)]
    _ = inner ℂ (∫ s, F s y ∂μ) x := inner_conj_symm _ _

theorem poissonVectorAverage_tendsto (F : ℝ → H →L[ℂ] H)
    (hF : ∀ x, Continuous (fun s => F s x)) (C : ℝ) (hC : ∀ s, ‖F s‖ ≤ C)
    (t : ℝ) (x : H) :
    Tendsto (fun r => poissonVectorAverage F hF C hC t r x) (𝓝 0) (𝓝 (F t x)) := by
  have hlim : Tendsto (fun r : ℝ => ∫ s, F (t + r * s) x
      ∂ProbabilityTheory.cauchyMeasure 0 1) (𝓝 0)
      (𝓝 (∫ _ : ℝ, F t x ∂ProbabilityTheory.cauchyMeasure 0 1)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => C * ‖x‖)
    · exact Eventually.of_forall fun r =>
        ((hF x).comp (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable
    · exact Eventually.of_forall fun r => ae_of_all _ fun s =>
        ((F (t + r * s)).le_opNorm x).trans
          (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg x))
    · exact integrable_const _
    · exact ae_of_all _ fun s => by
        have ht : Tendsto (fun r : ℝ => t + r * s) (𝓝 0) (𝓝 t) := by
          simpa only [zero_mul, add_zero] using
            (tendsto_const_nhds.add (tendsto_id.mul_const s) :
              Tendsto (fun r : ℝ => t + r * s) (𝓝 0) (𝓝 (t + 0 * s)))
        exact (hF x).continuousAt.tendsto.comp ht
  simpa only [poissonVectorAverage, probabilityOperatorIntegral_apply,
    integral_const, probReal_univ, one_smul] using hlim

/-- The adjoints also converge at every time of strong-* continuity. -/
theorem poissonVectorAverage_star_tendsto (F : ℝ → H →L[ℂ] H)
    (hF : ∀ x, Continuous (fun s => F s x))
    (hFs : ∀ x, Continuous (fun s => star (F s) x))
    (C : ℝ) (hC : ∀ s, ‖F s‖ ≤ C) (t : ℝ) (x : H) :
    Tendsto (fun r => star (poissonVectorAverage F hF C hC t r) x)
      (𝓝 0) (𝓝 (star (F t) x)) := by
  have he (r : ℝ) : star (poissonVectorAverage F hF C hC t r) =
      poissonVectorAverage (fun s => star (F s)) hFs C
        (fun s => (norm_star (F s)).le.trans (hC s)) t r := by
    exact (probabilityOperatorIntegral_star (ProbabilityTheory.cauchyMeasure 0 1)
      (fun s => F (t + r * s)) _ _ C _).symm
  simp_rw [he]
  exact poissonVectorAverage_tendsto _ hFs C _ t x

end

end KadisonKastler

end OAI
end

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
-- module Solutions.OAIQ075_KS.Naimark_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe u v w
namespace NaimarkZFC


section GNS

open scoped ComplexOrder InnerProductSpace
open UniformSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem gnsVector_norm_eq_one (f : A →ₚ[ℂ] ℂ) (hf : f 1 = 1) : ‖gnsVector f‖ = 1 := by
  have hs := gnsVector_norm_sq f
  rw [hf, Complex.one_re] at hs
  nlinarith [norm_nonneg (gnsVector f)]

end GNS

open Topology

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MarginalStateMultiplication
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Multiplication bounds from a normal vector-state marginal

A state on the ambient operator algebra need not be normal. Agreement
with a vector state on one algebra is enough for the corresponding
one-sided multiplication estimate.
-/

namespace KadisonKastler

open NaimarkZFC
open scoped ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem state_left_mul_le_of_vector_marginal
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (hφ : IsState φ) (Ω : H)
    (a b : H →L[ℂ] H)
    (ha : φ (a*star a)=((‖star a Ω‖^2 : ℝ) : ℂ)) :
    ‖φ (a*b)‖ ≤ ‖star a Ω‖*‖b‖ := by
  let : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _
  let f := positiveOfSquares φ hφ.2
  have hf : f 1=1 := ((isState_iff φ).mp hφ).1
  have he : φ (a*b)=inner ℂ (gnsOrbit f (star a)) (gnsOrbit f b) := by
    simp only [gnsOrbit_apply,UniformSpace.Completion.inner_coe,
      PositiveLinearMap.preGNS_inner_def,PositiveLinearMap.ofPreGNS_toPreGNS,star_star]
    rfl
  have ha' : ‖gnsOrbit f (star a)‖=‖star a Ω‖ := by
    rw [gnsOrbit_norm,star_star]
    change Real.sqrt (φ (a*star a)).re=‖star a Ω‖
    rw [ha,Complex.ofReal_re,Real.sqrt_sq (norm_nonneg _)]
  have hb : ‖gnsOrbit f b‖ ≤ ‖b‖ := by
    change ‖f.gnsStarAlgHom b (gnsVector f)‖ ≤ ‖b‖
    calc
      _ ≤ ‖f.gnsStarAlgHom b‖*‖gnsVector f‖ := (f.gnsStarAlgHom b).le_opNorm _
      _ ≤ ‖b‖*‖gnsVector f‖ := mul_le_mul_of_nonneg_right
        (NonUnitalStarAlgHom.norm_apply_le f.gnsStarAlgHom b) (norm_nonneg _)
      _ = ‖b‖ := by rw [gnsVector_norm_eq_one f hf,mul_one]
  rw [he]
  exact (norm_inner_le_norm _ _).trans (by rw [ha']; gcongr)

theorem state_right_mul_le_of_vector_marginal
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (hφ : IsState φ) (Ω : H)
    (a b : H →L[ℂ] H)
    (hb : φ (star b*b)=((‖b Ω‖^2 : ℝ) : ℂ)) :
    ‖φ (a*b)‖ ≤ ‖a‖*‖b Ω‖ := by
  let : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (H →L[ℂ] H) := CStarAlgebra.spectralOrderedRing _
  let f := positiveOfSquares φ hφ.2
  have hf : f 1=1 := ((isState_iff φ).mp hφ).1
  have he : φ (a*b)=inner ℂ (gnsOrbit f (star a)) (gnsOrbit f b) := by
    simp only [gnsOrbit_apply,UniformSpace.Completion.inner_coe,
      PositiveLinearMap.preGNS_inner_def,PositiveLinearMap.ofPreGNS_toPreGNS,star_star]
    rfl
  have hb' : ‖gnsOrbit f b‖=‖b Ω‖ := by
    rw [gnsOrbit_norm]
    change Real.sqrt (φ (star b*b)).re=‖b Ω‖
    rw [hb,Complex.ofReal_re,Real.sqrt_sq (norm_nonneg _)]
  have ha : ‖gnsOrbit f (star a)‖ ≤ ‖a‖ := by
    change ‖f.gnsStarAlgHom (star a) (gnsVector f)‖ ≤ ‖a‖
    calc
      _ ≤ ‖f.gnsStarAlgHom (star a)‖*‖gnsVector f‖ := (f.gnsStarAlgHom (star a)).le_opNorm _
      _ ≤ ‖star a‖*‖gnsVector f‖ := mul_le_mul_of_nonneg_right
        (NonUnitalStarAlgHom.norm_apply_le f.gnsStarAlgHom (star a)) (norm_nonneg _)
      _ = ‖a‖ := by rw [gnsVector_norm_eq_one f hf,mul_one,norm_star]
  rw [he]
  exact (norm_inner_le_norm _ _).trans (by rw [hb']; gcongr)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MarginalStateApproximation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Strong approximation of products under normal marginals

This estimates a possibly nonnormal ambient state using its vector-state
marginals. It is the product approximation step of Marrakchi's Lemma 4.1.
-/

namespace KadisonKastler

open Filter NaimarkZFC
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem state_product_sub_le_of_vector_marginals
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (hφ : IsState φ) (Ω : H)
    (a b a' b' : H →L[ℂ] H)
    (ha : φ ((a-a')*star (a-a'))=((‖star (a-a') Ω‖^2 : ℝ) : ℂ))
    (hb : φ (star (b-b')*(b-b'))=((‖(b-b') Ω‖^2 : ℝ) : ℂ)) :
    ‖φ (a*b)-φ (a'*b')‖ ≤
      ‖star (a-a') Ω‖*‖b‖+‖a'‖*‖(b-b') Ω‖ := by
  have he : a*b-a'*b'=(a-a')*b+a'*(b-b') := by noncomm_ring
  rw [← map_sub,he,map_add]
  exact (norm_add_le _ _).trans (add_le_add
    (state_left_mul_le_of_vector_marginal φ hφ Ω (a-a') b ha)
    (state_right_mul_le_of_vector_marginal φ hφ Ω a' (b-b') hb))

theorem state_product_tendsto_of_vector_marginals
    {I : Type*} {l : Filter I}
    (φ : (H →L[ℂ] H) →L[ℂ] ℂ) (hφ : IsState φ) (Ω : H)
    (a b : I → H →L[ℂ] H) (a₀ b₀ : H →L[ℂ] H)
    (ha : ∀ i, φ ((a i-a₀)*star (a i-a₀))=((‖star (a i-a₀) Ω‖^2 : ℝ) : ℂ))
    (hb : ∀ i, φ (star (b i-b₀)*(b i-b₀))=((‖(b i-b₀) Ω‖^2 : ℝ) : ℂ))
    (B : ℝ) (hB : ∀ i, ‖b i‖ ≤ B)
    (hca : Tendsto (fun i => star (a i-a₀) Ω) l (𝓝 0))
    (hcb : Tendsto (fun i => (b i-b₀) Ω) l (𝓝 0)) :
    Tendsto (fun i => φ (a i*b i)) l (𝓝 (φ (a₀*b₀))) := by
  have hlim : Tendsto (fun i => ‖star (a i-a₀) Ω‖*B+‖a₀‖*‖(b i-b₀) Ω‖)
      l (𝓝 0) := by
    simpa only [norm_zero,zero_mul,mul_zero,add_zero] using
      (hca.norm.mul_const B).add (hcb.norm.const_mul ‖a₀‖)
  have hn : Tendsto (fun i => ‖φ (a i*b i)-φ (a₀*b₀)‖) l (𝓝 0) := by
    apply squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) hlim
    exact (state_product_sub_le_of_vector_marginals φ hφ Ω (a i) (b i) a₀ b₀
      (ha i) (hb i)).trans (add_le_add
        (mul_le_mul_of_nonneg_left (hB i) (norm_nonneg _)) le_rfl)
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

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
-- module Solutions.OAIQ075_KS.KadisonKastler_PoissonActionApproximation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instIsProbabilityMeasureBilateralWalkPathBilateralWalkLaw _root_.OAI.KadisonKastler.instIsProbabilityMeasureRandomWalkBoundaryRandomWalkBoundaryMeasure _root_.OAI.KadisonKastler.randomWalkPathLaw_probability _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Bounded, norm-continuous approximations within invariant algebras -/

namespace KadisonKastler

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem stateActionOrbit_zero (a : H →L[ℂ] H) : stateActionOrbit U a 0=a := by
  change unitaryConj (U 1) a=a
  rw [map_one,unitaryConj_one]

theorem stateActionOrbit_star (a : H →L[ℂ] H) (t : ℝ) :
    stateActionOrbit U (star a) t=star (stateActionOrbit U a t) := by
  let e : (H →L[ℂ] H) ≃⋆ₐ[ℂ] (H →L[ℂ] H) :=
    Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (U (Multiplicative.ofAdd t))
  exact map_star e a

theorem poissonActionApprox_norm (a : H →L[ℂ] H) (r : ℝ) :
    ‖poissonActionApprox U hU a r‖ ≤ ‖a‖ :=
  norm_probabilityOperatorIntegral_le (ProbabilityTheory.cauchyMeasure 0 1)
    (fun t => stateActionOrbit U a (0+r*t))
    (fun x => ((stateActionOrbit_continuous U hU a x).comp
      (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable)
    (norm_nonneg a)
    (Eventually.of_forall fun t => (stateActionOrbit_norm U a (0+r*t)).le)

theorem poissonActionApprox_mem (M : VonNeumannAlgebra H)
    (hnormal : ∀ t a, a ∈ M → stateActionOrbit U a t ∈ M)
    (a : H →L[ℂ] H) (ha : a ∈ M) (r : ℝ) : poissonActionApprox U hU a r ∈ M :=
  probabilityOperatorIntegral_mem (ProbabilityTheory.cauchyMeasure 0 1)
    (fun t => stateActionOrbit U a (0+r*t))
    (fun x => ((stateActionOrbit_continuous U hU a x).comp
      (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable)
    ‖a‖ (Eventually.of_forall fun t => (stateActionOrbit_norm U a (0+r*t)).le) M
    (Eventually.of_forall fun t => hnormal (0+r*t) a ha)

theorem poissonActionApprox_tendsto (a : H →L[ℂ] H) (x : H) :
    Tendsto (fun r => poissonActionApprox U hU a r x) (𝓝 0) (𝓝 (a x)) := by
  have h := poissonVectorAverage_tendsto (stateActionOrbit U a)
    (stateActionOrbit_continuous U hU a) ‖a‖
    (fun t => (stateActionOrbit_norm U a t).le) 0 x
  simpa only [poissonActionApprox,stateActionOrbit_zero] using h

theorem poissonActionApprox_star_tendsto (a : H →L[ℂ] H) (x : H) :
    Tendsto (fun r => star (poissonActionApprox U hU a r) x) (𝓝 0) (𝓝 (star a x)) := by
  have hc (y : H) : Continuous (fun t => star (stateActionOrbit U a t) y) := by
    simp_rw [← stateActionOrbit_star]
    exact stateActionOrbit_continuous U hU (star a) y
  have h := poissonVectorAverage_star_tendsto (stateActionOrbit U a)
    (stateActionOrbit_continuous U hU a) hc ‖a‖
    (fun t => (stateActionOrbit_norm U a t).le) 0 x
  simpa only [poissonActionApprox,stateActionOrbit_zero] using h

theorem poissonActionApprox_orbit_continuous (a : H →L[ℂ] H) {r : ℝ} (hr : 0 < r) :
    Continuous (stateActionOrbit U (poissonActionApprox U hU a r)) := by
  have he (s : ℝ) : stateActionOrbit U (poissonActionApprox U hU a r) s =
      poissonVectorAverage (stateActionOrbit U a) (stateActionOrbit_continuous U hU a)
        ‖a‖ (fun t => (stateActionOrbit_norm U a t).le) s r := by
    ext x
    let u := U (Multiplicative.ofAdd s)
    have hi := integrable_bounded_operator_vector (ProbabilityTheory.cauchyMeasure 0 1)
      (fun t => stateActionOrbit U a (0+r*t))
      (fun y => ((stateActionOrbit_continuous U hU a y).comp
        (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable)
      (Eventually.of_forall fun t => (stateActionOrbit_norm U a (0+r*t)).le)
      (star (u : H →L[ℂ] H) x)
    change (u : H →L[ℂ] H)
        (∫ t, stateActionOrbit U a (0+r*t) (star (u : H →L[ℂ] H) x)
          ∂ProbabilityTheory.cauchyMeasure 0 1) =
      ∫ t, stateActionOrbit U a (s+r*t) x ∂ProbabilityTheory.cauchyMeasure 0 1
    rw [← (u : H →L[ℂ] H).integral_comp_comm hi]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro t
    change (u : H →L[ℂ] H) (stateActionOrbit U a (0+r*t) (star (u : H →L[ℂ] H) x))=
      stateActionOrbit U a (s+r*t) x
    rw [zero_add,stateActionOrbit_add]
    rfl
  change Continuous (fun s : ℝ => stateActionOrbit U (poissonActionApprox U hU a r) s)
  simp_rw [he]
  exact continuous_poissonVectorAverage (stateActionOrbit U a)
    (stateActionOrbit_continuous U hU a) (norm_nonneg a)
    (fun t => (stateActionOrbit_norm U a t).le) hr

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NormalMarginalAgreement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Recovering full product agreement from normal marginals

The two states may be nonnormal on the ambient operator algebra. Their
normal marginals suffice to pass from the smoothed products to all products.
-/

namespace KadisonKastler

open Filter NaimarkZFC
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem productVectorState_square (Ω : H) (a : H →L[ℂ] H) :
    productVectorState Ω (star a*a)=((‖a Ω‖^2 : ℝ) : ℂ) := by
  change inner ℂ Ω (star a (a Ω))=_
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  simp only [inner_self_eq_norm_sq_to_K,Complex.ofReal_pow]
  rfl

theorem normal_marginal_product_agreement_oai
    (U : Multiplicative ℝ →* unitary (H →L[ℂ] H))
    (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
    (M N : VonNeumannAlgebra H)
    (hM : ∀ t a, a ∈ M → stateActionOrbit U a t ∈ M)
    (hN : ∀ t a, a ∈ N → stateActionOrbit U a t ∈ N)
    (Ω : H) (φ ψ : (H →L[ℂ] H) →L[ℂ] ℂ) (hφ : IsState φ) (hψ : IsState ψ)
    (hφM : ∀ a ∈ M, φ a=productVectorState Ω a)
    (hψM : ∀ a ∈ M, ψ a=productVectorState Ω a)
    (hφN : ∀ a ∈ N, φ a=productVectorState Ω a)
    (hψN : ∀ a ∈ N, ψ a=productVectorState Ω a)
    (hagrees : ∀ a, Continuous (stateActionOrbit U a) → φ a=ψ a)
    (a b : H →L[ℂ] H) (ha : a ∈ M) (hb : b ∈ N) : φ (a*b)=ψ (a*b) := by
  let r (n : ℕ) : ℝ := 1/(n+1)
  have hr (n : ℕ) : 0 < r n := by dsimp [r] <;> positivity
  have hrzero : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let A (n : ℕ) := poissonActionApprox U hU a (r n)
  let B (n : ℕ) := poissonActionApprox U hU b (r n)
  have hAM (n : ℕ) : A n ∈ M := poissonActionApprox_mem U hU M hM a ha (r n)
  have hBN (n : ℕ) : B n ∈ N := poissonActionApprox_mem U hU N hN b hb (r n)
  have hconvA : Tendsto (fun n => star (A n-a) Ω) atTop (𝓝 0) := by
    have ht := ((poissonActionApprox_star_tendsto U hU a Ω).comp hrzero).sub_const (star a Ω)
    simpa only [A,Function.comp_def,star_sub,sub_apply,sub_self] using ht
  have hconvB : Tendsto (fun n => (B n-b) Ω) atTop (𝓝 0) := by
    have ht := ((poissonActionApprox_tendsto U hU b Ω).comp hrzero).sub_const (b Ω)
    simpa only [B,Function.comp_def,sub_apply,sub_self] using ht
  have hlim (ρ : (H →L[ℂ] H) →L[ℂ] ℂ) (hρ : IsState ρ)
      (hρM : ∀ c ∈ M, ρ c=productVectorState Ω c)
      (hρN : ∀ c ∈ N, ρ c=productVectorState Ω c) :
      Tendsto (fun n => ρ (A n*B n)) atTop (𝓝 (ρ (a*b))) := by
    apply state_product_tendsto_of_vector_marginals ρ hρ Ω A B a b
      (B := ‖b‖) (hB := fun n => poissonActionApprox_norm U hU b (r n))
      (hca := hconvA) (hcb := hconvB)
    · intro n
      have hd := M.sub_mem (hAM n) ha
      rw [hρM _ (M.mul_mem hd (M.toStarSubalgebra.star_mem' hd))]
      simpa only [star_star] using productVectorState_square Ω (star (A n-a))
    · intro n
      have hd := N.sub_mem (hBN n) hb
      rw [hρN _ (N.mul_mem (N.toStarSubalgebra.star_mem' hd) hd)]
      exact productVectorState_square Ω (B n-b)
  have he (n : ℕ) : φ (A n*B n)=ψ (A n*B n) := by
    apply hagrees
    change Continuous (fun t : ℝ => stateActionOrbit U (A n*B n) t)
    have hmul (t : ℝ) : stateActionOrbit U (A n*B n) t=
        stateActionOrbit U (A n) t*stateActionOrbit U (B n) t :=
      (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (U (Multiplicative.ofAdd t))).map_mul _ _
    simp_rw [hmul]
    exact (poissonActionApprox_orbit_continuous U hU a (hr n)).mul
      (poissonActionApprox_orbit_continuous U hU b (hr n))
  have ht := hlim ψ hψ hψM hψN
  rw [← funext he] at ht
  exact tendsto_nhds_unique (hlim φ hφ hφM hφN) ht

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.normal_marginal_product_agreement_oai.{u_1} := @OAI.KadisonKastler.normal_marginal_product_agreement_oai.{u_1}
