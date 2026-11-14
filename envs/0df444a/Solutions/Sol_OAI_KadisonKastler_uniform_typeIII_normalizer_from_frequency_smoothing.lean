-- Prove2me | solution 1 for OAI.KadisonKastler.uniform_typeIII_normalizer_from_frequency_smoothing
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T07:11:11.208377+00:00
-- url     : https://prove2.me/submissions/795f7467-ef93-4ff9-987f-46902022f74c

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
import Definitions.Def_Q260K065
import Theorems.Thm_OAI_KadisonKastler_FrequencySmoothing_continuous_smooth
import Theorems.Thm_OAI_KadisonKastler_FrequencySmoothing_infDist_smooth_sandwich_le
import Theorems.Thm_OAI_KadisonKastler_FrequencySmoothing_norm_product_sub_one_le
import Theorems.Thm_OAI_KadisonKastler_uniform_typeIII_normalizer_from_smoothing

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.conjugationFamily_apply _root_.OAI.KadisonKastler.ScalarInvariantMean.stateOrbitScalar_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.unitaryConjugateEquiv_apply _root_.OAI.KadisonKastler.unitaryConjugateHom_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

theorem isometry_unitaryConj (v : unitary (H →L[ℂ] H)) : Isometry (unitaryConj v) := by
  apply Isometry.of_dist_eq
  intro x y
  simp only [dist_eq_norm, ← unitaryConj_sub, norm_unitaryConj]

theorem unitaryConj_unitBall {M N : VonNeumannAlgebra H}
    {v : unitary (H →L[ℂ] H)} (hv : Conjugates v M N) :
    unitaryConj v '' unitBall M = unitBall N := by
  change unitaryConj v '' (M : Set (H →L[ℂ] H)) = (N : Set (H →L[ℂ] H)) at hv
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, by simpa using hx.2⟩
    change unitaryConj v x ∈ (N : Set (H →L[ℂ] H))
    rw [← hv]
    exact Set.mem_image_of_mem _ hx.1
  · intro hy
    obtain ⟨x, hx, rfl⟩ := (show y ∈ unitaryConj v '' (M : Set (H →L[ℂ] H)) from
      hv.symm ▸ hy.1)
    exact ⟨x, ⟨hx, by simpa using hy.2⟩, rfl⟩

/-- The same unitary change of position leaves the distance unchanged. -/
theorem kkDistance_eq_of_conjugates {M N P Q : VonNeumannAlgebra H}
    {v : unitary (H →L[ℂ] H)} (hMN : Conjugates v M N) (hPQ : Conjugates v P Q) :
    kkDistance N Q = kkDistance M P := by
  unfold kkDistance
  rw [← unitaryConj_unitBall hMN, ← unitaryConj_unitBall hPQ]
  exact Metric.hausdorffDist_image (isometry_unitaryConj v)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AmenableEmbedding
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Moving an injective subalgebra into a nearby algebra

The published input is the one-sided assertion of Cameron--Christensen--
Sinclair--Smith--White--Wiggins, *Kadison--Kastler stable factors*, Duke
Math. J. 163 (2014), Theorem 3.3(i), arXiv:1209.4116v3, p. 13. Only
the inclusion and the displacement bound `150 * γ` are retained.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The algebra just constructed is the exact unitary image. -/
theorem conjugates_unitaryConjugateAlgebra (w : unitary (H →L[ℂ] H))
    (M : VonNeumannAlgebra H) : Conjugates w M (unitaryConjugateAlgebra w M) := rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PoissonVectorAverage
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instIsProbabilityMeasureBilateralWalkPathBilateralWalkLaw _root_.OAI.KadisonKastler.instIsProbabilityMeasureRandomWalkBoundaryRandomWalkBoundaryMeasure _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.randomWalkPathLaw_probability _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
theorem norm_measurablePoissonAverage_le (F : ℝ → H →L[ℂ] H)
    (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ᵐ s, ‖F s‖ ≤ C) (t r : ℝ) (hr : 0 < r) :
    ‖measurablePoissonAverage F hF C hC t r hr‖ ≤ C :=
  norm_probabilityOperatorIntegral_le _ _ _ hC0 _

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

theorem measurablePoissonAverage_eq_poissonVectorAverage
    (F : ℝ → H →L[ℂ] H) (hF : ∀ x, Continuous (fun s => F s x))
    (C : ℝ) (hC : ∀ s, ‖F s‖ ≤ C) (t r : ℝ) (hr : 0 < r) :
    measurablePoissonAverage F (fun x => (hF x).aestronglyMeasurable) C
      (ae_of_all _ hC) t r hr = poissonVectorAverage F hF C hC t r := by
  ext x
  rw [measurablePoissonAverage_apply, poissonVectorAverage_apply_eq_integral F hF C hC t hr x]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PoissonBoundaryLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instIsProbabilityMeasureBilateralWalkPathBilateralWalkLaw _root_.OAI.KadisonKastler.instIsProbabilityMeasureRandomWalkBoundaryRandomWalkBoundaryMeasure _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.randomWalkPathLaw_probability _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem modulatedUnitaryField_star_continuous (W : ℝ → unitary (H →L[ℂ] H))
    (hW : ∀ x, Continuous (fun t => star (W t : H →L[ℂ] H) x)) (x : H) :
    Continuous (fun t => star (modulatedUnitaryField W t) x) := by
  have hc : Continuous (fun t : ℝ => star (Circle.exp t : ℂ)) :=
    (continuous_subtype_val.comp Circle.exp.continuous).star
  have he (t : ℝ) : star (modulatedUnitaryField W t) x =
      star (Circle.exp t : ℂ) • star (W t : H →L[ℂ] H) x := by
    simp only [modulatedUnitaryField, star_smul, smul_apply]
  simp_rw [he]
  exact hc.smul (hW x)

theorem norm_poissonBoundaryApprox_le (W : ℝ → unitary (H →L[ℂ] H))
    (hW : ∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x)) (t r : ℝ) :
    ‖poissonBoundaryApprox W hW t r‖ ≤ Real.exp r := by
  have hb := norm_probabilityOperatorIntegral_le (ProbabilityTheory.cauchyMeasure 0 1)
    (fun s => modulatedUnitaryField W (t + r * s))
    (fun x => ((modulatedUnitaryField_continuous W hW x).comp
      (continuous_const.add (continuous_const.mul continuous_id))).aestronglyMeasurable) zero_le_one
    (ae_of_all _ fun _ => norm_modulatedUnitaryField_le_one W _)
  have hs : ‖(Real.exp r : ℂ) * star (Circle.exp t : ℂ)‖ = Real.exp r := by
    rw [norm_mul, norm_star, Circle.norm_coe, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos r)]
  rw [poissonBoundaryApprox, norm_smul, hs]
  exact (mul_le_mul_of_nonneg_left hb (Real.exp_pos r).le).trans_eq (mul_one _)

theorem poissonBoundaryApprox_tendsto (W : ℝ → unitary (H →L[ℂ] H))
    (hW : ∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x)) (t : ℝ) (x : H) :
    Tendsto (fun r => poissonBoundaryApprox W hW t r x) (𝓝 0)
      (𝓝 ((W t : H →L[ℂ] H) x)) := by
  have hs : Tendsto (fun r : ℝ => (Real.exp r : ℂ) * star (Circle.exp t : ℂ))
      (𝓝 0) (𝓝 (star (Circle.exp t : ℂ))) := by
    simpa only [Function.comp_apply, Real.exp_zero, Complex.ofReal_one, one_mul] using
      ((Complex.continuous_ofReal.comp Real.continuous_exp).continuousAt (x := 0)).tendsto.mul_const
        (star (Circle.exp t : ℂ))
  have h := hs.smul (poissonVectorAverage_tendsto (modulatedUnitaryField W)
    (modulatedUnitaryField_continuous W hW) 1 (norm_modulatedUnitaryField_le_one W) t x)
  have hz : star (Circle.exp t : ℂ) * (Circle.exp t : ℂ) = 1 := by
    rw [Complex.star_def, Complex.conj_mul']
    simp only [Circle.norm_coe, one_pow, Complex.ofReal_one]
  simpa only [poissonBoundaryApprox, smul_apply, modulatedUnitaryField,
    smul_smul, hz, one_smul] using h

theorem poissonBoundaryApprox_star_tendsto (W : ℝ → unitary (H →L[ℂ] H))
    (hW : ∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x))
    (hWs : ∀ x, Continuous (fun t => star (W t : H →L[ℂ] H) x)) (t : ℝ) (x : H) :
    Tendsto (fun r => star (poissonBoundaryApprox W hW t r) x) (𝓝 0)
      (𝓝 (star (W t : H →L[ℂ] H) x)) := by
  have hs : Tendsto (fun r : ℝ => star ((Real.exp r : ℂ) * star (Circle.exp t : ℂ)))
      (𝓝 0) (𝓝 (Circle.exp t : ℂ)) := by
    simpa only [Function.comp_apply, Real.exp_zero, Complex.ofReal_one, one_mul, star_star] using
      (((Complex.continuous_ofReal.comp Real.continuous_exp).continuousAt (x := 0)).tendsto.mul_const
        (star (Circle.exp t : ℂ))).star
  have h := hs.smul (poissonVectorAverage_star_tendsto (modulatedUnitaryField W)
    (modulatedUnitaryField_continuous W hW) (modulatedUnitaryField_star_continuous W hWs)
      1 (norm_modulatedUnitaryField_le_one W) t x)
  have hz : (Circle.exp t : ℂ) * star (Circle.exp t : ℂ) = 1 := by
    rw [mul_comm, Complex.star_def, Complex.conj_mul']
    simp only [Circle.norm_coe, one_pow, Complex.ofReal_one]
  simpa only [poissonBoundaryApprox, star_smul, smul_apply, modulatedUnitaryField,
    smul_smul, hz, one_smul] using h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DemodulatedPoisson
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

private theorem norm_demodulation_scalar (t r : ℝ) :
    ‖(Real.exp r : ℂ) * star (Circle.exp t : ℂ)‖ = Real.exp r := by
  rw [norm_mul, norm_star, Circle.norm_coe, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos r)]

omit [CompleteSpace H] in
theorem norm_demodulatedPoissonAverage_le
    (F : ℝ → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ᵐ s, ‖F s‖ ≤ C) (t r : ℝ) (hr : 0 < r) :
    ‖demodulatedPoissonAverage F hF C hC t r hr‖ ≤ Real.exp r * C := by
  rw [demodulatedPoissonAverage, norm_smul, norm_demodulation_scalar]
  exact mul_le_mul_of_nonneg_left (norm_measurablePoissonAverage_le F hF hC0 hC t r hr)
    (Real.exp_pos r).le

/-- The comparison holds at every time, even when the boundary estimates
hold only almost everywhere. -/
theorem norm_demodulatedPoissonAverage_sub_boundary_le
    (F : ℝ → H →L[ℂ] H) (hF : ∀ x, AEStronglyMeasurable (fun s => F s x) volume)
    (C : ℝ) (hC : ∀ᵐ s, ‖F s‖ ≤ C)
    (W : ℝ → unitary (H →L[ℂ] H))
    (hW : ∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x))
    {δ : ℝ} (hδ : 0 ≤ δ) (hFW : ∀ᵐ s, ‖F s - modulatedUnitaryField W s‖ ≤ δ)
    (t r : ℝ) (hr : 0 < r) :
    ‖demodulatedPoissonAverage F hF C hC t r hr - poissonBoundaryApprox W hW t r‖ ≤
      Real.exp r * δ := by
  have h := norm_measurablePoissonAverage_sub_le F (modulatedUnitaryField W) hF
    (fun x => (modulatedUnitaryField_continuous W hW x).aestronglyMeasurable)
    C 1 hC (ae_of_all _ (norm_modulatedUnitaryField_le_one W)) hδ hFW t r hr
  have he := measurablePoissonAverage_eq_poissonVectorAverage (modulatedUnitaryField W)
    (modulatedUnitaryField_continuous W hW) 1 (norm_modulatedUnitaryField_le_one W) t r hr
  unfold demodulatedPoissonAverage poissonBoundaryApprox
  rw [← he, ← smul_sub, norm_smul, norm_demodulation_scalar]
  exact mul_le_mul_of_nonneg_left h (Real.exp_pos r).le

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DemodulatedCharacter
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The pointwise identity behind inverse comparison, for an arbitrary
unitary field without continuity assumptions. -/
theorem modulatedUnitaryField_mul_inverse (W : ℝ → unitary (H →L[ℂ] H)) (s : ℝ) :
    modulatedUnitaryField W s * modulatedUnitaryField (fun t => star (W t)) s =
      poissonCharacterField 2 s := by
  simp only [modulatedUnitaryField, poissonCharacterField,
    smul_mul_assoc, mul_smul_comm, smul_smul, Unitary.coe_star,
    Unitary.mul_star_self_of_mem (W s).property]
  rw [two_mul, Circle.exp_add, Circle.coe_mul]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ProbabilityMatrixDistance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Distance to an algebra after vector integration

Diagonal amplification commutes with the actual vector integral. Applying
the published complete commutant-distance bound to the commutant gives
an algebra approximation without choosing measurable nearest points.
-/

namespace KadisonKastler

open MeasureTheory
open scoped BigOperators Pointwise

noncomputable section

variable {S H : Type*} [MeasurableSpace S]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.matrixIntegralStarOrder
attribute [local instance] OAI.KadisonKastler.integralSourceStarOrder
/-- Scalar multiplication scales distance to the concrete complex algebra. -/
theorem infDist_smul_algebra (M : VonNeumannAlgebra H) (z : ℂ)
    (T : H →L[ℂ] H) :
    Metric.infDist (z • T) (M : Set (H →L[ℂ] H)) =
      ‖z‖ * Metric.infDist T (M : Set (H →L[ℂ] H)) := by
  classical
  by_cases hz : z = 0
  · subst z
    simp only [zero_smul, norm_zero, zero_mul]
    exact Metric.infDist_zero_of_mem M.zero_mem
  · have hset : z • (M : Set (H →L[ℂ] H)) = (M : Set (H →L[ℂ] H)) := by
      ext y
      simp only [Set.mem_smul_set]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact M.toStarSubalgebra.smul_mem hx z
      · intro hy
        refine ⟨z⁻¹ • y, M.toStarSubalgebra.smul_mem hy z⁻¹, ?_⟩
        rw [smul_smul, mul_inv_cancel₀ hz, one_smul]
    have he := infDist_smul₀ hz (M : Set (H →L[ℂ] H)) T
    rwa [hset] at he

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ModulatedAlgebraGap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Boundary algebra errors from the ordinary conjugacy gap

Scaling the unit-ball estimate supplies the exact boundary hypothesis
used in analytic smoothing, in both directions of conjugation.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem infDist_le_norm_mul_of_kkDistance_lt
    {M N : VonNeumannAlgebra H} {δ : ℝ} (hgap : kkDistance M N < δ)
    {x : H →L[ℂ] H} (hx : x ∈ M) :
    Metric.infDist x (N : Set (H →L[ℂ] H)) ≤ δ * ‖x‖ := by
  by_cases hx0 : x = 0
  · subst x
    rw [Metric.infDist_zero_of_mem (show (0 : H →L[ℂ] H) ∈ (N : Set (H →L[ℂ] H)) from N.zero_mem), norm_zero, mul_zero]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  let y : H →L[ℂ] H := (‖x‖⁻¹ : ℂ) • x
  have hy : y ∈ unitBall M := by
    refine ⟨M.toStarSubalgebra.smul_mem hx _, ?_⟩
    simp [y, norm_smul, Complex.norm_real, inv_mul_cancel₀ hn.ne']
  obtain ⟨z, hz, hyz⟩ := exists_unitBall_approx hy hgap
  have hdy : Metric.infDist y (N : Set (H →L[ℂ] H)) ≤ δ :=
    (Metric.infDist_le_dist_of_mem hz.1).trans (by simpa only [dist_eq_norm] using hyz.le)
  have he : x = (‖x‖ : ℂ) • y := by
    change x = (‖x‖ : ℂ) • ((‖x‖⁻¹ : ℂ) • x)
    rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hn.ne'), one_smul]
  calc
    Metric.infDist x (N : Set (H →L[ℂ] H)) =
        ‖x‖ * Metric.infDist y (N : Set (H →L[ℂ] H)) := by
      conv_lhs => rw [he, infDist_smul_algebra]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
    _ ≤ δ * ‖x‖ := by nlinarith

theorem kkDistance_inverse_conjugate (M : VonNeumannAlgebra H)
    (v : unitary (H →L[ℂ] H)) :
    kkDistance (unitaryConjugateAlgebra (star v) M) M =
      kkDistance (unitaryConjugateAlgebra v M) M := by
  have h := kkDistance_eq_of_conjugates
    (conjugates_unitaryConjugateAlgebra v M).symm
    (conjugates_unitaryConjugateAlgebra (star v) M)
  exact (kkDistance_comm _ _).trans h

theorem modulated_sandwich_eq (W : ℝ → unitary (H →L[ℂ] H))
    (t : ℝ) (x : H →L[ℂ] H) :
    modulatedUnitaryField W t * x * modulatedUnitaryField (fun s => star (W s)) t =
      ((Circle.exp t : ℂ) * (Circle.exp t : ℂ)) • unitaryConj (W t) x := by
  simp only [modulatedUnitaryField, Unitary.coe_star, unitaryConj,
    smul_mul_assoc, mul_smul_comm, smul_smul]

theorem infDist_modulated_sandwich_le
    (M : VonNeumannAlgebra H) (W : ℝ → unitary (H →L[ℂ] H))
    {δ : ℝ} (hgap : ∀ t, kkDistance (unitaryConjugateAlgebra (W t) M) M < δ)
    (t : ℝ) (x : H →L[ℂ] H) (hx : x ∈ M) :
    Metric.infDist
      (modulatedUnitaryField W t * x * modulatedUnitaryField (fun s => star (W s)) t)
      (M : Set (H →L[ℂ] H)) ≤ δ * ‖x‖ := by
  rw [modulated_sandwich_eq, infDist_smul_algebra, norm_mul, Circle.norm_coe, one_mul,
    one_mul]
  have hm : unitaryConj (W t) x ∈ unitaryConjugateAlgebra (W t) M := by
    change unitaryConj (W t) x ∈ (unitaryConjugateAlgebra (W t) M : Set (H →L[ℂ] H))
    rw [← conjugates_unitaryConjugateAlgebra (W t) M]
    exact Set.mem_image_of_mem _ hx
  simpa only [norm_unitaryConj] using infDist_le_norm_mul_of_kkDistance_lt (hgap t) hm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FrequencySmoothing
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

attribute [local instance] OAI.KadisonKastler.frequencySmoothingStarOrder
variable {F G : ℝ → H →L[ℂ] H} {δ : ℝ}

theorem norm_smooth_le (A : FrequencySmoothing F δ) (hδ : 0 ≤ δ)
    (t r : ℝ) (hr : 0 < r) : ‖A.smooth t r hr‖ ≤ Real.exp r * (1 + 2 * δ) :=
  norm_demodulatedPoissonAverage_le A.boundary A.measurable (by positivity) A.bounded t r hr

theorem norm_smooth_le_one_add (A : FrequencySmoothing F δ)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 8)
    (t r : ℝ) (hr : 0 < r) (hrδ : r ≤ δ) : ‖A.smooth t r hr‖ ≤ 1 + 5 * δ := by
  have habs : |r| ≤ 1 := by rw [abs_of_pos hr]; linarith
  have he := Real.abs_exp_sub_one_le habs
  rw [abs_of_pos hr] at he
  have he' : Real.exp r ≤ 1 + 2 * δ := by
    linarith [le_abs_self (Real.exp r - 1)]
  exact (A.norm_smooth_le hδ t r hr).trans
    ((mul_le_mul_of_nonneg_right he' (by positivity)).trans (by nlinarith))

/-- Comparison to the original continuous modular field, using the same
boundary Poisson operator that already has strong-star convergence. -/
theorem norm_smooth_sub_boundary_le
    (W : ℝ → unitary (H →L[ℂ] H))
    (A : FrequencySmoothing (modulatedUnitaryField W) δ)
    (hW : ∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x))
    (hδ : 0 ≤ δ) (t r : ℝ) (hr : 0 < r) :
    ‖A.smooth t r hr - poissonBoundaryApprox W hW t r‖ ≤ Real.exp r * (2 * δ) :=
  norm_demodulatedPoissonAverage_sub_boundary_le A.boundary A.measurable (1 + 2 * δ)
    A.bounded W hW (by positivity) A.close t r hr

theorem norm_smooth_sub_boundary_le_four
    (W : ℝ → unitary (H →L[ℂ] H))
    (A : FrequencySmoothing (modulatedUnitaryField W) δ)
    (hW : ∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x))
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 8)
    (t r : ℝ) (hr : 0 < r) (hrδ : r ≤ δ) :
    ‖A.smooth t r hr - poissonBoundaryApprox W hW t r‖ ≤ 4 * δ := by
  have he := Real.abs_exp_sub_one_le (x := r)
    (show |r| ≤ 1 by rw [abs_of_pos hr]; linarith)
  rw [abs_of_pos hr] at he
  have he' : Real.exp r ≤ 2 := by linarith [le_abs_self (Real.exp r - 1)]
  exact (A.norm_smooth_sub_boundary_le W hW hδ t r hr).trans
    ((mul_le_mul_of_nonneg_right he' (by positivity)).trans_eq (by ring))

end FrequencySmoothing

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SmoothingHeightSequence
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Positive smoothing heights tending to the boundary -/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

theorem smoothingHeight_pos {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    0 < smoothingHeight δ n := div_pos hδ (by positivity)

theorem smoothingHeight_le {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    smoothingHeight δ n ≤ δ := by
  change δ / ((n : ℝ) + 1) ≤ δ
  rw [div_le_iff₀ (by positivity)]
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem smoothingHeight_tendsto (δ : ℝ) :
    Tendsto (smoothingHeight δ) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => δ / ((n : ℝ) + 1)) atTop (𝓝 0)
  simpa only [smoothingHeight, one_div, div_eq_mul_inv, mul_zero, one_mul] using
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem poissonBoundaryApprox_smoothingHeight_tendsto
    (W : ℝ → unitary (H →L[ℂ] H))
    (hW : ∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x))
    (δ t : ℝ) (x : H) :
    Tendsto (fun n => poissonBoundaryApprox W hW t (smoothingHeight δ n) x) atTop
      (𝓝 ((W t : H →L[ℂ] H) x)) :=
  (poissonBoundaryApprox_tendsto W hW t x).comp (smoothingHeight_tendsto δ)

theorem poissonBoundaryApprox_star_smoothingHeight_tendsto
    (W : ℝ → unitary (H →L[ℂ] H))
    (hW : ∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x))
    (hWs : ∀ x, Continuous (fun t => star (W t : H →L[ℂ] H) x))
    (δ t : ℝ) (x : H) :
    Tendsto (fun n => star (poissonBoundaryApprox W hW t (smoothingHeight δ n)) x) atTop
      (𝓝 (star (W t : H →L[ℂ] H) x)) :=
  (poissonBoundaryApprox_star_tendsto W hW hWs t x).comp (smoothingHeight_tendsto δ)

theorem norm_poissonBoundaryApprox_smoothingHeight_le_two
    (W : ℝ → unitary (H →L[ℂ] H))
    (hW : ∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x))
    {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8) (n : ℕ) (t : ℝ) :
    ‖poissonBoundaryApprox W hW t (smoothingHeight δ n)‖ ≤ 2 := by
  have hr := smoothingHeight_pos hδ n
  have hrδ := smoothingHeight_le hδ.le n
  have he := Real.abs_exp_sub_one_le
    (show |smoothingHeight δ n| ≤ 1 by rw [abs_of_pos hr]; linarith)
  rw [abs_of_pos hr] at he
  exact (norm_poissonBoundaryApprox_le W hW t (smoothingHeight δ n)).trans
    (by linarith [le_abs_self (Real.exp (smoothingHeight δ n) - 1)])

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FrequencyNormalizer
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.factorizationCyclicSpace_complete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.operatorFieldAlgebraCStar _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.ScalarInvariantMean.algebraMean_coe _root_.OAI.KadisonKastler.algebraRow_apply _root_.OAI.KadisonKastler.ambientAlgebraFamily_apply _root_.OAI.KadisonKastler.cyclicFactorLeft_apply _root_.OAI.KadisonKastler.cyclicFactorRepresentation_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonKastler.mem_centralVectorSpace _root_.OAI.KadisonKastler.regularCoreDualEquiv_apply _root_.OAI.KadisonKastler.regularCoreDualHom_apply _root_.OAI.KadisonKastler.tracialSequenceEquiv_coe _root_.OAI.KadisonKastler.typeICyclicHom_apply _root_.OAI.KadisonKastler.typeICyclicOperator_apply _root_.OAI.KadisonKastler.unitaryInAlgebra_coe _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Exact normalizers from the constructed frequency smoothing

All constants precede the Hilbert space and algebra. The previously
proved polar-path theorem is applied to the actual Poisson operators
at positive heights tending to zero.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

universe u

attribute [local instance] OAI.KadisonKastler.frequencyNormalizerOrder
attribute [local instance] OAI.KadisonKastler.frequencyNormalizerStarOrder
theorem uniform_typeIII_normalizer_from_frequency_smoothing_oai
    (hSpectral : PublishedVonNeumannSpectralCut.{u})
    (hCompare : PublishedTypeIIIProjectionComparison.{u})
    (hSakai : PublishedSimpleDerivationInner.{u})
    (hDistance : ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H], ∀ M : VonNeumannAlgebra H,
        PublishedBlockCommutantApproximation (Algebra M) H)
    (hHardy : PublishedHardyMultiplierEvaluation.{u}) :
    ∃ δ0 K : ℝ, 0 < δ0 ∧ 0 < K ∧
      ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        [CompleteSpace H] [Nontrivial H] [TopologicalSpace.SeparableSpace H],
      ∀ (M : VonNeumannAlgebra H), TypeIIIFactor M →
      ∀ (W : ℝ → unitary (H →L[ℂ] H)), W 0 = 1 →
      (∀ x, Continuous (fun t => (W t : H →L[ℂ] H) x)) →
      (∀ x, Continuous (fun t => star (W t : H →L[ℂ] H) x)) →
      (∀ t, PublishedMultiplicationCorrection (unitaryConjugateAlgebra (W t) M)) →
      ∀ δ : ℝ, 0 < δ → δ < δ0 →
      FrequencySmoothing (modulatedUnitaryField W) δ →
      FrequencySmoothing (modulatedUnitaryField (fun t => star (W t))) δ →
      (∀ t, kkDistance (unitaryConjugateAlgebra (W t) M) M < δ) →
      ∀ t, ∃ v : unitary (H →L[ℂ] H), Conjugates v M M ∧
        ‖(v : H →L[ℂ] H) - W t‖ ≤ K * δ := by
  obtain ⟨r0, C, hr0, hC, hnormal⟩ :=
    uniform_typeIII_normalizer_from_smoothing hSpectral hCompare hSakai hDistance
  refine ⟨min (1 / 16) (r0 / 12), 12 * C, lt_min (by norm_num) (by positivity),
    by positivity, ?_⟩
  intro H _ _ _ _ _ M hM W hW0 hW hWs hCorrection δ hδ hδ0 A B hgap t
  have hnear := infDist_modulated_sandwich_le M W hgap
  have hgapInv (s : ℝ) : kkDistance (unitaryConjugateAlgebra (star (W s)) M) M < δ := by
    rw [kkDistance_inverse_conjugate]
    exact hgap s
  have hnearInv := infDist_modulated_sandwich_le M (fun s => star (W s)) hgapInv
  have hδ16 : δ ≤ 1 / 16 := (hδ0.trans_le (min_le_left _ _)).le
  have hδ8 : δ ≤ 1 / 8 := hδ16.trans (by norm_num)
  have hRsmall : 12 * δ < r0 := by
    have h := hδ0.trans_le (min_le_right _ _)
    linarith
  let a (n : ℕ) (t : ℝ) := A.smooth t (smoothingHeight δ n) (smoothingHeight_pos hδ n)
  let c (n : ℕ) (t : ℝ) := B.smooth t (smoothingHeight δ n) (smoothingHeight_pos hδ n)
  let D (n : ℕ) (t : ℝ) := poissonBoundaryApprox W hW t (smoothingHeight δ n)
  have hF (x : H) : AEStronglyMeasurable (fun t => modulatedUnitaryField W t x) volume :=
    (modulatedUnitaryField_continuous W hW x).aestronglyMeasurable
  have hG (x : H) : AEStronglyMeasurable
      (fun t => modulatedUnitaryField (fun s => star (W s)) t x) volume :=
    (modulatedUnitaryField_continuous (fun s => star (W s)) hWs x).aestronglyMeasurable
  have hFn : ∀ᵐ s, ‖modulatedUnitaryField W s‖ ≤ 1 :=
    Filter.Eventually.of_forall (norm_modulatedUnitaryField_le_one W)
  have hGn : ∀ᵐ s, ‖modulatedUnitaryField (fun t => star (W t)) s‖ ≤ 1 :=
    Filter.Eventually.of_forall (norm_modulatedUnitaryField_le_one (fun t => star (W t)))
  have hFG : ∀ᵐ s, modulatedUnitaryField W s *
      modulatedUnitaryField (fun t => star (W t)) s = poissonCharacterField 2 s :=
    Filter.Eventually.of_forall (modulatedUnitaryField_mul_inverse W)
  have hGF : ∀ᵐ s, modulatedUnitaryField (fun t => star (W t)) s *
      modulatedUnitaryField W s = poissonCharacterField 2 s := by
    filter_upwards with s
    simpa only [star_star] using modulatedUnitaryField_mul_inverse (fun t => star (W t)) s
  have han (n : ℕ) (s : ℝ) : ‖a n s‖ ≤ 1 + 12 * δ :=
    (A.norm_smooth_le_one_add hδ.le hδ8 s _ (smoothingHeight_pos hδ n)
      (smoothingHeight_le hδ.le n)).trans (by linarith)
  have hcn (n : ℕ) (s : ℝ) : ‖c n s‖ ≤ 1 + 12 * δ :=
    (B.norm_smooth_le_one_add hδ.le hδ8 s _ (smoothingHeight_pos hδ n)
      (smoothingHeight_le hδ.le n)).trans (by linarith)
  have hac (n : ℕ) (s : ℝ) : ‖a n s * c n s - 1‖ ≤ 12 * δ :=
    A.norm_product_sub_one_le hHardy B hF hG hFn hGn hFG hδ.le hδ16 s _
      (smoothingHeight_pos hδ n) (smoothingHeight_le hδ.le n)
  have hca (n : ℕ) (s : ℝ) : ‖c n s * a n s - 1‖ ≤ 12 * δ :=
    B.norm_product_sub_one_le hHardy A hG hF hGn hFn hGF hδ.le hδ16 s _
      (smoothingHeight_pos hδ n) (smoothingHeight_le hδ.le n)
  have halg (n : ℕ) (s : ℝ) (x : H →L[ℂ] H) (hx : x ∈ unitBall M) :
      Metric.infDist (a n s * x * c n s) (M : Set (H →L[ℂ] H)) ≤ 12 * δ := by
    have h := A.infDist_smooth_sandwich_le hHardy M (hDistance H M.commutant) B
      hFn hGn hδ.le le_rfl hδ.le hδ16 x (Filter.Eventually.of_forall fun s => hnear s x hx.1)
      s _ (smoothingHeight_pos hδ n) (smoothingHeight_le hδ.le n)
    exact h.trans ((mul_le_mul_of_nonneg_left hx.2 (by positivity)).trans_eq (mul_one _))
  have hcalg (n : ℕ) (s : ℝ) (x : H →L[ℂ] H) (hx : x ∈ unitBall M) :
      Metric.infDist (c n s * x * a n s) (M : Set (H →L[ℂ] H)) ≤ 12 * δ := by
    have h := B.infDist_smooth_sandwich_le hHardy M (hDistance H M.commutant) A
      hGn hFn hδ.le le_rfl hδ.le hδ16 x (Filter.Eventually.of_forall fun s => by simpa only [star_star] using hnearInv s x hx.1)
      s _ (smoothingHeight_pos hδ n) (smoothingHeight_le hδ.le n)
    exact h.trans ((mul_le_mul_of_nonneg_left hx.2 (by positivity)).trans_eq (mul_one _))
  have hDn (n : ℕ) (s : ℝ) : ‖D n s‖ ≤ 2 :=
    norm_poissonBoundaryApprox_smoothingHeight_le_two W hW hδ hδ8 n s
  have haD (n : ℕ) (s : ℝ) : ‖a n s - D n s‖ ≤ 12 * δ :=
    (A.norm_smooth_sub_boundary_le_four W hW hδ.le hδ8 s _
      (smoothingHeight_pos hδ n) (smoothingHeight_le hδ.le n)).trans (by linarith)
  obtain ⟨v, hv, hvn⟩ := hnormal H M hM W hW0 hCorrection a c D (12 * δ)
    (by positivity) hRsmall (fun n => A.continuous_smooth hδ.le _ (smoothingHeight_pos hδ n))
    han hcn hac hca halg hcalg hDn haD
    (poissonBoundaryApprox_smoothingHeight_tendsto W hW δ)
    (poissonBoundaryApprox_star_smoothingHeight_tendsto W hW hWs δ)
    (fun s => (hgap s).trans (by linarith)) t
  refine ⟨v, hv, hvn.trans_eq ?_⟩
  ring

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.uniform_typeIII_normalizer_from_frequency_smoothing_oai.{u} := @OAI.KadisonKastler.uniform_typeIII_normalizer_from_frequency_smoothing_oai.{u}
