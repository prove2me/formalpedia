-- Prove2me | solution 1 for OAI.KadisonKastler.commonCenterSeparableStability_of_factors
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:14:32.421597+00:00
-- url     : https://prove2.me/submissions/9b83f62f-ecfe-4900-a960-ad65a8f156a9

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
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
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Combination
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
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
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
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
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
import Definitions.Def_Q260K028
import Theorems.Thm_OAI_KadisonKastler_exists_bounded_conjugacy_from_centralPair

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Basic
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem kkDistance_nonneg (M N : VonNeumannAlgebra H) : 0 ≤ kkDistance M N :=
  Metric.hausdorffDist_nonneg

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakCPLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Positivity and norm bounds in pointwise weak operator limits

These lemmas retain the complete positivity of the maps obtained from
finite Hilbert-space tests. No normality of the limiting map is needed.
-/

namespace KadisonKastler

open Filter
open scoped Topology CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} {l : Filter ι} [l.NeBot]

omit [CompleteSpace H] in
/-- A uniform operator norm bound survives a weak coefficient limit. -/
theorem norm_le_of_weak_limit {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] (T : ι → H →L[ℂ] K) (S : H →L[ℂ] K)
    {C : ℝ} (hC : 0 ≤ C) (hT : ∀ i, ‖T i‖ ≤ C)
    (ht : ∀ x y, Tendsto (fun i => inner ℂ y (T i x)) l (𝓝 (inner ℂ y (S x)))) :
    ‖S‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le hC
  intro x y hx hy
  change (inner ℂ (S x) y).re ≤ C
  have hb (i : ι) : (inner ℂ y (T i x)).re ≤ C := by
    calc
      _ ≤ ‖inner ℂ y (T i x)‖ := Complex.re_le_norm _
      _ ≤ ‖y‖ * ‖T i x‖ := norm_inner_le_norm _ _
      _ ≤ ‖y‖ * (C * ‖x‖) := mul_le_mul_of_nonneg_left
        ((T i).le_of_opNorm_le (hT i) x) (norm_nonneg y)
      _ = C := by rw [hx, hy]; ring
  have hr := (Complex.continuous_re.tendsto _).comp (ht x y)
  rw [show (inner ℂ (S x) y).re = (inner ℂ y (S x)).re from
    inner_re_symm (𝕜 := ℂ) (S x) y]
  exact le_of_tendsto hr (Eventually.of_forall hb)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_DenseUnitBallGap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Passing unit-ball approximation through weakly dense tests

A bounded target family has a weak operator ultralimit. The same
uniform approximation bound survives this limit, allowing bounds on
weakly dense unit-ball tests to control the full Kadison--Kastler gap.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A uniform approximation by the target unit ball survives an arbitrary
nontrivial coefficientwise convergent net. -/
theorem exists_unitBall_approx_of_weak_limit
    {ι : Type*} {l : Filter ι} [l.NeBot] (N : VonNeumannAlgebra H)
    (T : ι → H →L[ℂ] H) (a : H →L[ℂ] H)
    (hlim : ∀ x y, Tendsto (fun i => inner ℂ y (T i x)) l
      (𝓝 (inner ℂ y (a x))))
    {r : ℝ} (hr : 0 ≤ r)
    (hnear : ∀ i, ∃ b ∈ unitBall N, ‖T i - b‖ ≤ r) :
    ∃ b ∈ unitBall N, ‖a - b‖ ≤ r := by
  choose b hb hdist using hnear
  let ω : Ultrafilter ι := Ultrafilter.of l
  have hω : (ω : Filter ι) ≤ l := Ultrafilter.of_le l
  obtain ⟨c, hcn, hc⟩ := Generator.Tracial.exists_weak_operator_ultralimit ω b 1
    zero_le_one (fun i => (hb i).2)
  have hcN : c ∈ N := Generator.Tracial.weak_operator_limit_mem N
    (fun i => ⟨b i, (hb i).1⟩) c hc
  refine ⟨c, ⟨hcN, hcn⟩, ?_⟩
  apply norm_le_of_weak_limit (l := (ω : Filter ι)) (fun i => T i - b i) (a - c) hr hdist
  intro x y
  simpa only [sub_apply, inner_sub_right] using
    ((hlim x y).mono_left hω).sub (hc x y)

theorem exists_unitBall_approx_of_weakly_dense_tests
    {ι : Type*} {M N : VonNeumannAlgebra H} (T : ι → H →L[ℂ] H)
    (hT : WeakUnitBallDense T M) {r : ℝ} (hr : 0 ≤ r)
    (hnear : ∀ i, ∃ b ∈ unitBall N, ‖T i - b‖ ≤ r)
    (a : H →L[ℂ] H) (ha : a ∈ unitBall M) :
    ∃ b ∈ unitBall N, ‖a - b‖ ≤ r := by
  obtain ⟨l, hl, hlim⟩ := hT.2 a ha
  let : l.NeBot := hl
  exact exists_unitBall_approx_of_weak_limit N T a hlim hr hnear

/-- Two weakly dense test families suffice to bound the full gap. -/
theorem kkDistance_le_of_weakly_dense_tests
    {ι κ : Type*} (M N : VonNeumannAlgebra H)
    (T : ι → H →L[ℂ] H) (S : κ → H →L[ℂ] H)
    (hT : WeakUnitBallDense T M) (hS : WeakUnitBallDense S N)
    {r : ℝ} (hr : 0 ≤ r)
    (hTN : ∀ i, ∃ b ∈ unitBall N, ‖T i - b‖ ≤ r)
    (hSM : ∀ j, ∃ a ∈ unitBall M, ‖S j - a‖ ≤ r) :
    kkDistance M N ≤ r := by
  apply Metric.hausdorffDist_le_of_mem_dist hr
  · intro a ha
    obtain ⟨b, hb, hab⟩ := exists_unitBall_approx_of_weakly_dense_tests T hT hr hTN a ha
    exact ⟨b, hb, by simpa only [dist_eq_norm] using hab⟩
  · intro b hb
    obtain ⟨a, ha, hba⟩ := exists_unitBall_approx_of_weakly_dense_tests S hS hr hSM b hb
    exact ⟨a, ha, by simpa only [dist_eq_norm] using hba⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedKaplansky
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The published bounded-density input

Irving Kaplansky, *A theorem on rings of operators*, Pacific Journal of
Mathematics 1 (1951), 227--232, Theorem 1, p. 227:
https://msp.org/pjm/1951/1-2/pjm-v1-n2-p06-s.pdf

The paper's terminology "unit sphere" is the closed unit ball, as the
norm bounds in the proof on pp. 228 and 230--231 explicitly show.
The input below is its finite-strong-neighborhood specialization to a
unital star algebra and its bicommutant. The already proved double
commutant theorem supplies the required strong density. No statement
comparing two algebras or their Kadison--Kastler distances is assumed.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The contractive elements of the original algebra give a concrete weakly
dense test family in its generated von Neumann algebra. -/
theorem PublishedKaplanskyDensity.weakUnitBallDense
    (hK : PublishedKaplanskyDensity.{u})
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    WeakUnitBallDense (fun a : {a : A // ‖a‖ ≤ 1} => (a.val : H →L[ℂ] H))
      (generatedVonNeumannAlgebra A) := by
  classical
  constructor
  · intro a
    exact ⟨subset_generatedVonNeumannAlgebra A a.val.property, a.property⟩
  · intro T hT
    have hm : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))) := by
      have hm' : T ∈ (generatedVonNeumannAlgebra A : Set (H →L[ℂ] H)) := hT.1
      rwa [generatedVonNeumannAlgebra_coe] at hm'
    obtain ⟨a, ha, hlim⟩ := hK.exists_weak_contraction_net A T hm hT.2
    let b : Finset H × ℕ → {a : A // ‖a‖ ≤ 1} := fun d => ⟨a d, ha d⟩
    have hne : (atTop : Filter (Finset H × ℕ)).NeBot := inferInstance
    refine ⟨Filter.map b (atTop : Filter (Finset H × ℕ)), hne.map b, ?_⟩
    intro x y
    apply Filter.tendsto_map'_iff.mpr
    exact hlim x y

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UnitBallClosure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Unit balls in norm closures of complex linear subspaces

Radial contraction keeps approximants in their original subspace. It
proves the norm-density statement needed for the separable test algebras.
-/

namespace KadisonKastler

noncomputable section

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B]

theorem unitBallClip_norm_le (x : B) : ‖unitBallClip x‖ ≤ 1 := by
  have hp : 0 < max 1 ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [unitBallClip, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hp.le), inv_mul_eq_div]
  exact (div_le_one hp).mpr (le_max_right _ _)

theorem unitBallClip_eq_self {x : B} (hx : ‖x‖ ≤ 1) : unitBallClip x = x := by
  simp only [unitBallClip, max_eq_left hx, inv_one, Complex.ofReal_one, one_smul]

theorem continuous_unitBallClip : Continuous (unitBallClip : B → B) := by
  have hc : Continuous (fun x : B => (max 1 ‖x‖)⁻¹) :=
    (continuous_const.max continuous_norm).inv₀ (fun x => by
      have h : 0 < max 1 ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      exact ne_of_gt h)
  exact (Complex.continuous_ofReal.comp hc).smul continuous_id

theorem unitBallClip_mem (S : Submodule ℂ B) {x : B} (hx : x ∈ S) :
    unitBallClip x ∈ S := S.smul_mem _ hx

/-- The unit ball of a linear subspace is norm dense in the unit ball of
its closure, even when the subspace is not closed. -/
theorem closure_submodule_unitBall (S : Submodule ℂ B) :
    closure {x : B | x ∈ S ∧ ‖x‖ ≤ 1} =
      {x : B | x ∈ closure (S : Set B) ∧ ‖x‖ ≤ 1} := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · intro x hx
      exact ⟨subset_closure hx.1, hx.2⟩
    · exact isClosed_closure.inter (isClosed_le continuous_norm continuous_const)
  · intro x hx
    have hclip := mem_closure_image continuous_unitBallClip.continuousAt hx.1
    rw [unitBallClip_eq_self hx.2] at hclip
    apply closure_mono _ hclip
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨unitBallClip_mem S hy, unitBallClip_norm_le y⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SeparableAlgebraPair
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Nearby separable test algebras

Countably many generators are enlarged alternately by nearby contractions.
The increasing norm closures give the two separable C*-algebras in §9.
All choices and closure estimates are constructed here; there is no
separable-reduction hypothesis.
-/

namespace KadisonKastler

open TopologicalSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem zero_mem_starAlgebraBall (A : StarSubalgebra ℂ (H →L[ℂ] H)) :
    0 ∈ starAlgebraBall A := ⟨A.zero_mem, by simp⟩

theorem cstarHull_mono : Monotone (cstarHull (H := H)) :=
  fun _ _ h => StarSubalgebra.topologicalClosure_mono (StarAlgebra.adjoin_mono h)

theorem SeparableSeeds.next_spec {M N : VonNeumannAlgebra H}
    (p : SeparableSeeds M N) {r : ℝ} (hr : kkDistance M N < r) :
    p.Extends (p.next hr) r := Classical.choose_spec (p.exists_extension hr)

theorem SeparableSeeds.stages_left_mono {M N : VonNeumannAlgebra H}
    (p : SeparableSeeds M N) {r : ℝ} (hr : kkDistance M N < r) :
    Monotone (fun n => (p.stages hr n).left) :=
  monotone_nat_of_le_succ (fun n => ((p.stages hr n).next_spec hr).1)

theorem SeparableSeeds.stages_right_mono {M N : VonNeumannAlgebra H}
    (p : SeparableSeeds M N) {r : ℝ} (hr : kkDistance M N < r) :
    Monotone (fun n => (p.stages hr n).right) :=
  monotone_nat_of_le_succ (fun n => ((p.stages hr n).next_spec hr).2.1)

theorem le_increasingCstarClosure (A : ℕ → StarSubalgebra ℂ (H →L[ℂ] H)) (n : ℕ) :
    A n ≤ increasingCstarClosure A :=
  (le_iSup A n).trans (StarSubalgebra.le_topologicalClosure _)

theorem isSeparable_increasingCstarClosure
    (A : ℕ → StarSubalgebra ℂ (H →L[ℂ] H)) (hA : Monotone A)
    (hsep : ∀ n, IsSeparable (A n : Set (H →L[ℂ] H))) :
    IsSeparable (increasingCstarClosure A : Set (H →L[ℂ] H)) := by
  apply IsSeparable.closure
  rw [StarSubalgebra.coe_iSup_of_directed hA.directed_le]
  exact IsSeparable.iUnion hsep

theorem infDist_increasingCstarClosure_ball
    (A : ℕ → StarSubalgebra ℂ (H →L[ℂ] H)) (hA : Monotone A)
    (t : Set (H →L[ℂ] H)) {r : ℝ}
    (hnear : ∀ n, ∀ x ∈ starAlgebraBall (A n), Metric.infDist x t ≤ r) :
    ∀ x ∈ starAlgebraBall (increasingCstarClosure A), Metric.infDist x t ≤ r := by
  intro x hx
  apply infDist_le_of_mem_closure (s := starAlgebraBall (iSup A)) ?_ ?_
  · intro y hy
    have hymem : y ∈ ⋃ n, (A n : Set (H →L[ℂ] H)) := by
      rw [← StarSubalgebra.coe_iSup_of_directed hA.directed_le]
      exact hy.1
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hymem
    exact hnear n y ⟨hn, hy.2⟩
  · change x ∈ closure {y | y ∈ (iSup A).toSubalgebra.toSubmodule ∧ ‖y‖ ≤ 1}
    rw [closure_submodule_unitBall]
    exact hx

/-- The alternating countable construction produces nearby closed separable
test algebras containing any prescribed finite operator tests. -/
theorem exists_near_separable_algebra_pair_countable (M N : VonNeumannAlgebra H)
    (E F : Set (H →L[ℂ] H)) (hEc : E.Countable) (hFc : F.Countable)
    (hE : ∀ x ∈ E, x ∈ M) (hF : ∀ x ∈ F, x ∈ N)
    {g : ℝ} (hg : kkDistance M N < g) :
    ∃ A B : StarSubalgebra ℂ (H →L[ℂ] H),
      IsClosed (A : Set (H →L[ℂ] H)) ∧ IsClosed (B : Set (H →L[ℂ] H)) ∧
      IsSeparable (A : Set (H →L[ℂ] H)) ∧ IsSeparable (B : Set (H →L[ℂ] H)) ∧
      A ≤ M.toStarSubalgebra ∧ B ≤ N.toStarSubalgebra ∧
      (∀ x ∈ E, x ∈ A) ∧ (∀ x ∈ F, x ∈ B) ∧
      Metric.hausdorffDist (starAlgebraBall A) (starAlgebraBall B) < g := by
  obtain ⟨r, hr, hrg⟩ := exists_between hg
  let p : SeparableSeeds M N :=
    ⟨E, F, hEc, hFc, hE, hF⟩
  let A (n : ℕ) := cstarHull (p.stages hr n).left
  let B (n : ℕ) := cstarHull (p.stages hr n).right
  have hA : Monotone A := cstarHull_mono.comp (p.stages_left_mono hr)
  have hB : Monotone B := cstarHull_mono.comp (p.stages_right_mono hr)
  have hAM : increasingCstarClosure A ≤ M.toStarSubalgebra :=
    StarSubalgebra.topologicalClosure_minimal
      (iSup_le fun n => cstarHull_le M (p.stages hr n).left_mem) (isClosed_algebra M)
  have hBN : increasingCstarClosure B ≤ N.toStarSubalgebra :=
    StarSubalgebra.topologicalClosure_minimal
      (iSup_le fun n => cstarHull_le N (p.stages hr n).right_mem) (isClosed_algebra N)
  refine ⟨increasingCstarClosure A, increasingCstarClosure B,
    StarSubalgebra.isClosed_topologicalClosure _, StarSubalgebra.isClosed_topologicalClosure _,
    isSeparable_increasingCstarClosure A hA
      (fun n => isSeparable_cstarHull (p.stages hr n).left_countable),
    isSeparable_increasingCstarClosure B hB
      (fun n => isSeparable_cstarHull (p.stages hr n).right_countable),
    hAM, hBN, ?_, ?_, ?_⟩
  · intro x hx
    exact le_increasingCstarClosure A 0 (subset_cstarHull p.left hx)
  · intro x hx
    exact le_increasingCstarClosure B 0 (subset_cstarHull p.right hx)
  · apply lt_of_le_of_lt (Metric.hausdorffDist_le_of_infDist
      ((kkDistance_nonneg M N).trans hr.le) ?_ ?_) hrg
    · apply infDist_increasingCstarClosure_ball A hA
      intro n x hx
      have hnext := ((p.stages hr n).next_spec hr).2.2.1 x hx
      apply le_trans (Metric.infDist_le_infDist_of_subset (t :=
        starAlgebraBall (increasingCstarClosure B)) ?_
        ⟨0, zero_mem_starAlgebraBall _⟩) hnext
      intro y hy
      exact ⟨le_increasingCstarClosure B (n + 1) hy.1, hy.2⟩
    · apply infDist_increasingCstarClosure_ball B hB
      intro n x hx
      have hnext := ((p.stages hr n).next_spec hr).2.2.2 x hx
      apply le_trans (Metric.infDist_le_infDist_of_subset (t :=
        starAlgebraBall (increasingCstarClosure A)) ?_
        ⟨0, zero_mem_starAlgebraBall _⟩) hnext
      intro y hy
      exact ⟨le_increasingCstarClosure A (n + 1) hy.1, hy.2⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SeparableTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Common separable reducing spaces for nearby test algebras

The countable dense generators of both algebras generate one separable
ambient C*-algebra. Its finite-vector orbit supplies the common reducing
space, including when the original Hilbert space is not separable.
-/

namespace KadisonKastler

open TopologicalSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_separable_common_superalgebra
    (A B : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : IsSeparable (A : Set (H →L[ℂ] H)))
    (hB : IsSeparable (B : Set (H →L[ℂ] H))) :
    ∃ C : StarSubalgebra ℂ (H →L[ℂ] H),
      IsSeparable (C : Set (H →L[ℂ] H)) ∧ A ≤ C ∧ B ≤ C := by
  obtain ⟨s, hsA, hsc, hAs⟩ := hA.exists_countable_dense_subset
  obtain ⟨t, htB, htc, hBt⟩ := hB.exists_countable_dense_subset
  refine ⟨cstarHull (s ∪ t), isSeparable_cstarHull (hsc.union htc), ?_, ?_⟩
  · exact hAs.trans (closure_minimal
      (Set.subset_union_left.trans (subset_cstarHull (s ∪ t)))
      (StarSubalgebra.isClosed_topologicalClosure _))
  · exact hBt.trans (closure_minimal
      (Set.subset_union_right.trans (subset_cstarHull (s ∪ t)))
      (StarSubalgebra.isClosed_topologicalClosure _))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StrongCommutantTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-- d13f23b's `TopologicalSpace.exists_countable_dense_subset` (port compat, absent from our Mathlib). -/
private theorem ecdsCompat_p1 {α : Type*} [TopologicalSpace α] (s : Set α) [TopologicalSpace.SeparableSpace s] :
    ∃ t : Set α, t.Countable ∧ t ⊆ s ∧ s ⊆ closure t := by
  obtain ⟨t, ct, dt⟩ := TopologicalSpace.exists_countable_dense s
  exact ⟨Subtype.val '' t, ct.image _, by simp, fun x hx ↦ closure_subtype.1 (dt ⟨x, hx⟩)⟩

/-! # Countable strong-operator tests for commutation

On a uniformly bounded set of operators, convergence on a countable dense
set of vectors implies convergence on every vector. A countable dense set
of coordinate sequences therefore supplies all commutant tests.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Every contraction-valued set on a separable space has a countable
subset that approximates each of its elements strongly by a sequence. -/
theorem exists_countable_strong_dense_contractions [SeparableSpace H]
    (S : Set (H →L[ℂ] H)) (hS : ∀ T ∈ S, ‖T‖ ≤ 1) :
    ∃ E : Set (H →L[ℂ] H), E.Countable ∧ E ⊆ S ∧
      ∀ T ∈ S, ∃ A : ℕ → H →L[ℂ] H,
        (∀ n, A n ∈ E) ∧ ∀ ξ, Tendsto (fun n => A n ξ) atTop (𝓝 (T ξ)) := by
  obtain ⟨v, hv⟩ := exists_dense_seq (α := H)
  let coordinates : (H →L[ℂ] H) → ℕ → H := fun A n => A (v n)
  obtain ⟨D, hDc, hDsub, hDdense⟩ := ecdsCompat_p1 (coordinates '' S)
  choose lift hliftS hlift using fun z : D => hDsub z.property
  let E : Set (H →L[ℂ] H) := Set.range lift
  have hEc : E.Countable := by
    let := hDc.to_subtype
    exact Set.countable_range lift
  have hES : E ⊆ S := by
    rintro T ⟨z, rfl⟩
    exact hliftS z
  refine ⟨E, hEc, hES, ?_⟩
  intro T hT
  obtain ⟨z, hz, hzt⟩ := mem_closure_iff_seq_limit.mp (hDdense ⟨T, hT, rfl⟩)
  let A : ℕ → H →L[ℂ] H := fun n => lift ⟨z n, hz n⟩
  have hAE (n : ℕ) : A n ∈ E := ⟨⟨z n, hz n⟩, rfl⟩
  refine ⟨A, hAE, ?_⟩
  apply tendsto_apply_of_dense_contractions v hv A T
    (fun n => hS (A n) (hES (hAE n))) (hS T hT)
  intro j
  have ht := tendsto_pi_nhds.mp hzt j
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  exact congrFun (hlift ⟨z n, hz n⟩) j

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CountableConjugacyTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Countable tests for the implementer relation

Strongly dense contraction families determine both inclusions of a
unitary conjugacy. This is the algebraic equivalence used when forming
the measurable implementer relation in the central decomposition.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem unitBall_subset_algebra_iff (M N : VonNeumannAlgebra H) :
    unitBall M ⊆ N ↔ M ≤ N := by
  constructor
  · intro h x hx
    have hclip : unitBallClip x ∈ N :=
      h ⟨unitBallClip_mem M.toStarSubalgebra.toSubalgebra.toSubmodule hx,
        unitBallClip_norm_le x⟩
    have hp : 0 < max 1 ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have heq : ((max 1 ‖x‖ : ℝ) : ℂ) • unitBallClip x = x := by
      rw [unitBallClip, smul_smul]
      have hn : ((max 1 ‖x‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
      simp only [Complex.ofReal_inv, mul_inv_cancel₀ hn, one_smul]
    rw [← heq]
    exact N.toStarSubalgebra.smul_mem hclip _
  · exact fun h _ hx => h hx.1

theorem unitaryConj_mem_of_strong_tests (N : VonNeumannAlgebra H)
    (v : unitary (H →L[ℂ] H)) (T : ℕ → H →L[ℂ] H) (x : H →L[ℂ] H)
    (hlim : ∀ ξ, Tendsto (fun n => T n ξ) atTop (𝓝 (x ξ)))
    (hT : ∀ n, unitaryConj v (T n) ∈ N) : unitaryConj v x ∈ N := by
  let b (n : ℕ) : Algebra N := ⟨unitaryConj v (T n), hT n⟩
  apply Generator.Tracial.weak_operator_limit_mem (l := atTop) N b (unitaryConj v x)
  intro ξ η
  have h := ((v : H →L[ℂ] H).continuous.tendsto _).comp
    (hlim (star (v : H →L[ℂ] H) ξ))
  have h' : Tendsto
      (fun n => inner ℂ η ((v : H →L[ℂ] H) (T n (star (v : H →L[ℂ] H) ξ)))) atTop
      (𝓝 (inner ℂ η ((v : H →L[ℂ] H) (x (star (v : H →L[ℂ] H) ξ))))) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => η) atTop (𝓝 η)).inner (𝕜 := ℂ) h
  simpa only [b, unitaryConj, mul_apply_eq_comp] using h'

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_SequentialConjugacyTests
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Sequential tests for the measurable conjugacy relation

Each represented algebra on a separable Hilbert space has an actual
sequence of contractions whose range is strongly dense in its unit ball.
Conjugacy is exactly two countable families of finite-vector tests.
-/

namespace KadisonKastler

open Filter TopologicalSpace
open scoped Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_strongUnitBallTestSequence [SeparableSpace H] (M : VonNeumannAlgebra H) :
    Nonempty (StrongUnitBallTestSequence M) := by
  obtain ⟨E, hEc, hEM, hE⟩ := exists_countable_strong_dense_contractions
    (unitBall M) (fun _ hx => hx.2)
  obtain ⟨T, hTE, _⟩ := hE 0 (zero_mem_unitBall M)
  obtain ⟨a, ha⟩ := hEc.exists_eq_range ⟨T 0, hTE 0⟩
  refine ⟨⟨a, fun n => hEM (ha.symm ▸ Set.mem_range_self n), ?_⟩⟩
  intro x hx
  obtain ⟨S, hSE, hlim⟩ := hE x hx
  exact ⟨S, fun n => ha ▸ hSE n, hlim⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_NearSeparableGenerators
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.PopaCorner.instOne _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Nearby separable C-star algebras generating the original pair

In a separable representation, the alternating construction can retain
countable strong generators of both original algebras. This supplies
the norm-separable algebras needed for simultaneous fiber representations.
-/

namespace KadisonKastler

open TopologicalSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem generated_eq_of_strong_tests (M : VonNeumannAlgebra H)
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (hAM : A ≤ M.toStarSubalgebra)
    (s : StrongUnitBallTestSequence M) (hs : ∀ j, s.op j ∈ A) :
    generatedVonNeumannAlgebra A = M := by
  apply le_antisymm
  · intro T hT
    have h : Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))) ⊆
        Set.centralizer (Set.centralizer (M : Set (H →L[ℂ] H))) :=
      Set.centralizer_subset (Set.centralizer_subset hAM)
    have ht : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))) := by
      change T ∈ (generatedVonNeumannAlgebra A : Set (H →L[ℂ] H)) at hT
      rwa [generatedVonNeumannAlgebra_coe] at hT
    rw [M.centralizer_centralizer] at h
    exact h ht
  · apply (unitBall_subset_algebra_iff _ _).mp
    intro T hT
    change T ∈ generatedVonNeumannAlgebra A
    obtain ⟨S, hS, hlim⟩ := s.dense T hT
    have hm (j : ℕ) : S j ∈ generatedVonNeumannAlgebra A := by
      obtain ⟨k, hk⟩ := hS j
      rw [← hk]
      exact subset_generatedVonNeumannAlgebra A (hs k)
    simpa only [unitaryConj_one] using
      unitaryConj_mem_of_strong_tests (generatedVonNeumannAlgebra A) 1 S T hlim
        (fun j => by simpa only [unitaryConj_one] using hm j)

theorem exists_near_separable_generators [SeparableSpace H]
    (M N : VonNeumannAlgebra H) {g : ℝ} (hg : kkDistance M N < g) :
    ∃ A B : StarSubalgebra ℂ (H →L[ℂ] H),
      IsClosed (A : Set (H →L[ℂ] H)) ∧ IsClosed (B : Set (H →L[ℂ] H)) ∧
      IsSeparable (A : Set (H →L[ℂ] H)) ∧ IsSeparable (B : Set (H →L[ℂ] H)) ∧
      generatedVonNeumannAlgebra A = M ∧ generatedVonNeumannAlgebra B = N ∧
      Metric.hausdorffDist (starAlgebraBall A) (starAlgebraBall B) < g := by
  obtain ⟨s⟩ := exists_strongUnitBallTestSequence M
  obtain ⟨t⟩ := exists_strongUnitBallTestSequence N
  obtain ⟨A, B, hAc, hBc, hAs, hBs, hAM, hBN, hsA, htB, hd⟩ :=
    exists_near_separable_algebra_pair_countable M N (Set.range s.op) (Set.range t.op)
      (Set.countable_range _) (Set.countable_range _)
      (by rintro _ ⟨j, rfl⟩; exact (s.mem j).1)
      (by rintro _ ⟨j, rfl⟩; exact (t.mem j).1) hg
  exact ⟨A, B, hAc, hBc, hAs, hBs,
    generated_eq_of_strong_tests M A hAM s (fun j => hsA _ ⟨j, rfl⟩),
    generated_eq_of_strong_tests N B hBN t (fun j => htB _ ⟨j, rfl⟩), hd⟩

theorem exists_closed_separable_common_superalgebra
    (A B : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : IsSeparable (A : Set (H →L[ℂ] H)))
    (hB : IsSeparable (B : Set (H →L[ℂ] H))) :
    ∃ C : StarSubalgebra ℂ (H →L[ℂ] H),
      IsClosed (C : Set (H →L[ℂ] H)) ∧ IsSeparable (C : Set (H →L[ℂ] H)) ∧
      A ≤ C ∧ B ≤ C := by
  obtain ⟨C, hCs, hAC, hBC⟩ := exists_separable_common_superalgebra A B hA hB
  exact ⟨C.topologicalClosure, StarSubalgebra.isClosed_topologicalClosure C, hCs.closure,
    hAC.trans C.le_topologicalClosure, hBC.trans C.le_topologicalClosure⟩

/-- The common separable algebra can be chosen inside any common ambient
von Neumann algebra, in particular inside the common central commutant. -/
theorem exists_closed_separable_common_superalgebra_in
    (A B : StarSubalgebra ℂ (H →L[ℂ] H)) (D : VonNeumannAlgebra H)
    (hA : IsSeparable (A : Set (H →L[ℂ] H)))
    (hB : IsSeparable (B : Set (H →L[ℂ] H)))
    (hAD : A ≤ D.toStarSubalgebra) (hBD : B ≤ D.toStarSubalgebra) :
    ∃ C : StarSubalgebra ℂ (H →L[ℂ] H),
      IsClosed (C : Set (H →L[ℂ] H)) ∧ IsSeparable (C : Set (H →L[ℂ] H)) ∧
      A ≤ C ∧ B ≤ C ∧ C ≤ D.toStarSubalgebra := by
  obtain ⟨C, hCc, hCs, hAC, hBC⟩ :=
    exists_closed_separable_common_superalgebra A B hA hB
  refine ⟨C ⊓ D.toStarSubalgebra, ?_, hCs.mono (fun _ h => h.1),
    (fun _ h => ⟨hAC h, hAD h⟩), (fun _ h => ⟨hBC h, hBD h⟩), inf_le_right⟩
  exact hCc.inter (isClosed_algebra D)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RestrictionGap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The ordinary gap decreases under a common reducing restriction

Exact contraction lifts through the two restriction homomorphisms avoid
any faithfulness assumption and lose no radius in the gap estimate.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (K : Submodule ℂ H) [CompleteSpace K]
  (A B : StarSubalgebra ℂ (H →L[ℂ] H))
  (hA : ∀ a : A, ∀ x ∈ K, (a : H →L[ℂ] H) x ∈ K)
  (hB : ∀ b : B, ∀ x ∈ K, (b : H →L[ℂ] H) x ∈ K)

theorem starAlgebraBall_hausdorffEDist_ne_top :
    Metric.hausdorffEDist (starAlgebraBall A) (starAlgebraBall B) ≠ ⊤ :=
  Metric.hausdorffEDist_ne_top_of_nonempty_of_bounded
    ⟨0, zero_mem_starAlgebraBall A⟩ ⟨0, zero_mem_starAlgebraBall B⟩
    (isBounded_iff_forall_norm_le.mpr ⟨1, fun _ hx => hx.2⟩)
    (isBounded_iff_forall_norm_le.mpr ⟨1, fun _ hx => hx.2⟩)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GeneratedAlgebraGap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Gap control under generation and reducing restriction

Kaplansky density supplies bounded test nets. The already constructed
weak-operator limits pass the two near inclusions to the generated
von Neumann algebras without loss in the ordinary gap.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem kkDistance_generated_le (hK : PublishedKaplanskyDensity.{u})
    (A B : StarSubalgebra ℂ (H →L[ℂ] H)) :
    kkDistance (generatedVonNeumannAlgebra A) (generatedVonNeumannAlgebra B) ≤
      Metric.hausdorffDist (starAlgebraBall A) (starAlgebraBall B) := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  apply kkDistance_le_of_weakly_dense_tests _ _ _ _
    (hK.weakUnitBallDense A) (hK.weakUnitBallDense B)
    (Metric.hausdorffDist_nonneg.trans hr.le)
  · intro a
    obtain ⟨b, hb, hab⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt
      (show a.val.val ∈ starAlgebraBall A from ⟨a.val.property, a.property⟩)
      hr (starAlgebraBall_hausdorffEDist_ne_top A B)
    exact ⟨b, ⟨subset_generatedVonNeumannAlgebra B hb.1, hb.2⟩,
      by simpa only [dist_eq_norm] using hab.le⟩
  · intro b
    obtain ⟨a, ha, hba⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt
      (show b.val.val ∈ starAlgebraBall B from ⟨b.val.property, b.property⟩)
      (show Metric.hausdorffDist (starAlgebraBall B) (starAlgebraBall A) < r by
        simpa only [Metric.hausdorffDist_comm] using hr)
      (starAlgebraBall_hausdorffEDist_ne_top B A)
    exact ⟨a, ⟨subset_generatedVonNeumannAlgebra A ha.1, ha.2⟩,
      by simpa only [dist_eq_norm] using hba.le⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonRepresentationGap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The fiber gap from nearby norm-separable test algebras

The common representation is contractive even when it is not faithful.
Exact contraction lifting to each source algebra then preserves their
ordinary gap. Kaplansky density passes the estimate to the fiber algebras.
-/

namespace KadisonKastler

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem commonRepresentation_unitBall_approx
    (A B C : StarSubalgebra ℂ (H →L[ℂ] H))
    (hAc : IsClosed (A : Set (H →L[ℂ] H)))
    (hBc : IsClosed (B : Set (H →L[ℂ] H)))
    (hCc : IsClosed (C : Set (H →L[ℂ] H)))
    (hAC : A ≤ C) (hBC : B ≤ C) (φ : C →⋆ₐ[ℂ] (K →L[ℂ] K))
    {r : ℝ} (hr : Metric.hausdorffDist (starAlgebraBall A) (starAlgebraBall B) < r)
    {T : K →L[ℂ] K}
    (hT : T ∈ starAlgebraBall (φ.comp (StarSubalgebra.inclusion hAC)).range) :
    ∃ S ∈ starAlgebraBall (φ.comp (StarSubalgebra.inclusion hBC)).range, ‖T - S‖ < r := by
  let := StarSubalgebra.cstarAlgebra A (h_closed := hAc)
  let := StarSubalgebra.cstarAlgebra B (h_closed := hBc)
  let := StarSubalgebra.cstarAlgebra C (h_closed := hCc)
  let φA := φ.comp (StarSubalgebra.inclusion hAC)
  let φB := φ.comp (StarSubalgebra.inclusion hBC)
  obtain ⟨a, han, haT⟩ := exists_contractive_starAlgHom_preimage φA hT.1 hT.2
  obtain ⟨b, hb, hab⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt
    (show (a : H →L[ℂ] H) ∈ starAlgebraBall A from ⟨a.property, han⟩)
    hr (starAlgebraBall_hausdorffEDist_ne_top A B)
  let b' : B := ⟨b, hb.1⟩
  refine ⟨φB b', ⟨⟨b', rfl⟩,
    (NonUnitalStarAlgHom.norm_apply_le φB b').trans hb.2⟩, ?_⟩
  rw [← haT]
  have hnorm : ‖φA a - φB b'‖ ≤ ‖(a : H →L[ℂ] H) - b‖ := by
    change ‖φ (StarSubalgebra.inclusion hAC a) - φ (StarSubalgebra.inclusion hBC b')‖ ≤ _
    rw [← map_sub]
    exact NonUnitalStarAlgHom.norm_apply_le φ _
  exact hnorm.trans_lt (by simpa only [dist_eq_norm] using hab)

theorem kkDistance_commonRepresentation_le (hK : PublishedKaplanskyDensity.{v})
    (A B C : StarSubalgebra ℂ (H →L[ℂ] H))
    (hAc : IsClosed (A : Set (H →L[ℂ] H)))
    (hBc : IsClosed (B : Set (H →L[ℂ] H)))
    (hCc : IsClosed (C : Set (H →L[ℂ] H)))
    (hAC : A ≤ C) (hBC : B ≤ C) (φ : C →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    kkDistance (generatedVonNeumannAlgebra (φ.comp (StarSubalgebra.inclusion hAC)).range)
      (generatedVonNeumannAlgebra (φ.comp (StarSubalgebra.inclusion hBC)).range) ≤
        Metric.hausdorffDist (starAlgebraBall A) (starAlgebraBall B) := by
  apply (kkDistance_generated_le hK _ _).trans
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  apply Metric.hausdorffDist_le_of_mem_dist (Metric.hausdorffDist_nonneg.trans hr.le)
  · intro T hT
    obtain ⟨S, hS, hTS⟩ := commonRepresentation_unitBall_approx A B C hAc hBc hCc hAC hBC φ hr hT
    exact ⟨S, hS, by simpa only [dist_eq_norm] using hTS.le⟩
  · intro S hS
    obtain ⟨T, hT, hST⟩ := commonRepresentation_unitBall_approx B A C hBc hAc hCc hBC hAC φ
      (by simpa only [Metric.hausdorffDist_comm] using hr) hS
    exact ⟨T, hT, by simpa only [dist_eq_norm] using hST.le⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CommonCenterFromFactors
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.normUltraproductCStarAlgebra _root_.OAI.KadisonKastler.normUltraproductNontrivial _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonKastler.spatialHilbert_separable _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.tracialSequenceQuotientNontrivial _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.scalarHilbertCoordinates_separable _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The common-center reduction to the uniform factor theorem

Uniform stability of factors passes to algebras with a common center
by constructing nearby separable test algebras, bounding their fibers,
and assembling the factor implementers.
-/

namespace KadisonKastler

open MeasureTheory TopologicalSpace

noncomputable section

universe u

local instance instPartialOrderSubtypeContinuousLinearMapComplexIdMemStarSubalgebraAlgebra_3_r5f8a4e_1 {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : VonNeumannAlgebra H) : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance instStarOrderedRingSubtypeContinuousLinearMapComplexIdMemStarSubalgebraAlgebra_3_r5f8a4e_1 {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (M : VonNeumannAlgebra H) : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
theorem commonCenterSeparableStability_of_factors_oai
    (hFactor : UniformFactorStability.{u})
    (hCentral : PublishedCentralPairDecomposition.{u})
    (hK : PublishedKaplanskyDensity.{u})
    (hSelect : PublishedUnitaryBorelSelection.{u, u}) :
    CommonCenterSeparableStability.{u} := by
  intro a ha
  obtain ⟨τ, hτ, hlocal⟩ := hFactor (a / 2) (by positivity)
  refine ⟨τ / 2, by positivity, ?_⟩
  intro H _ _ _ _ M N hcenter hgap
  obtain ⟨A, B, hAc, hBc, hAs, hBs, hAM, hBN, hAB⟩ :=
    exists_near_separable_generators M N hgap
  have hMD : M.toStarSubalgebra ≤ (concreteCenter M).commutant.toStarSubalgebra := by
    intro T hT
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro z hz
    exact ((VonNeumannAlgebra.mem_commutant_iff.mp hz.2) T hT).symm
  have hND : N.toStarSubalgebra ≤ (concreteCenter M).commutant.toStarSubalgebra := by
    rw [hcenter]
    intro T hT
    apply VonNeumannAlgebra.mem_commutant_iff.mpr
    intro z hz
    exact ((VonNeumannAlgebra.mem_commutant_iff.mp hz.2) T hT).symm
  have hAD : A ≤ (concreteCenter M).commutant.toStarSubalgebra := by
    intro T hT
    apply hMD
    rw [← hAM]
    exact subset_generatedVonNeumannAlgebra A hT
  have hBD : B ≤ (concreteCenter M).commutant.toStarSubalgebra := by
    intro T hT
    apply hND
    rw [← hBN]
    exact subset_generatedVonNeumannAlgebra B hT
  obtain ⟨C, hCc, hCs, hAC, hBC, hCD⟩ :=
    exists_closed_separable_common_superalgebra_in A B (concreteCenter M).commutant
      hAs hBs hAD hBD
  obtain ⟨D⟩ := hCentral H M N hcenter A B C hAc hBc hCc hAs hBs hCs hAM hBN hAC hBC hCD
  have hex (n : ℕ) : ∀ᵐ x ∂(D.stratum n).μ,
      ∃ v : unitary ((D.stratum n).K →L[ℂ] (D.stratum n).K),
        Conjugates v
          (generatedVonNeumannAlgebra
            ((D.representation n x).comp (StarSubalgebra.inclusion hAC)).range)
          (generatedVonNeumannAlgebra
            ((D.representation n x).comp (StarSubalgebra.inclusion hBC)).range) ∧
        ‖(v : (D.stratum n).K →L[ℂ] (D.stratum n).K) - 1‖ ≤ a / 2 := by
    filter_upwards [D.factors n] with x hx
    have hd := kkDistance_commonRepresentation_le hK A B C hAc hBc hCc hAC hBC
      (D.representation n x)
    have hdτ : kkDistance
        (generatedVonNeumannAlgebra
          ((D.representation n x).comp (StarSubalgebra.inclusion hAC)).range)
        (generatedVonNeumannAlgebra
          ((D.representation n x).comp (StarSubalgebra.inclusion hBC)).range) < τ := by
      linarith only [hd, hAB, hτ]
    obtain ⟨v, hv, hvn⟩ := hlocal (D.stratum n).K _ _ hx.1 hx.2 hdτ
    exact ⟨v, hv, hvn.le⟩
  obtain ⟨v, hv, hvn⟩ := exists_bounded_conjugacy_from_centralPair hK hSelect
    M N A B C hAc hBc hAs hBs D (by positivity : 0 ≤ a / 2) hex
  exact ⟨v, hv, hvn.trans_lt (by linarith only [ha])⟩

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.commonCenterSeparableStability_of_factors_oai.{u} := @OAI.KadisonKastler.commonCenterSeparableStability_of_factors_oai.{u}
