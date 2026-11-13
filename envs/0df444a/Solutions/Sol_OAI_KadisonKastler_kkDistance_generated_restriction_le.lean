-- Prove2me | solution 1 for OAI.KadisonKastler.kkDistance_generated_restriction_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:09:01.392302+00:00
-- url     : https://prove2.me/submissions/3cc2828d-832c-47d3-b5c2-c2108cfaa951

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.LocallyConvex.WeakSpace
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Zorn
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K012
import Definitions.Def_Q260K013
import Definitions.Def_Q260K015

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
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.PopaCorner.instNormedRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
-- module Solutions.OAIQ075_KS.KadisonKastler_SeparableAlgebraPair
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RestrictionGap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem exists_restriction_ball_approx
    (hAc : IsClosed (A : Set (H →L[ℂ] H)))
    (hBc : IsClosed (B : Set (H →L[ℂ] H)))
    {r : ℝ} (hr : Metric.hausdorffDist (starAlgebraBall A) (starAlgebraBall B) < r)
    {x : K →L[ℂ] K} (hx : x ∈ starAlgebraBall (reducingRestriction K A hA).range) :
    ∃ y ∈ starAlgebraBall (reducingRestriction K B hB).range, ‖x - y‖ < r := by
  let : CStarAlgebra A := StarSubalgebra.cstarAlgebra A (h_closed := hAc)
  let : CStarAlgebra B := StarSubalgebra.cstarAlgebra B (h_closed := hBc)
  obtain ⟨a, ha, haeq⟩ := exists_contractive_starAlgHom_preimage
    (reducingRestriction K A hA) hx.1 hx.2
  obtain ⟨b, hb, hab⟩ := Metric.exists_dist_lt_of_hausdorffDist_lt
    (show a.val ∈ starAlgebraBall A from ⟨a.property, ha⟩) hr
    (starAlgebraBall_hausdorffEDist_ne_top A B)
  let b' : B := ⟨b, hb.1⟩
  refine ⟨reducingRestriction K B hB b',
    ⟨⟨b', rfl⟩, (NonUnitalStarAlgHom.norm_apply_le _ b').trans hb.2⟩, ?_⟩
  have hnorm : ‖x - reducingRestriction K B hB b'‖ ≤ ‖a.val - b‖ := by
    rw [← haeq]
    change ‖cornerCompression K a.val - cornerCompression K b‖ ≤ ‖a.val - b‖
    rw [← map_sub]
    exact norm_cornerCompression_le K _
  exact hnorm.trans_lt (by simpa only [dist_eq_norm] using hab)

/-- Restriction can have a kernel on either algebra. It still decreases
the distance of their closed unit balls. -/
theorem restriction_gap_le
    (hAc : IsClosed (A : Set (H →L[ℂ] H)))
    (hBc : IsClosed (B : Set (H →L[ℂ] H))) :
    Metric.hausdorffDist (starAlgebraBall (reducingRestriction K A hA).range)
      (starAlgebraBall (reducingRestriction K B hB).range) ≤
      Metric.hausdorffDist (starAlgebraBall A) (starAlgebraBall B) := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro r hr
  apply Metric.hausdorffDist_le_of_mem_dist (Metric.hausdorffDist_nonneg.trans hr.le)
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := exists_restriction_ball_approx K A B hA hB hAc hBc hr hx
    exact ⟨y, hy, by simpa only [dist_eq_norm] using hxy.le⟩
  · intro y hy
    obtain ⟨x, hx, hyx⟩ := exists_restriction_ball_approx K B A hB hA hBc hAc
      (by simpa only [Metric.hausdorffDist_comm] using hr) hy
    exact ⟨x, hx, by simpa only [dist_eq_norm] using hyx.le⟩

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GeneratedAlgebraGap
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem kkDistance_generated_restriction_le_oai (hK : PublishedKaplanskyDensity.{u})
    (K : Submodule ℂ H) [CompleteSpace K]
    (A B : StarSubalgebra ℂ (H →L[ℂ] H))
    (hA : ∀ a : A, ∀ x ∈ K, (a : H →L[ℂ] H) x ∈ K)
    (hB : ∀ b : B, ∀ x ∈ K, (b : H →L[ℂ] H) x ∈ K)
    (hAc : IsClosed (A : Set (H →L[ℂ] H)))
    (hBc : IsClosed (B : Set (H →L[ℂ] H))) :
    kkDistance (generatedVonNeumannAlgebra (reducingRestriction K A hA).range)
      (generatedVonNeumannAlgebra (reducingRestriction K B hB).range) ≤
      Metric.hausdorffDist (starAlgebraBall A) (starAlgebraBall B) :=
  (kkDistance_generated_le hK _ _).trans (restriction_gap_le K A B hA hB hAc hBc)

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.kkDistance_generated_restriction_le_oai.{u} := @OAI.KadisonKastler.kkDistance_generated_restriction_le_oai.{u}
