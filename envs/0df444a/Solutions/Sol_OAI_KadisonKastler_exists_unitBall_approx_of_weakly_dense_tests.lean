-- Prove2me | solution 1 for OAI.KadisonKastler.exists_unitBall_approx_of_weakly_dense_tests
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T08:56:10.981036+00:00
-- url     : https://prove2.me/submissions/6d8d476e-998d-47f3-b217-8303fb276464

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Matrix.Composition
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K013

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WeakCPLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem exists_unitBall_approx_of_weakly_dense_tests_oai
    {ι : Type*} {M N : VonNeumannAlgebra H} (T : ι → H →L[ℂ] H)
    (hT : WeakUnitBallDense T M) {r : ℝ} (hr : 0 ≤ r)
    (hnear : ∀ i, ∃ b ∈ unitBall N, ‖T i - b‖ ≤ r)
    (a : H →L[ℂ] H) (ha : a ∈ unitBall M) :
    ∃ b ∈ unitBall N, ‖a - b‖ ≤ r := by
  obtain ⟨l, hl, hlim⟩ := hT.2 a ha
  let : l.NeBot := hl
  exact exists_unitBall_approx_of_weak_limit N T a hlim hr hnear

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.exists_unitBall_approx_of_weakly_dense_tests_oai.{u_1, u_2} := @OAI.KadisonKastler.exists_unitBall_approx_of_weakly_dense_tests_oai.{u_1, u_2}
