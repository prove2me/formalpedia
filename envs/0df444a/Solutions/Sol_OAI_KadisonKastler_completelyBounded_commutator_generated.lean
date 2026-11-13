-- Prove2me | solution 1 for OAI.KadisonKastler.completelyBounded_commutator_generated
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:53:26.695975+00:00
-- url     : https://prove2.me/submissions/200324d9-9a9f-4495-a830-04cb4d2efd21

import Mathlib
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Spectrum
import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Powerset
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
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Q260K015

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CStarCommutatorClosure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instNonemptyMatrixSiteBlockIndex _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Spatial commutator bounds pass to the represented bicommutant

Spectral clipping lifts each represented contraction to an actual source
contraction. Kaplansky density then passes its commutator bound to the
unit ball of the represented von Neumann closure.
-/

namespace KadisonKastler

open Filter
open scoped Topology

noncomputable section

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem exists_source_contraction (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (b : π.range) (hb : ‖(b : H →L[ℂ] H)‖ ≤ 1) :
    ∃ a : A, π a = b ∧ ‖a‖ ≤ 1 := by
  obtain ⟨a, ha⟩ := b.property
  change π a = (b : H →L[ℂ] H) at ha
  refine ⟨spectralClip 1 a, ?_, spectralClip_norm_le zero_lt_one a⟩
  rw [map_spectralClip_eq π zero_lt_one a (by simpa only [ha] using hb), ha]

theorem commutator_bound_generated_contraction
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H) {e : ℝ} (he : 0 ≤ e)
    (hsource : ∀ a : A, ‖T * π a - π a * T‖ ≤ e * ‖a‖)
    (b : H →L[ℂ] H)
    (hb : b ∈ generatedVonNeumannAlgebra π.range) (hbn : ‖b‖ ≤ 1) :
    ‖T * b - b * T‖ ≤ e := by
  classical
  have hb' : b ∈ Set.centralizer (Set.centralizer (π.range : Set (H →L[ℂ] H))) := by
    rwa [← generatedVonNeumannAlgebra_coe]
  obtain ⟨a, ha, ht⟩ := publishedKaplanskyDensity.exists_strong_contraction_net
    π.range b hb' hbn
  have hbound (d : Finset H × ℕ) : ‖T * (a d : H →L[ℂ] H) - (a d : H →L[ℂ] H) * T‖ ≤ e := by
    obtain ⟨x, hx, hxn⟩ := exists_source_contraction π (a d) (ha d)
    rw [← hx]
    exact (hsource x).trans (mul_le_of_le_one_right he hxn)
  apply ContinuousLinearMap.opNorm_le_bound _ he
  intro x
  have hlim : Tendsto (fun d =>
      (T * (a d : H →L[ℂ] H) - (a d : H →L[ℂ] H) * T) x) atTop
      (𝓝 ((T * b - b * T) x)) := by
    change Tendsto (fun d => T ((a d : H →L[ℂ] H) x) - (a d : H →L[ℂ] H) (T x))
      atTop (𝓝 (T (b x) - b (T x)))
    exact (T.continuous.continuousAt.tendsto.comp (ht x)).sub (ht (T x))
  exact le_of_tendsto hlim.norm (Eventually.of_forall fun d =>
    (ContinuousLinearMap.le_opNorm _ x).trans
      (mul_le_mul_of_nonneg_right (hbound d) (norm_nonneg x)))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_AmplifiedCommutatorClosure
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Complete commutator estimates on finite represented closures -/

namespace KadisonKastler

open Generator
open scoped BigOperators

noncomputable section

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [PartialOrder A] [StarOrderedRing A] in
theorem finiteAmplifiedRepresentation_range (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    (finiteAmplifiedRepresentation (ι := ι) π).range = matrixOperatorAlgebra π.range := by
  apply le_antisymm
  · rintro T ⟨X, rfl⟩
    refine ⟨coefficientMatrixMap π X, ?_, rfl⟩
    intro i j
    exact ⟨X i j, rfl⟩
  · rintro T ⟨Y, hY, rfl⟩
    have hex : ∀ i j, ∃ a : A, π a = Y i j := fun i j => hY i j
    choose X hX using hex
    refine ⟨CStarMatrix.ofMatrix X, ?_⟩
    change hilbertMatrix (coefficientMatrixMap π (CStarMatrix.ofMatrix X)) = hilbertMatrix Y
    congr 1
    apply CStarMatrix.ext
    intro i j
    exact hX i j

omit [PartialOrder A] [StarOrderedRing A] in
theorem finiteAmplifiedRepresentation_apply (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (X : CStarMatrix ι ι A) (x : FiniteHilbert ι H) (i : ι) :
    finiteAmplifiedRepresentation π X x i = ∑ j, π (X i j) (x j) := by
  change hilbertMatrix (coefficientMatrixMap π X) x i = _
  rw [hilbertMatrix_apply]
  rfl

omit [PartialOrder A] [StarOrderedRing A] in
theorem finiteAmplifiedRepresentation_commutator
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (X : CStarMatrix ι ι A) :
    diagonalOperator T * finiteAmplifiedRepresentation π X -
        finiteAmplifiedRepresentation π X * diagonalOperator T =
      hilbertMatrix (CStarMatrix.mapₗ
        ((innerDerivation T).comp π.toAlgHom.toLinearMap) X) := by
  ext x i
  simp only [sub_apply, mul_apply_eq_comp, WithLp.ofLp_sub, Pi.sub_apply,
    diagonalOperator_apply, finiteAmplifiedRepresentation_apply, hilbertMatrix_apply]
  change T (∑ j, π (X i j) (x j)) - (∑ j, π (X i j) (T (x j))) =
    ∑ j, (T (π (X i j) (x j)) - π (X i j) (T (x j)))
  rw [map_sum, Finset.sum_sub_distrib]

theorem completelyBounded_commutator_generated_oai
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (T : H →L[ℂ] H) {e : ℝ} (he : 0 ≤ e)
    (hcb : CompletelyBoundedBy ((innerDerivation T).comp π.toAlgHom.toLinearMap) e)
    (n : ℕ) (b : FiniteHilbert (Fin n) H →L[ℂ] FiniteHilbert (Fin n) H)
    (hb : b ∈ matrixVonNeumann (generatedVonNeumannAlgebra π.range)) (hbn : ‖b‖ ≤ 1) :
    ‖diagonalOperator T * b - b * diagonalOperator T‖ ≤ e := by
  apply commutator_bound_generated_contraction (finiteAmplifiedRepresentation π)
    (diagonalOperator T) he _ b _ hbn
  · intro X
    rw [finiteAmplifiedRepresentation_commutator, norm_hilbertMatrix]
    exact hcb n n X
  · rwa [finiteAmplifiedRepresentation_range, generated_matrixOperatorAlgebra]

end

end KadisonKastler

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.KadisonKastler.completelyBounded_commutator_generated_oai.{u_1, u_2} := @OAI.KadisonKastler.completelyBounded_commutator_generated_oai.{u_1, u_2}
