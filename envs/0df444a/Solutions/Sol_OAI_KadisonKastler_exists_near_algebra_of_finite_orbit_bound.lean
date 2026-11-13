-- Prove2me | solution 1 for OAI.KadisonKastler.exists_near_algebra_of_finite_orbit_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:52:13.488738+00:00
-- url     : https://prove2.me/submissions/52060d88-e9f7-49b7-8b6b-55621e269e1f

import Mathlib
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.WeakOperatorTopology
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Topology.Algebra.Algebra
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Instances.Complex
import Definitions.Def_Q260K007
import Definitions.Def_Q260K010
import Theorems.Thm_OAI_KadisonKastler_exists_finite_polar_coefficients

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteOperatorDuality
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite operator coefficient duality

The polar factor and a positive rank-one decomposition give vector
coefficients whose two square sums are bounded by the functional norm.
This is the finite-dimensional part of the commutant distance formula.
-/

namespace KadisonKastler

open InnerProductSpace
open scoped BigOperators

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable [FiniteDimensional ℂ E]

theorem operatorTracePairing_rankOne (x y : E) (S : E →L[ℂ] E) :
    operatorTracePairing (rankOne ℂ x y) S = inner ℂ x (S y) := by
  rw [operatorTracePairing_apply, adjoint_rankOne]
  rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.trace_comp_comm']
  rw [← ContinuousLinearMap.toLinearMap_comp, comp_rankOne, trace_rankOne]

theorem operatorTracePairing_sum {ι : Type*} [Fintype ι]
    (T : ι → E →L[ℂ] E) (S : E →L[ℂ] E) :
    operatorTracePairing (∑ i, T i) S = ∑ i, operatorTracePairing (T i) S := by
  change LinearMap.trace ℂ E ((star (∑ i, T i) * S).toLinearMap) = _
  rw [star_sum, Finset.sum_mul, ContinuousLinearMap.toLinearMap_sum, map_sum]
  rfl

theorem finite_dimensional_coefficient_factorization {ι : Type*} [Fintype ι]
    (x y : ι → E) :
    ∃ (n : ℕ) (a b : Fin n → E),
      finiteOperatorCoefficient x y = finiteOperatorCoefficient a b ∧
      (∑ i, ‖a i‖ ^ 2) ≤ ‖finiteOperatorCoefficient x y‖ ∧
      (∑ i, ‖b i‖ ^ 2) ≤ ‖finiteOperatorCoefficient x y‖ := by
  let T := ∑ i, rankOne ℂ (y i) (x i)
  have hT : operatorTracePairing T = finiteOperatorCoefficient x y := by
    ext S
    simp only [T, operatorTracePairing_sum, operatorTracePairing_rankOne,
      finiteOperatorCoefficient_apply]
  simpa only [hT] using exists_finite_polar_coefficients T

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_IsometryComplement
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Complementary projection of an isometric embedding

The formulas below retain the concrete adjoint of the embedding, as needed
for a contractive lift with prescribed first coordinate.
-/

namespace KadisonKastler

open scoped InnerProductSpace

noncomputable section

variable {E K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem adjoint_isometry_apply (V : E →ₗᵢ[ℂ] K) (x : E) :
    V.toContinuousLinearMap.adjoint (V x) = x := by
  exact congrArg (fun T : E →L[ℂ] E => T x) V.adjoint_comp_self

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteCoefficientFactorization
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFiniteBoundedWord _root_.OAI.HochschildPatching.instFiniteLinearLabel _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Sharp finite coefficient factorization on an arbitrary Hilbert space

All vectors involved lie in a finite-dimensional subspace. Compression and
extension by zero preserve the dual norm, so finite-dimensional polar
duality applies without a separability assumption on the ambient space.
-/

namespace KadisonKastler

open scoped BigOperators InnerProductSpace

noncomputable section

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem isometricOperatorLift_norm_le (J : E →ₗᵢ[ℂ] H) (S : E →L[ℂ] E) :
    ‖isometricOperatorLift J S‖ ≤ ‖S‖ := by
  calc
    _ ≤ ‖J.toContinuousLinearMap‖ * (‖S‖ * ‖J.toContinuousLinearMap.adjoint‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _)
          (norm_nonneg _))
    _ ≤ 1 * (‖S‖ * 1) := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      exact mul_le_mul J.norm_toContinuousLinearMap_le
        (mul_le_mul_of_nonneg_left J.norm_toContinuousLinearMap_le (norm_nonneg _))
        (by positivity) zero_le_one
    _ = ‖S‖ := by ring

theorem finiteOperatorCoefficient_lift {ι : Type*} [Fintype ι]
    (J : E →ₗᵢ[ℂ] H) (x y : ι → E) (S : E →L[ℂ] E) :
    finiteOperatorCoefficient (fun i => J (x i)) (fun i => J (y i))
      (isometricOperatorLift J S) = finiteOperatorCoefficient x y S := by
  simp only [finiteOperatorCoefficient_apply, isometricOperatorLift,
    ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    adjoint_isometry_apply, J.inner_map_map]

theorem finiteOperatorCoefficient_compress {ι : Type*} [Fintype ι]
    (J : E →ₗᵢ[ℂ] H) (x y : ι → E) (S : H →L[ℂ] H) :
    finiteOperatorCoefficient x y
      (J.toContinuousLinearMap.adjoint.comp (S.comp J.toContinuousLinearMap)) =
      finiteOperatorCoefficient (fun i => J (x i)) (fun i => J (y i)) S := by
  simp only [finiteOperatorCoefficient_apply, ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact J.toContinuousLinearMap.adjoint_inner_right _ _

theorem finiteOperatorCoefficient_norm_lift {ι : Type*} [Fintype ι]
    (J : E →ₗᵢ[ℂ] H) (x y : ι → E) :
    ‖finiteOperatorCoefficient x y‖ ≤
      ‖finiteOperatorCoefficient (fun i => J (x i)) (fun i => J (y i))‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro S
  rw [← finiteOperatorCoefficient_lift J x y S]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_left (isometricOperatorLift_norm_le J S) (norm_nonneg _))

theorem isometric_coefficient_factorization [FiniteDimensional ℂ E]
    {ι : Type*} [Fintype ι] (J : E →ₗᵢ[ℂ] H) (x y : ι → E) :
    ∃ (n : ℕ) (a b : Fin n → H),
      finiteOperatorCoefficient (fun i => J (x i)) (fun i => J (y i)) =
        finiteOperatorCoefficient a b ∧
      (∑ i, ‖a i‖ ^ 2) ≤
        ‖finiteOperatorCoefficient (fun i => J (x i)) (fun i => J (y i))‖ ∧
      (∑ i, ‖b i‖ ^ 2) ≤
        ‖finiteOperatorCoefficient (fun i => J (x i)) (fun i => J (y i))‖ := by
  obtain ⟨n, a, b, he, ha, hb⟩ := finite_dimensional_coefficient_factorization x y
  refine ⟨n, fun i => J (a i), fun i => J (b i), ?_, ?_, ?_⟩
  · ext S
    rw [← finiteOperatorCoefficient_compress J x y, he,
      finiteOperatorCoefficient_compress]
  · simpa only [J.norm_map] using ha.trans (finiteOperatorCoefficient_norm_lift J x y)
  · simpa only [J.norm_map] using hb.trans (finiteOperatorCoefficient_norm_lift J x y)

/-- Every finite vector functional on an arbitrary Hilbert space admits
coefficient vectors with each squared Hilbert sum at most its dual norm. -/
theorem finite_coefficient_factorization {ι : Type*} [Fintype ι] (x y : ι → H) :
    ∃ (n : ℕ) (a b : Fin n → H),
      finiteOperatorCoefficient x y = finiteOperatorCoefficient a b ∧
      (∑ i, ‖a i‖ ^ 2) ≤ ‖finiteOperatorCoefficient x y‖ ∧
      (∑ i, ‖b i‖ ^ 2) ≤ ‖finiteOperatorCoefficient x y‖ := by
  let V := Submodule.span ℂ (Set.range x ∪ Set.range y)
  have : FiniteDimensional ℂ V :=
    FiniteDimensional.span_of_finite ℂ ((Set.finite_range x).union (Set.finite_range y))
  let x' : ι → V := fun i => ⟨x i, Submodule.subset_span (Or.inl ⟨i, rfl⟩)⟩
  let y' : ι → V := fun i => ⟨y i, Submodule.subset_span (Or.inr ⟨i, rfl⟩)⟩
  exact isometric_coefficient_factorization V.subtypeₗᵢ x' y'

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WOTCoefficientDuality
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.crossMatchingFintype _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Finite coefficient form of a weak-operator continuous functional

The defining weak topology first gives a finite coefficient expression.
Finite polar duality then chooses coefficients with sharp Hilbert norms.
-/

namespace KadisonKastler

open scoped BigOperators InnerProductSpace

noncomputable section

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem wot_functional_finite_coefficients (f : (H →WOT[ℂ] H) →L[ℂ] ℂ) :
    ∃ (ι : Type u) (_ : Fintype ι) (x y : ι → H),
      f.comp (ContinuousLinearMap.WOTofCLM (𝕜₂ := ℂ)) = finiteOperatorCoefficient x y := by
  classical
  let v : (H × StrongDual ℂ H) → (H →WOT[ℂ] H) →ₗ[ℂ] ℂ :=
    fun p => (LinearMap.proj p).comp (ContinuousLinearMapWOT.inducingFn (RingHom.id ℂ) H H)
  have hspan : f.toLinearMap ∈ Submodule.span ℂ (Set.range v) := by
    rw [LinearMap.mem_span_iff_continuous]
    have ht : (⨅ p, TopologicalSpace.induced (v p) inferInstance) =
        ContinuousLinearMapWOT.instTopologicalSpace (σ := RingHom.id ℂ) (E := H) (F := H) := by
      change _ = TopologicalSpace.induced
        (ContinuousLinearMapWOT.inducingFn (RingHom.id ℂ) H H) _
      rw [induced_to_pi]
      rfl
    rw [ht]
    exact f.continuous
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hspan
  let x : c.support → H := fun p => c p • p.val.1
  let y : c.support → H := fun p => (InnerProductSpace.toDual ℂ H).symm p.val.2
  refine ⟨↥c.support, inferInstance, x, y, ?_⟩
  apply ContinuousLinearMap.ext
  intro S
  have h := congrArg (fun g : (H →WOT[ℂ] H) →ₗ[ℂ] ℂ =>
    g (ContinuousLinearMapWOT.ofCLM S)) hc
  rw [Finsupp.sum, LinearMap.sum_apply] at h
  rw [← Finset.sum_coe_sort] at h
  change (∑ p : c.support, c p * p.val.2 (S p.val.1)) =
    f (ContinuousLinearMapWOT.ofCLM S) at h
  change f (ContinuousLinearMapWOT.ofCLM S) = _
  rw [← h, finiteOperatorCoefficient_apply]
  apply Finset.sum_congr rfl
  intro p _
  change c p * p.val.2 (S p.val.1) =
    inner ℂ ((InnerProductSpace.toDual ℂ H).symm p.val.2) (S (c p • p.val.1))
  rw [map_smul, inner_smul_right]
  congr 1
  have he := congrArg (fun g : StrongDual ℂ H => g (S p.val.1))
    ((InnerProductSpace.toDual ℂ H).apply_symm_apply p.val.2)
  exact he.symm

theorem wot_functional_sharp_coefficients (f : (H →WOT[ℂ] H) →L[ℂ] ℂ) :
    ∃ (n : ℕ) (x y : Fin n → H),
      f.comp (ContinuousLinearMap.WOTofCLM (𝕜₂ := ℂ)) = finiteOperatorCoefficient x y ∧
      (∑ i, ‖x i‖ ^ 2) ≤ ‖f.comp (ContinuousLinearMap.WOTofCLM (𝕜₂ := ℂ))‖ ∧
      (∑ i, ‖y i‖ ^ 2) ≤ ‖f.comp (ContinuousLinearMap.WOTofCLM (𝕜₂ := ℂ))‖ := by
  obtain ⟨ι, hι, a, b, hab⟩ := wot_functional_finite_coefficients f
  let := hι
  rw [hab]
  exact finite_coefficient_factorization a b

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_RealPartDualBound
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Recovering a functional norm from its real part on a ball -/

namespace KadisonKastler

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem norm_mul_le_of_real_bound (f : E →L[ℂ] ℂ) {r C : ℝ} (hr : 0 < r)
    (h : ∀ x : E, ‖x‖ ≤ r → (f x).re ≤ C) : r * ‖f‖ ≤ C := by
  let g := (StrongDual.extendRCLikeₗᵢ (𝕜 := ℂ) (F := E)).symm f
  have hC : 0 ≤ C := by simpa using h 0 (by simpa using hr.le)
  have hnorm : ‖g‖ ≤ C / r := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hC hr.le)
    intro x hx
    have hp : r * g x ≤ C := by
      have hh := h (r • x) (by simp [norm_smul, abs_of_pos hr, hx])
      change g (r • x) ≤ C at hh
      simpa only [map_smul, smul_eq_mul] using hh
    have hn : -(r * g x) ≤ C := by
      have hh := h (r • (-x)) (by simp [norm_smul, abs_of_pos hr, hx])
      change g (r • (-x)) ≤ C at hh
      simpa only [map_smul, map_neg, smul_eq_mul, mul_neg] using hh
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have hh : -g x ≤ C / r := (le_div_iff₀ hr).mpr (by nlinarith)
      linarith
    · apply (le_div_iff₀ hr).mpr
      nlinarith
  have he : ‖g‖ = ‖f‖ := (StrongDual.extendRCLikeₗᵢ (𝕜 := ℂ) (F := E)).symm.norm_map f
  rw [he] at hnorm
  nlinarith [(le_div_iff₀ hr).mp hnorm]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_WOTDistanceSeparation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Weak operator separation and operator-norm distance

A dual estimate on weak-operator continuous functionals annihilating a
closed subspace gives strict norm approximants in that subspace.
-/

namespace KadisonKastler

open scoped Pointwise

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem wotNormBall_compact (r : ℝ) : IsCompact (wotNormBall (H := H) r) := by
  let M : VonNeumannAlgebra H :=
    { toStarSubalgebra := StarSubalgebra.centralizer ℂ (∅ : Set (H →L[ℂ] H))
      centralizer_centralizer' := Set.centralizer_centralizer_centralizer _ }
  have he : Generator.Tracial.weakOperatorBall M r = wotNormBall (H := H) r := by
    ext T
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      change T.toCLM ∈ StarSubalgebra.centralizer ℂ (∅ : Set (H →L[ℂ] H))
      simp [StarSubalgebra.mem_centralizer_iff]
  rw [← he]
  exact Generator.Tracial.weakOperatorBall_isCompact M r

omit [CompleteSpace H] in
theorem wotNormBall_convex (r : ℝ) : Convex ℝ (wotNormBall (H := H) r) := by
  have he : wotNormBall (H := H) r =
      ContinuousLinearMapWOT.ofCLM '' Metric.closedBall (0 : H →L[ℂ] H) r := by
    ext T
    constructor
    · intro hT
      exact ⟨T.toCLM, by simpa [wotNormBall, Metric.mem_closedBall] using hT, rfl⟩
    · rintro ⟨T, hT, rfl⟩
      simpa [wotNormBall, Metric.mem_closedBall] using hT
  rw [he]
  exact (convex_closedBall (0 : H →L[ℂ] H) r).linear_image
    ((ContinuousLinearMap.WOTofCLM (𝕜₂ := ℂ)).restrictScalars ℝ).toLinearMap

theorem exists_near_subspace_of_wot_dual_bound
    (S : Submodule ℂ (H →L[ℂ] H))
    (hS : IsClosed {T : H →WOT[ℂ] H | T.toCLM ∈ S})
    (T : H →L[ℂ] H) {c : ℝ} (hc : 0 ≤ c)
    (hdual : ∀ f : (H →WOT[ℂ] H) →L[ℂ] ℂ,
      (∀ D ∈ S, f (ContinuousLinearMapWOT.ofCLM D) = 0) →
      ‖f (ContinuousLinearMapWOT.ofCLM T)‖ ≤
        c * ‖f.comp (ContinuousLinearMap.WOTofCLM (𝕜₂ := ℂ))‖)
    {r : ℝ} (hr : c < r) : ∃ D ∈ S, ‖D - T‖ < r := by
  classical
  let s := (c + r) / 2
  have hcs : c < s := by dsimp [s] <;> linarith
  have hsr : s < r := by dsimp [s] <;> linarith
  have hs : 0 < s := lt_of_le_of_lt hc hcs
  let C : Submodule ℂ (H →WOT[ℂ] H) :=
    S.comap (ContinuousLinearMapWOT.linearEquiv ℂ).toLinearMap
  let B := wotNormBall (H := H) s
  have hclosed : IsClosed ((C : Set (H →WOT[ℂ] H)) + B) :=
    hS.add_right_of_isCompact (wotNormBall_compact s)
  have hconvex : Convex ℝ ((C : Set (H →WOT[ℂ] H)) + B) :=
    (C.restrictScalars ℝ).convex.add (wotNormBall_convex s)
  by_contra hn
  have hnot : ContinuousLinearMapWOT.ofCLM T ∉ (C : Set (H →WOT[ℂ] H)) + B := by
    rintro ⟨D, hD, E, hE, hsum⟩
    apply hn
    refine ⟨D.toCLM, hD, ?_⟩
    have he : D.toCLM - T = -E.toCLM := by
      have hh := congrArg ContinuousLinearMapWOT.toCLM hsum
      change D.toCLM + E.toCLM = T at hh
      rw [← hh]
      abel
    rw [he, norm_neg]
    exact (show ‖E.toCLM‖ ≤ s from hE).trans_lt hsr
  obtain ⟨f, u, hfu, hut⟩ := RCLike.geometric_hahn_banach_closed_point
    (𝕜 := ℂ) hconvex hclosed hnot
  have hzero : ∀ D ∈ S, f (ContinuousLinearMapWOT.ofCLM D) = 0 := by
    intro D hD
    by_contra hne
    let z : ℂ := (u + 1) / f (ContinuousLinearMapWOT.ofCLM D)
    have hmem : ContinuousLinearMapWOT.ofCLM (z • D) ∈
        (C : Set (H →WOT[ℂ] H)) + B := by
      refine ⟨ContinuousLinearMapWOT.ofCLM (z • D), S.smul_mem z hD, 0, ?_, add_zero _⟩
      change ‖(0 : H →L[ℂ] H)‖ ≤ s
      simpa using hs.le
    have hh := hfu _ hmem
    have he : f (ContinuousLinearMapWOT.ofCLM (z • D)) = (u + 1 : ℂ) := by
      rw [ContinuousLinearMapWOT.ofCLM_smul, map_smul, smul_eq_mul]
      exact div_mul_cancel₀ _ hne
    rw [he] at hh
    norm_num at hh
  have hball : ∀ X : H →L[ℂ] H, ‖X‖ ≤ s →
      (f (ContinuousLinearMapWOT.ofCLM X)).re ≤ u := by
    intro X hX
    exact (hfu _ ⟨0, S.zero_mem, ContinuousLinearMapWOT.ofCLM X, hX, zero_add _⟩).le
  have hnorm : s * ‖f.comp (ContinuousLinearMap.WOTofCLM (𝕜₂ := ℂ))‖ ≤ u :=
    norm_mul_le_of_real_bound _ hs hball
  have hbound := hdual f hzero
  have hre := Complex.re_le_norm (f (ContinuousLinearMapWOT.ofCLM T))
  have hcmp := mul_le_mul_of_nonneg_right hcs.le
    (norm_nonneg (f.comp (ContinuousLinearMap.WOTofCLM (𝕜₂ := ℂ))))
  change u < (f (ContinuousLinearMapWOT.ofCLM T)).re at hut
  linarith

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteOrbitDistance
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.vectorOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.tensorScalarsInnerProductSpace _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Operator distance from finite simultaneous orbit estimates

Finite coefficient factorization turns orbit-projection bounds into dual
bounds. Weak operator separation then supplies norm approximants.
-/

namespace KadisonKastler

open Generator
open scoped BigOperators InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem finite_orbit_dual_bound (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) {c : ℝ} (hc : 0 ≤ c)
    (horbit : ∀ (n : ℕ) (x : FiniteHilbert (Fin n) H),
      ‖diagonalOperator T x - (tupleOrbitClosure S x).starProjection (diagonalOperator T x)‖ ≤
        c * ‖x‖)
    (f : (H →WOT[ℂ] H) →L[ℂ] ℂ)
    (hf : ∀ a ∈ S, f (ContinuousLinearMapWOT.ofCLM a) = 0) :
    ‖f (ContinuousLinearMapWOT.ofCLM T)‖ ≤
      c * ‖f.comp (ContinuousLinearMap.WOTofCLM (𝕜₂ := ℂ))‖ := by
  obtain ⟨n, x, y, heq, hx, hy⟩ := wot_functional_sharp_coefficients f
  let ξ : FiniteHilbert (Fin n) H := WithLp.toLp 2 x
  let η : FiniteHilbert (Fin n) H := WithLp.toLp 2 y
  have heval (a : H →L[ℂ] H) : f (ContinuousLinearMapWOT.ofCLM a) =
      inner ℂ η (diagonalOperator a ξ) := by
    have hh := congrArg (fun g : (H →L[ℂ] H) →L[ℂ] ℂ => g a) heq
    change f (ContinuousLinearMapWOT.ofCLM a) = finiteOperatorCoefficient x y a at hh
    simpa only [finiteOperatorCoefficient_apply,
      PiLp.inner_apply, diagonalOperator_apply, ξ, η] using hh
  have hker : tupleOrbitClosure S ξ ≤ (innerSL ℂ η).toLinearMap.ker := by
    apply Submodule.topologicalClosure_minimal
    · rintro z ⟨a, rfl⟩
      change inner ℂ η (diagonalOperator a.val ξ) = 0
      rw [← heval, hf a.val a.property]
    · exact (innerSL ℂ η).isClosed_ker
  have horth : inner ℂ η ((tupleOrbitClosure S ξ).starProjection
      (diagonalOperator T ξ)) = 0 :=
    hker ((tupleOrbitClosure S ξ).starProjection_apply_mem _)
  have hξ : ‖ξ‖ ^ 2 ≤ ‖f.comp (ContinuousLinearMap.WOTofCLM (𝕜₂ := ℂ))‖ := by
    simpa only [PiLp.norm_sq_eq_of_L2, ξ] using hx
  have hη : ‖η‖ ^ 2 ≤ ‖f.comp (ContinuousLinearMap.WOTofCLM (𝕜₂ := ℂ))‖ := by
    simpa only [PiLp.norm_sq_eq_of_L2, η] using hy
  have hprod : ‖η‖ * ‖ξ‖ ≤ ‖f.comp (ContinuousLinearMap.WOTofCLM (𝕜₂ := ℂ))‖ := by
    nlinarith [sq_nonneg (‖η‖ - ‖ξ‖)]
  rw [heval]
  calc
    ‖inner ℂ η (diagonalOperator T ξ)‖ =
        ‖inner ℂ η (diagonalOperator T ξ -
          (tupleOrbitClosure S ξ).starProjection (diagonalOperator T ξ))‖ := by
      rw [inner_sub_right, horth, sub_zero]
    _ ≤ ‖η‖ * ‖diagonalOperator T ξ -
        (tupleOrbitClosure S ξ).starProjection (diagonalOperator T ξ)‖ := norm_inner_le_norm _ _
    _ ≤ ‖η‖ * (c * ‖ξ‖) := mul_le_mul_of_nonneg_left (horbit n ξ) (norm_nonneg _)
    _ = c * (‖η‖ * ‖ξ‖) := by ring
    _ ≤ c * ‖f.comp (ContinuousLinearMap.WOTofCLM (𝕜₂ := ℂ))‖ :=
      mul_le_mul_of_nonneg_left hprod hc

theorem exists_near_algebra_of_finite_orbit_bound_oai
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : WOTClosed S)
    (T : H →L[ℂ] H) {c : ℝ} (hc : 0 ≤ c)
    (horbit : ∀ (n : ℕ) (x : FiniteHilbert (Fin n) H),
      ‖diagonalOperator T x - (tupleOrbitClosure S x).starProjection (diagonalOperator T x)‖ ≤
        c * ‖x‖)
    {r : ℝ} (hr : c < r) : ∃ D ∈ S, ‖D - T‖ < r :=
  exists_near_subspace_of_wot_dual_bound S.toSubmodule hS T hc
    (fun f hf => finite_orbit_dual_bound S T hc horbit f hf) hr

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.exists_near_algebra_of_finite_orbit_bound_oai.{u_1} := @OAI.KadisonKastler.exists_near_algebra_of_finite_orbit_bound_oai.{u_1}
