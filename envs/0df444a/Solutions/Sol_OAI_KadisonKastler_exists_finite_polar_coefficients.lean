-- Prove2me | solution 1 for OAI.KadisonKastler.exists_finite_polar_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T04:52:12.465119+00:00
-- url     : https://prove2.me/submissions/d7661129-857b-42a7-ac21-4cdb23a5d4d9

import Mathlib
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Normed.Operator.Extend
import Definitions.Def_Q260K015

section
-- module Solutions.OAIQ075_KS.KadisonKastler_HilbertContractionFactor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.MatrixUnitSystem.initialHilbertSpace_complete _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.projectionOrbitClosure_complete _root_.OAI.Generator.tupleOrbitClosure_complete _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildNormalPart.cyclicSpace_complete _root_.OAI.HochschildNormalPart.normalVectors_complete _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.finiteReducingSpaceComplete _root_.OAI.KadisonKastler.generatedExtension_complete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instCompleteSpaceSubtypeMemSubmoduleComplexHilbertBasisInitialSpace _root_.OAI.KadisonKastler.partialSupportSpace_complete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.TracialCornerGeometry.baseSpace_complete _root_.OAI.KadisonSimilarity.TracialCornerGeometry.cornerSubmodule_complete _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.operatorRangeClosure_complete _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Contractive factorization through a Hilbert-space operator

This is the range-extension step used for contractive block completions in
the finite-nest distance argument. The factor is constructed on the closed
range and extended by zero on its orthogonal complement.
-/

namespace KadisonKastler

noncomputable section

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

omit [CompleteSpace F] in
theorem operatorClosedRangeMap_dense (S : E →L[ℂ] F) :
    DenseRange (operatorClosedRangeMap S) := by
  apply Metric.denseRange_iff.mpr
  intro z ε hε
  obtain ⟨x, hx⟩ := Metric.mem_closure_range_iff.mp z.property ε hε
  exact ⟨x, hx⟩

/-- Norm domination gives a contractive factor on the entire middle Hilbert
space, including when the original operator has nonclosed range. -/
theorem exists_contraction_factor (S : E →L[ℂ] F) (T : E →L[ℂ] G)
    (h : ∀ x, ‖T x‖ ≤ ‖S x‖) :
    ∃ C : F →L[ℂ] G, ‖C‖ ≤ 1 ∧ C.comp S = T := by
  let W := S.toLinearMap.range.topologicalClosure
  let s := operatorClosedRangeMap S
  let c : W →L[ℂ] G := T.toLinearMap.extendOfNorm s.toLinearMap
  have hs : DenseRange s := operatorClosedRangeMap_dense S
  have hn : ∀ x, ‖T.toLinearMap x‖ ≤ (1 : ℝ) * ‖s.toLinearMap x‖ := by
    intro x
    change ‖T x‖ ≤ 1 * ‖S x‖
    simpa only [one_mul] using h x
  have hc : ‖c‖ ≤ 1 := LinearMap.opNorm_extendOfNorm_le hs zero_le_one hn
  refine ⟨c.comp W.orthogonalProjectionOnto, ?_, ?_⟩
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul hc W.orthogonalProjectionOnto_norm_le (norm_nonneg W.orthogonalProjectionOnto)
        zero_le_one).trans_eq (mul_one 1))
  · apply ContinuousLinearMap.ext
    intro x
    change c (W.orthogonalProjectionOnto (S x)) = T x
    have hp : W.orthogonalProjectionOnto (S x) = s x :=
      W.orthogonalProjectionOnto_mem_subspace_eq_self (s x)
    rw [hp]
    exact LinearMap.extendOfNorm_eq hs ⟨1, hn⟩ x

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ContractionPolarFactor
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # A contractive polar factor for a Hilbert-space operator

Only the factor and its adjoint identity are needed for finite coefficient
duality. There is no closed-range or finite-dimensional hypothesis here.
-/

namespace KadisonKastler

open scoped InnerProductSpace

noncomputable section

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem contraction_adjoint_self_of_norm_eq (U : E →L[ℂ] F) (hU : ‖U‖ ≤ 1)
    (x : E) (hx : ‖U x‖ = ‖x‖) : U.adjoint (U x) = x := by
  have hd : operatorDefect U x = 0 := by
    apply norm_eq_zero.mp
    have h := norm_operatorDefect_sq U hU x
    rw [hx, sub_self] at h
    nlinarith [norm_nonneg (operatorDefect U x)]
  have h := congrArg (fun A : E →L[ℂ] E => A x) (operatorDefect_sq U hU)
  change operatorDefect U (operatorDefect U x) = x - U.adjoint (U x) at h
  rw [hd, map_zero] at h
  exact (sub_eq_zero.mp h.symm).symm

/-- The positive modulus has the same vector norms as the original operator. -/
theorem operator_modulus_norm (T : E →L[ℂ] F) (x : E) :
    ‖CFC.sqrt (T.adjoint.comp T) x‖ = ‖T x‖ := by
  let R := CFC.sqrt (T.adjoint.comp T)
  have hR : R.adjoint = R := (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
  have hsq : R.adjoint.comp R = T.adjoint.comp T := by
    rw [hR]
    exact CFC.sqrt_mul_sqrt_self _
      ((ContinuousLinearMap.nonneg_iff_isPositive _).mpr
        (ContinuousLinearMap.isPositive_adjoint_comp_self T))
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right,
    ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right]
  change (inner ℂ x ((R.adjoint.comp R) x)).re = _
  rw [hsq]
  rfl

/-- A contractive polar factor suffices for the exact trace-norm duality.
The second identity records that its adjoint recovers the positive modulus. -/
theorem exists_contractive_polar_factor (T : E →L[ℂ] F) :
    ∃ U : E →L[ℂ] F, ‖U‖ ≤ 1 ∧
      U.comp (CFC.sqrt (T.adjoint.comp T)) = T ∧
      U.adjoint.comp T = CFC.sqrt (T.adjoint.comp T) := by
  let R := CFC.sqrt (T.adjoint.comp T)
  obtain ⟨U, hU, hUT⟩ := exists_contraction_factor R T
    (fun x => (operator_modulus_norm T x).ge)
  refine ⟨U, hU, hUT, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  have hx : U (R x) = T x := congrArg (fun S : E →L[ℂ] F => S x) hUT
  rw [ContinuousLinearMap.comp_apply, ← hx]
  apply contraction_adjoint_self_of_norm_eq U hU
  rw [hx]
  exact (operator_modulus_norm T x).symm

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FiniteOperatorDuality
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

theorem exists_finite_polar_coefficients_oai (T : E →L[ℂ] E) :
    ∃ (n : ℕ) (x y : Fin n → E),
      operatorTracePairing T = finiteOperatorCoefficient x y ∧
      (∑ i, ‖x i‖ ^ 2) ≤ ‖operatorTracePairing T‖ ∧
      (∑ i, ‖y i‖ ^ 2) ≤ ‖operatorTracePairing T‖ := by
  obtain ⟨U, hU, hUT, hUadj⟩ := exists_contractive_polar_factor T
  let R := CFC.sqrt (T.adjoint.comp T)
  have hR : R.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive _).mp (CFC.sqrt_nonneg _)
  obtain ⟨n, a, ha⟩ := ContinuousLinearMap.isPositive_iff_eq_sum_rankOne.mp hR
  have hT : T = ∑ i, rankOne ℂ (U (a i)) (a i) := by
    rw [← hUT]
    change U * R = _
    rw [ha, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact comp_rankOne _ _ _
  have hp : operatorTracePairing T = finiteOperatorCoefficient a (fun i => U (a i)) := by
    apply ContinuousLinearMap.ext
    intro S
    rw [finiteOperatorCoefficient_apply, hT]
    simp only [operatorTracePairing_sum, operatorTracePairing_rankOne]
  have hadj : T.adjoint.comp U = R := by
    have h := congrArg ContinuousLinearMap.adjoint hUadj
    have hr : R.adjoint = R := (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
    change (U.adjoint.comp T).adjoint = R.adjoint at h
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, hr] at h
    exact h
  have heval : operatorTracePairing T U = (∑ i, ‖a i‖ ^ 2 : ℝ) := by
    rw [operatorTracePairing_apply, hadj, ha, ContinuousLinearMap.toLinearMap_sum, map_sum]
    simp only [trace_rankOne, inner_self_eq_norm_sq_to_K, Complex.ofReal_sum,
      Complex.ofReal_pow]
    rfl
  have hsum : (∑ i, ‖a i‖ ^ 2) ≤ ‖operatorTracePairing T‖ := by
    have h := (operatorTracePairing T).le_opNorm U
    rw [heval, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg ‖a i‖)] at h
    exact h.trans (mul_le_of_le_one_right (norm_nonneg _) hU)
  refine ⟨n, a, (fun i => U (a i)), hp, hsum, ?_⟩
  apply le_trans (Finset.sum_le_sum fun i _ => ?_) hsum
  have hn : ‖U (a i)‖ ≤ ‖a i‖ := (U.le_opNorm _).trans
    (mul_le_of_le_one_left (norm_nonneg _) hU)
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.exists_finite_polar_coefficients_oai.{u_1} := @OAI.KadisonKastler.exists_finite_polar_coefficients_oai.{u_1}
