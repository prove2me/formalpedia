-- Prove2me | solution 1 for OAI.KadisonKastler.multiplication_correction_of_quadratic_cochains
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T05:09:49.123451+00:00
-- url     : https://prove2.me/submissions/e2bd3713-5fd9-4643-9b71-1cd51812f465

import Mathlib
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_Q260K012
import Definitions.Def_Q260K013
import Definitions.Def_Q260K014

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CorrectionBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Bounds for correcting a transported multiplication

These are the inverse and composition estimates used in the UCP criterion
of §2 of *Universal strong Kadison–Kastler stability* (2026). The estimates are formulated for an explicitly supplied correction map.
-/

namespace KadisonKastler

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

/-- The inverse norm estimate for a linear equivalence within `η < 1`
of the identity. -/
theorem norm_inverse_le_of_close_to_id (L : E ≃ₗ[ℂ] E) {η : ℝ} (hη : η < 1)
    (hclose : ∀ x, ‖L x - x‖ ≤ η * ‖x‖) (x : E) :
    ‖L.symm x‖ ≤ (1 - η)⁻¹ * ‖x‖ := by
  have hpos : 0 < 1 - η := sub_pos.mpr hη
  apply (le_inv_mul_iff₀ hpos).mpr
  have hnorm := norm_le_norm_sub_add (L.symm x) x
  have herror := hclose (L.symm x)
  rw [L.apply_symm_apply, norm_sub_rev] at herror
  linarith

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompletelyBounded
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Matrix bounds for perturbation maps

All norms here are the C*-matrix norms, including for rectangular matrices.
The rectangular formulation records exactly the estimates needed for the
Haagerup product norm in the multiplication-correction argument.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] in
theorem rectangular_toCLM_mul {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A) :
    CStarMatrix.toCLM (X * Y) = (CStarMatrix.toCLM Y).comp (CStarMatrix.toCLM X) := by
  ext v i
  simp only [CStarMatrix.toCLM_apply, ContinuousLinearMap.comp_apply]
  exact congrFun (Matrix.vecMul_vecMul v X Y).symm i

/-- Submultiplicativity also holds for rectangular C*-matrices. -/
theorem rectangular_norm_mul_le {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A) :
    ‖X * Y‖ ≤ ‖X‖ * ‖Y‖ := by
  simp only [CStarMatrix.norm_def, rectangular_toCLM_mul]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans_eq (mul_comm _ _)

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
theorem matrix_map_sub (F G : A →ₗ[ℂ] B) {p q : ℕ}
    (X : CStarMatrix (Fin p) (Fin q) A) :
    CStarMatrix.mapₗ (F - G) X = CStarMatrix.mapₗ F X - CStarMatrix.mapₗ G X := by
  ext i j
  rfl

theorem inverse_completelyBoundedBy_of_close_to_id (L : A ≃ₗ[ℂ] A)
    {η : ℝ} (hη : η < 1)
    (hclose : CompletelyBoundedBy (L.toLinearMap - LinearMap.id) η) :
    CompletelyBoundedBy L.symm.toLinearMap ((1 - η)⁻¹) := by
  intro p q X
  apply norm_inverse_le_of_close_to_id (matrixLinearEquiv L p q) hη
  intro Y
  have hid : CStarMatrix.mapₗ (LinearMap.id : A →ₗ[ℂ] A) Y = Y := by
    ext i j
    rfl
  have h := hclose p q Y
  rw [matrix_map_sub, hid] at h
  exact h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixCorrection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Rectangular matrix estimates for multiplication correction

The inverse and corrected-map bounds used in the UCP criterion hold at
every rectangular C⋆-matrix size. The source and target may be represented
in a third ambient C⋆-algebra.
-/

namespace KadisonKastler

variable {A B C : Type*}
  [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
  [PartialOrder C] [StarOrderedRing C] in
/-- Entrywise application respects composition on rectangular matrices. -/
theorem matrix_map_comp (F : A →ₗ[ℂ] B) (G : B →ₗ[ℂ] C) {p q : ℕ}
    (X : CStarMatrix (Fin p) (Fin q) A) :
    CStarMatrix.mapₗ (G.comp F) X = CStarMatrix.mapₗ G (CStarMatrix.mapₗ F X) := by
  ext i j
  rfl

omit [PartialOrder A] [StarOrderedRing A] in
/-- The identity linear map acts identically at every rectangular level. -/
theorem matrix_map_id {p q : ℕ} (X : CStarMatrix (Fin p) (Fin q) A) :
    CStarMatrix.mapₗ (LinearMap.id : A →ₗ[ℂ] A) X = X := by
  ext i j
  rfl

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompleteLinearLimits
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Scalar and limit consequences of complete bounds -/

namespace KadisonKastler

noncomputable section

open Filter Topology

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- A sufficiently small completely bounded perturbation of the identity is
an algebraic linear equivalence, before any multiplicativity is considered. -/
theorem CompletelyBoundedBy.exists_equiv_add_id {D : A →ₗ[ℂ] A} {c : ℝ}
    (hc : 0 ≤ c) (hc1 : c < 1) (hD : CompletelyBoundedBy D c) :
    ∃ L : A ≃ₗ[ℂ] A, L.toLinearMap = LinearMap.id + D := by
  let T := hD.toContinuousLinearMap
  have hT : ‖T‖ < 1 :=
    (ContinuousLinearMap.opNorm_le_bound _ hc hD.apply_norm_le).trans_lt hc1
  have hunit : IsUnit (1 + T) := by
    have h := isUnit_one_sub_of_norm_lt_one (x := -T) (by simpa using hT)
    simpa only [sub_neg_eq_add] using h
  obtain ⟨U, hU⟩ := hunit
  refine ⟨(ContinuousLinearEquiv.unitsEquiv ℂ A U).toLinearEquiv, ?_⟩
  ext x
  change (U : A →L[ℂ] A) x = x + D x
  rw [hU]
  rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompleteLinearOperations
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Elementary operations on complete bounds -/

namespace KadisonKastler

noncomputable section

variable {A B C : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

theorem CompletelyBoundedBy.mono {F : A →ₗ[ℂ] B} {c d : ℝ}
    (hF : CompletelyBoundedBy F c) (hcd : c ≤ d) : CompletelyBoundedBy F d := by
  intro p q X
  exact (hF p q X).trans (mul_le_mul_of_nonneg_right hcd (norm_nonneg X))

theorem CompletelyBoundedBy.add {F G : A →ₗ[ℂ] B} {c d : ℝ}
    (hF : CompletelyBoundedBy F c) (hG : CompletelyBoundedBy G d) :
    CompletelyBoundedBy (F + G) (c + d) := by
  intro p q X
  rw [matrix_map_add, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hF p q X) (hG p q X))

theorem completelyBoundedBy_id : CompletelyBoundedBy (LinearMap.id : A →ₗ[ℂ] A) 1 := by
  intro p q X
  rw [matrix_map_id, one_mul]

theorem CompletelyBoundedBy.comp {F : A →ₗ[ℂ] B} {G : B →ₗ[ℂ] C} {c d : ℝ}
    (hG : CompletelyBoundedBy G d) (hF : CompletelyBoundedBy F c) (hd : 0 ≤ d) :
    CompletelyBoundedBy (G.comp F) (d * c) := by
  intro p q X
  rw [matrix_map_comp, mul_assoc]
  exact (hG p q _).trans (mul_le_mul_of_nonneg_left (hF p q X) hd)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompleteCorrectionLimit
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedStarGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The limit of summably many completely bounded corrections -/

namespace KadisonKastler

noncomputable section

open Filter Topology

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Complete estimates on the successive differences produce an actual
continuous linear limit and the same complete estimate on its displacement. -/
theorem exists_complete_correction_limit
    (L : ℕ → A →L[ℂ] A) (c : ℕ → ℝ)
    (hc : ∀ n, 0 ≤ c n) (hsum : Summable c)
    (hstep : ∀ n, CompletelyBoundedBy
      ((L (n + 1)).toLinearMap - (L n).toLinearMap) (c n)) :
    ∃ T : A →L[ℂ] A, Tendsto L atTop (𝓝 T) ∧
      CompletelyBoundedBy (T.toLinearMap - (L 0).toLinearMap) (∑' n, c n) := by
  have hnorm (n : ℕ) : ‖L (n + 1) - L n‖ ≤ c n := by
    apply ContinuousLinearMap.opNorm_le_bound _ (hc n)
    exact (hstep n).apply_norm_le
  have hdist : Summable (fun n => dist (L n) (L (n + 1))) := by
    apply hsum.of_nonneg_of_le (fun _ => dist_nonneg)
    intro n
    simpa only [dist_eq_norm, norm_sub_rev] using hnorm n
  obtain ⟨T, ht⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hdist)
  refine ⟨T, ht, ?_⟩
  intro p q X
  let V (n : ℕ) := CStarMatrix.mapₗ (L n).toLinearMap X
  let W := CStarMatrix.mapₗ T.toLinearMap X
  have hV : Tendsto V atTop (𝓝 W) := by
    apply CStarMatrix.ofMatrixL.continuous.tendsto _ |>.comp
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact (ContinuousLinearMap.apply ℂ A (X i j)).continuous.tendsto T |>.comp ht
  have hbound (n : ℕ) : dist (V n) (V (n + 1)) ≤ c n * ‖X‖ := by
    have h := hstep n p q X
    rw [matrix_map_sub, norm_sub_rev] at h
    simpa only [dist_eq_norm, V] using h
  have hsumX : Summable (fun n => c n * ‖X‖) := hsum.mul_right ‖X‖
  have h := dist_le_tsum_of_dist_le_of_tendsto₀
    (fun n => c n * ‖X‖) hbound hsumX hV
  rw [matrix_map_sub, norm_sub_rev]
  simpa only [dist_eq_norm, V, W, tsum_mul_right] using h

/-- Summably small corrections which asymptotically intertwine a product
converge to an exact invertible star-preserving intertwiner. -/
theorem correction_of_summable_steps
    (m : A →ₗ[ℂ] A →ₗ[ℂ] A) (L : ℕ → A →L[ℂ] A)
    (hzero : L 0 = ContinuousLinearMap.id ℂ A) (c d : ℕ → ℝ)
    (hc : ∀ n, 0 ≤ c n) (hsum : Summable c) (hsmall : (∑' n, c n) < 1)
    (hstep : ∀ n, CompletelyBoundedBy
      ((L (n + 1)).toLinearMap - (L n).toLinearMap) (c n))
    (hstar : ∀ n x, L n (star x) = star (L n x))
    (hd : Tendsto d atTop (𝓝 0))
    (hm : ∀ n x y, ‖L n (m x y) - L n x * L n y‖ ≤ d n * ‖x‖ * ‖y‖) :
    ∃ T : A ≃ₗ[ℂ] A,
      (∀ x y, T (m x y) = T x * T y) ∧
      (∀ x, T (star x) = star (T x)) ∧
      CompletelyBoundedBy (T.toLinearMap - LinearMap.id) (∑' n, c n) := by
  obtain ⟨F, hF, hcb⟩ := exists_complete_correction_limit L c hc hsum hstep
  have hclose : CompletelyBoundedBy (F.toLinearMap - LinearMap.id) (∑' n, c n) := by
    simpa only [hzero, ContinuousLinearMap.coe_id] using hcb
  have hsum0 : 0 ≤ ∑' n, c n := tsum_nonneg hc
  obtain ⟨T, hT⟩ := hclose.exists_equiv_add_id hsum0 hsmall
  have hTF : T.toLinearMap = F.toLinearMap := by rw [hT]; abel
  have ht (x : A) : Tendsto (fun n => L n x) atTop (𝓝 (F x)) :=
    (ContinuousLinearMap.apply ℂ A x).continuous.tendsto F |>.comp hF
  refine ⟨T, ?_, ?_, ?_⟩
  · intro x y
    have hres := (ht (m x y)).sub ((ht x).mul (ht y))
    have hz : Tendsto (fun n => ‖L n (m x y) - L n x * L n y‖) atTop (𝓝 0) := by
      apply squeeze_zero (fun _ => norm_nonneg _) (fun n => hm n x y)
      simpa only [zero_mul] using (hd.mul_const ‖x‖).mul_const ‖y‖
    have heq : F (m x y) - F x * F y = 0 := norm_eq_zero.mp
      (tendsto_nhds_unique hres.norm hz)
    change T.toLinearMap (m x y) = T.toLinearMap x * T.toLinearMap y
    rw [hTF]
    exact sub_eq_zero.mp heq
  · intro x
    have h : F (star x) = star (F x) := by
      apply tendsto_nhds_unique (ht (star x))
      simpa only [hstar] using (ht x).star
    have happ (z : A) : T z = F z := congrArg (fun R : A →ₗ[ℂ] A => R z) hTF
    rw [happ, happ]
    exact h
  · simpa only [hTF] using hclose

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompleteCorrectionProducts
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Uniform complete bounds on the successive correction products -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
theorem correctionProducts_increment (S : ℕ → A →L[ℂ] A) (n : ℕ) :
    (correctionProducts S (n + 1)).toLinearMap - (correctionProducts S n).toLinearMap =
      ((S n).toLinearMap - LinearMap.id).comp (correctionProducts S n).toLinearMap := by
  ext x
  simp

/-- The displacement is bounded by twice the sum of the step sizes. The
hypothesis on the partial sums closes the simultaneous bound by two. -/
theorem correctionProducts_complete_bounds (S : ℕ → A →L[ℂ] A) (r : ℕ → ℝ)
    (hr : ∀ n, 0 ≤ r n)
    (hsmall : ∀ n, 2 * ∑ i ∈ Finset.range n, r i ≤ 1)
    (hS : ∀ n, CompletelyBoundedBy ((S n).toLinearMap - LinearMap.id) (r n))
    (n : ℕ) :
    CompletelyBoundedBy ((correctionProducts S n).toLinearMap - LinearMap.id)
      (2 * ∑ i ∈ Finset.range n, r i) ∧
    CompletelyBoundedBy (correctionProducts S n).toLinearMap 2 := by
  induction n with
  | zero =>
    constructor
    · intro p q X
      simp only [correctionProducts_zero, ContinuousLinearMap.coe_id, sub_self,
        matrix_map_zero, Finset.range_zero, Finset.sum_empty, mul_zero, zero_mul, norm_zero, le_refl]
    · exact (completelyBoundedBy_id (A := A)).mono (by norm_num)
  | succ n ih =>
    have hdifference : CompletelyBoundedBy
        ((correctionProducts S (n + 1)).toLinearMap -
          (correctionProducts S n).toLinearMap) (2 * r n) := by
      rw [correctionProducts_increment]
      convert (hS n).comp ih.2 (hr n) using 1
      all_goals try with_reducible_and_instances rfl
      ring
    have heq : (correctionProducts S (n + 1)).toLinearMap - LinearMap.id =
        ((correctionProducts S (n + 1)).toLinearMap -
          (correctionProducts S n).toLinearMap) +
        ((correctionProducts S n).toLinearMap - LinearMap.id) := by abel
    have hdisplacement : CompletelyBoundedBy
        ((correctionProducts S (n + 1)).toLinearMap - LinearMap.id)
        (2 * ∑ i ∈ Finset.range (n + 1), r i) := by
      rw [heq]
      convert hdifference.add ih.1 using 1
      all_goals try with_reducible_and_instances rfl
      rw [Finset.sum_range_succ]
      ring
    refine ⟨hdisplacement, ?_⟩
    have heq' : (correctionProducts S (n + 1)).toLinearMap =
        LinearMap.id + ((correctionProducts S (n + 1)).toLinearMap - LinearMap.id) := by abel
    rw [heq']
    exact ((completelyBoundedBy_id (A := A)).add hdisplacement).mono (by linarith [hsmall (n+1)])

omit [PartialOrder A] [StarOrderedRing A] in
/-- The products preserve the involution if each factor does. -/
theorem correctionProducts_star (S : ℕ → A →L[ℂ] A)
    (hS : ∀ n x, S n (star x) = star (S n x)) (n : ℕ) (x : A) :
    correctionProducts S n (star x) = star (correctionProducts S n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change S n (correctionProducts S n (star x)) = star (S n (correctionProducts S n x))
    rw [ih, hS]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_GeometricCorrectionScale
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # The summable error scale for multiplication correction -/

namespace KadisonKastler

open Filter Topology

noncomputable section

theorem correctionScale_succ (q : ℝ) (n : ℕ) :
    correctionScale q (n + 1) = correctionScale q n / 2 := by
  simp only [correctionScale, pow_succ]
  ring

theorem correctionScale_nonneg {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    0 ≤ correctionScale q n := by
  unfold correctionScale
  positivity

theorem correctionScale_le {q : ℝ} (hq : 0 ≤ q) (n : ℕ) : correctionScale q n ≤ q := by
  exact (mul_le_mul_of_nonneg_left
    (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)) hq).trans_eq
    (mul_one q)

theorem correctionScale_summable (q : ℝ) : Summable (correctionScale q) :=
  (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) < 1)).mul_left q

theorem correctionScale_tsum (q : ℝ) : ∑' n, correctionScale q n = 2 * q := by
  change (∑' n : ℕ, q * (1/2 : ℝ)^n) = 2*q
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
  · ring
  · norm_num

theorem correctionScale_tendsto (q : ℝ) : Tendsto (correctionScale q) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => q * (1/2 : ℝ)^n) atTop (𝓝 0)
  simpa only [mul_zero] using tendsto_const_nhds.mul
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1))

theorem correctionScale_partial_sum {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    ∑ i ∈ Finset.range n, correctionScale q i ≤ 2 * q := by
  rw [← correctionScale_tsum]
  exact (correctionScale_summable q).sum_le_tsum _
    (fun i _ => correctionScale_nonneg hq i)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MultiplicationNewtonStep
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CompletelyBoundedBy.toContinuousLinearMap_apply _root_.OAI.KadisonKastler.HaagerupBound.toContinuousBilinear_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # One quadratic step in correction of multiplication

These are the concrete matrix identities used in the perturbation iteration.
The choice of a correcting cochain is a separate construction.
-/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

/-- The coboundary formula is unchanged at every rectangular matrix level. -/
theorem bilinearProduct_linearCoboundary (D : A →ₗ[ℂ] A) {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A) :
    bilinearProduct (linearCoboundary D) X Y =
      X * CStarMatrix.mapₗ D Y - CStarMatrix.mapₗ D (X * Y) +
        CStarMatrix.mapₗ D X * Y := by
  ext i j
  simp [CStarMatrix.mul_apply, map_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]

theorem bilinearProduct_conjugated (L : A ≃ₗ[ℂ] A)
    (m : A →ₗ[ℂ] A →ₗ[ℂ] A) {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A) :
    bilinearProduct (conjugatedBilinear L m) X Y =
      CStarMatrix.mapₗ L.toLinearMap
        (bilinearProduct m (CStarMatrix.mapₗ L.symm.toLinearMap X)
          (CStarMatrix.mapₗ L.symm.toLinearMap Y)) := by
  ext i j
  simp [map_sum]

theorem conjugatedBilinear_assoc (L : A ≃ₗ[ℂ] A)
    (m : A →ₗ[ℂ] A →ₗ[ℂ] A) (hm : ∀ x y z, m (m x y) z = m x (m y z)) :
    ∀ x y z, conjugatedBilinear L m (conjugatedBilinear L m x y) z =
      conjugatedBilinear L m x (conjugatedBilinear L m y z) := by
  intro x y z
  simp only [conjugatedBilinear_apply, L.symm_apply_apply, hm]

theorem conjugatedBilinear_star (L : A ≃ₗ[ℂ] A)
    (hL : ∀ x, L (star x) = star (L x))
    (m : A →ₗ[ℂ] A →ₗ[ℂ] A)
    (hm : ∀ x y, star (m x y) = m (star y) (star x)) :
    ∀ x y, star (conjugatedBilinear L m x y) =
      conjugatedBilinear L m (star y) (star x) := by
  have hinv (x : A) : L.symm (star x) = star (L.symm x) := by
    apply L.injective
    simp [hL]
  intro x y
  simp only [conjugatedBilinear_apply, ← hL, hm, hinv]

/-- Exact error before conjugating by the near-identity correction. -/
theorem matrix_newton_residual (m : A →ₗ[ℂ] A →ₗ[ℂ] A) (D : A →ₗ[ℂ] A)
    {p r q : ℕ} (X : CStarMatrix (Fin p) (Fin r) A)
    (Y : CStarMatrix (Fin r) (Fin q) A) :
    CStarMatrix.mapₗ (LinearMap.id + D) (bilinearProduct m X Y) -
      CStarMatrix.mapₗ (LinearMap.id + D) X * CStarMatrix.mapₗ (LinearMap.id + D) Y =
    bilinearProduct (m - LinearMap.mul ℂ A - linearCoboundary D) X Y +
      CStarMatrix.mapₗ D (bilinearProduct (m - LinearMap.mul ℂ A) X Y) -
      CStarMatrix.mapₗ D X * CStarMatrix.mapₗ D Y := by
  have hadd {p q : ℕ} (Z : CStarMatrix (Fin p) (Fin q) A) :
      CStarMatrix.mapₗ (LinearMap.id + D) Z = Z + CStarMatrix.mapₗ D Z := by
    ext i j
    rfl
  simp only [hadd, bilinearProduct_sub, bilinearProduct_mul,
    bilinearProduct_linearCoboundary, map_sub, CStarMatrix.add_mul, CStarMatrix.mul_add]
  abel

variable [PartialOrder A] [StarOrderedRing A]

/-- The new error is the uncorrected cohomology error plus two quadratic terms. -/
theorem matrix_newton_residual_bound (m : A →ₗ[ℂ] A →ₗ[ℂ] A) (D : A →ₗ[ℂ] A)
    {c q r : ℝ} (hc : 0 ≤ c)
    (hD : CompletelyBoundedBy D c)
    (hm : HaagerupBound (m - LinearMap.mul ℂ A) q)
    (hres : HaagerupBound (m - LinearMap.mul ℂ A - linearCoboundary D) r)
    {p s t : ℕ} (X : CStarMatrix (Fin p) (Fin s) A)
    (Y : CStarMatrix (Fin s) (Fin t) A) :
    ‖CStarMatrix.mapₗ (LinearMap.id + D) (bilinearProduct m X Y) -
      CStarMatrix.mapₗ (LinearMap.id + D) X * CStarMatrix.mapₗ (LinearMap.id + D) Y‖ ≤
      (r + c * q + c ^ 2) * ‖X‖ * ‖Y‖ := by
  rw [matrix_newton_residual]
  calc
    _ ≤ ‖bilinearProduct (m - LinearMap.mul ℂ A - linearCoboundary D) X Y‖ +
        ‖CStarMatrix.mapₗ D (bilinearProduct (m - LinearMap.mul ℂ A) X Y)‖ +
        ‖CStarMatrix.mapₗ D X * CStarMatrix.mapₗ D Y‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ r * ‖X‖ * ‖Y‖ + c * (q * ‖X‖ * ‖Y‖) +
        (c * ‖X‖) * (c * ‖Y‖) := by
      apply add_le_add
      · apply add_le_add (hres p s t X Y)
        exact (hD p t _).trans (mul_le_mul_of_nonneg_left (hm p s t X Y) hc)
      · exact (rectangular_norm_mul_le _ _).trans
          (mul_le_mul (hD p s X) (hD s t Y) (norm_nonneg _) (mul_nonneg hc (norm_nonneg X)))
    _ = _ := by ring

/-- After changing coordinates, the new multiplication has the same quadratic
bound divided by the two inverse-coordinate bounds. -/
theorem conjugatedBilinear_defect_bound
    (m : A →ₗ[ℂ] A →ₗ[ℂ] A) (D : A →ₗ[ℂ] A) (L : A ≃ₗ[ℂ] A)
    (hL : L.toLinearMap = LinearMap.id + D) {c q r : ℝ}
    (hc : 0 ≤ c) (hc1 : c < 1) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hD : CompletelyBoundedBy D c)
    (hm : HaagerupBound (m - LinearMap.mul ℂ A) q)
    (hres : HaagerupBound (m - LinearMap.mul ℂ A - linearCoboundary D) r) :
    HaagerupBound (conjugatedBilinear L m - LinearMap.mul ℂ A)
      ((r + c * q + c ^ 2) / (1 - c) ^ 2) := by
  have hclose : CompletelyBoundedBy (L.toLinearMap - LinearMap.id) c := by
    simpa only [hL, add_sub_cancel_left] using hD
  have hinv := inverse_completelyBoundedBy_of_close_to_id L hc1 hclose
  have hK : 0 ≤ r + c * q + c ^ 2 := by positivity
  have hinv0 : 0 ≤ (1 - c)⁻¹ := inv_nonneg.mpr (sub_pos.mpr hc1).le
  intro p s t X Y
  let U := CStarMatrix.mapₗ L.symm.toLinearMap X
  let V := CStarMatrix.mapₗ L.symm.toLinearMap Y
  have hU : CStarMatrix.mapₗ L.toLinearMap U = X := by
    ext i j
    exact L.apply_symm_apply _
  have hV : CStarMatrix.mapₗ L.toLinearMap V = Y := by
    ext i j
    exact L.apply_symm_apply _
  have herror : bilinearProduct (conjugatedBilinear L m - LinearMap.mul ℂ A) X Y =
      CStarMatrix.mapₗ (LinearMap.id + D) (bilinearProduct m U V) -
        CStarMatrix.mapₗ (LinearMap.id + D) U * CStarMatrix.mapₗ (LinearMap.id + D) V := by
    rw [bilinearProduct_sub, bilinearProduct_mul, bilinearProduct_conjugated]
    rw [← hL, hU, hV]
  rw [herror]
  calc
    _ ≤ (r + c * q + c ^ 2) * ‖U‖ * ‖V‖ :=
      matrix_newton_residual_bound m D hc hD hm hres U V
    _ ≤ (r + c * q + c ^ 2) * ((1 - c)⁻¹ * ‖X‖) * ((1 - c)⁻¹ * ‖Y‖) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hinv p s X) hK
      · exact hinv s t Y
      · exact norm_nonneg V
      · positivity
    _ = ((r + c * q + c ^ 2) / (1 - c) ^ 2) * ‖X‖ * ‖Y‖ := by
      field_simp

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_QuadraticMultiplicationCorrection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.spatialHilbert_nontrivial _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Quantitative quadratic correction of an associative multiplication -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem quadratic_correction_half_bound {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1 / 11) :
    (4 * q ^ 2) / (1 - q) ^ 2 ≤ q / 2 := by
  have hden : 0 < 1 - q := by linarith
  apply (div_le_iff₀ (sq_pos_of_pos hden)).mpr
  have hpoly : 0 ≤ 1 - 10 * q + q ^ 2 := by nlinarith [sq_nonneg q]
  nlinarith [mul_nonneg hq hpoly]

/-- A cochain with unit complete bound and quadratic coboundary error gives
an invertible, star-preserving correction which halves the error. -/
theorem quadratic_multiplication_half_step
    (m : A →ₗ[ℂ] A →ₗ[ℂ] A)
    (hm : ∀ x y z, m (m x y) z = m x (m y z))
    (hmstar : ∀ x y, star (m x y) = m (star y) (star x))
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1 / 11)
    (hbound : HaagerupBound (m - LinearMap.mul ℂ A) q)
    (D : A →ₗ[ℂ] A) (hD : CompletelyBoundedBy D q)
    (hDstar : ∀ x, D (star x) = star (D x))
    (hres : HaagerupBound (m - LinearMap.mul ℂ A - linearCoboundary D) (2 * q ^ 2)) :
    ∃ L : A ≃ₗ[ℂ] A,
      L.toLinearMap = LinearMap.id + D ∧
      (∀ x, L (star x) = star (L x)) ∧
      CompletelyBoundedBy (L.toLinearMap - LinearMap.id) q ∧
      (∀ x y z, conjugatedBilinear L m (conjugatedBilinear L m x y) z =
        conjugatedBilinear L m x (conjugatedBilinear L m y z)) ∧
      (∀ x y, star (conjugatedBilinear L m x y) =
        conjugatedBilinear L m (star y) (star x)) ∧
      HaagerupBound (conjugatedBilinear L m - LinearMap.mul ℂ A) (q / 2) := by
  have hq_lt : q < 1 := by linarith
  obtain ⟨L, hL⟩ := hD.exists_equiv_add_id hq hq_lt
  have hLstar (x : A) : L (star x) = star (L x) := by
    change L.toLinearMap (star x) = star (L.toLinearMap x)
    simp only [hL, LinearMap.add_apply, LinearMap.id_apply, hDstar, star_add]
  refine ⟨L, hL, hLstar, ?_, conjugatedBilinear_assoc L m hm,
    conjugatedBilinear_star L hLstar m hmstar, ?_⟩
  · simpa only [hL, add_sub_cancel_left] using hD
  · have hnew := conjugatedBilinear_defect_bound m D L hL hq hq_lt hq
      (by positivity) hD hbound hres
    have hconstant : (2 * q ^ 2 + q * q + q ^ 2) / (1 - q) ^ 2 ≤ q / 2 := by
      convert quadratic_correction_half_bound hq hq1 using 1
      all_goals try with_reducible_and_instances rfl
      ring
    intro p r s X Y
    exact (hnew p r s X Y).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hconstant (norm_nonneg X)) (norm_nonneg Y))

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MultiplicationCorrectionSequence
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # Iterating the quadratic cochain correction

A cochain with unit complete bound and quadratic coboundary remainder
produces successive associative multiplications whose defects halve.
-/

namespace KadisonKastler

noncomputable section

variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {A}

theorem exists_halving_multiplication_sequence (hsolver : QuadraticCochainSolver A)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1/11) (m : SmallAssociativeProduct A q) :
    ∃ P : (n : ℕ) → SmallAssociativeProduct A (correctionScale q n),
      (P 0).mul = m.mul ∧ ∃ U : ℕ → A ≃ₗ[ℂ] A,
        (∀ n x, U n (star x) = star (U n x)) ∧
        (∀ n, CompletelyBoundedBy ((U n).toLinearMap - LinearMap.id) (correctionScale q n)) ∧
        (∀ n, (P (n+1)).mul = conjugatedBilinear (U n) (P n).mul) := by
  have move (n : ℕ) (p : SmallAssociativeProduct A (correctionScale q n)) :
      ∃ L : A ≃ₗ[ℂ] A,
        (∀ x, L (star x) = star (L x)) ∧
        CompletelyBoundedBy (L.toLinearMap - LinearMap.id) (correctionScale q n) ∧
        (∀ x y z, conjugatedBilinear L p.mul (conjugatedBilinear L p.mul x y) z =
          conjugatedBilinear L p.mul x (conjugatedBilinear L p.mul y z)) ∧
        (∀ x y, star (conjugatedBilinear L p.mul x y) =
          conjugatedBilinear L p.mul (star y) (star x)) ∧
        HaagerupBound (conjugatedBilinear L p.mul - LinearMap.mul ℂ A)
          (correctionScale q (n+1)) := by
    have hn := correctionScale_nonneg hq n
    have hn1 := (correctionScale_le hq n).trans hq1
    obtain ⟨D, hD, hDs, hres⟩ := hsolver _ hn hn1 p
    obtain ⟨L, _, hLs, hLc, hLa, hLst, hLb⟩ :=
      quadratic_multiplication_half_step p.mul p.assoc p.star_mul hn hn1 p.bound D hD hDs hres
    exact ⟨L, hLs, hLc, hLa, hLst, by simpa only [correctionScale_succ] using hLb⟩
  let next (n : ℕ) (p : SmallAssociativeProduct A (correctionScale q n)) :
      SmallAssociativeProduct A (correctionScale q (n+1)) :=
    { mul := conjugatedBilinear (Classical.choose (move n p)) p.mul
      assoc := (Classical.choose_spec (move n p)).2.2.1
      star_mul := (Classical.choose_spec (move n p)).2.2.2.1
      bound := (Classical.choose_spec (move n p)).2.2.2.2 }
  let initial : SmallAssociativeProduct A (correctionScale q 0) :=
    { mul := m.mul
      assoc := m.assoc
      star_mul := m.star_mul
      bound := by simpa only [correctionScale_zero] using m.bound }
  let P : (n : ℕ) → SmallAssociativeProduct A (correctionScale q n) :=
    fun n => Nat.rec initial (fun n p => next n p) n
  let U (n : ℕ) := Classical.choose (move n (P n))
  refine ⟨P, rfl, U, ?_, ?_, ?_⟩
  · intro n
    exact (Classical.choose_spec (move n (P n))).1
  · intro n
    exact (Classical.choose_spec (move n (P n))).2.1
  · intro n
    rfl

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MultiplicationCorrectionFromCochains
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.HaagerupBound.toContinuousBilinear_apply _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-! # From the quadratic cochain estimate to multiplication correction

The analytic cochain selector is kept as an explicit argument. The product
iteration and its complete bound are proved here, not postulated.
-/

namespace KadisonKastler

noncomputable section

open Filter Topology

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem multiplication_correction_of_quadratic_cochains_oai
    (hsolver : QuadraticCochainSolver A)
    (m : A →ₗ[ℂ] A →ₗ[ℂ] A)
    (hm : ∀ x y z, m (m x y) z = m x (m y z))
    (hms : ∀ x y, star (m x y) = m (star y) (star x))
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1/11)
    (hb : HaagerupBound (m - LinearMap.mul ℂ A) q) :
    ∃ T : A ≃ₗ[ℂ] A, (∀ x y, T (m x y) = T x * T y) ∧
      (∀ x, T (star x) = star (T x)) ∧
      CompletelyBoundedBy (T.toLinearMap - LinearMap.id) (4 * q) := by
  let initial : SmallAssociativeProduct A q := ⟨m, hm, hms, hb⟩
  obtain ⟨P, hP0, U, hUs, hUb, hnext⟩ :=
    exists_halving_multiplication_sequence hsolver hq hq1 initial
  have hUbound (n : ℕ) : CompletelyBoundedBy (U n).toLinearMap
      (1 + correctionScale q n) := by
    have he : (U n).toLinearMap = LinearMap.id + ((U n).toLinearMap - LinearMap.id) := by abel
    rw [he]
    exact (completelyBoundedBy_id (A := A)).add (hUb n)
  let S (n : ℕ) : A →L[ℂ] A := (hUbound n).toContinuousLinearMap
  have hSU (n : ℕ) (x : A) : S n x = U n x := rfl
  have hScb (n : ℕ) : CompletelyBoundedBy ((S n).toLinearMap - LinearMap.id)
      (correctionScale q n) := hUb n
  have hsmall (n : ℕ) : 2 * ∑ i ∈ Finset.range n, correctionScale q i ≤ 1 := by
    have h := correctionScale_partial_sum hq n
    linarith
  have hLb (n : ℕ) := correctionProducts_complete_bounds S (correctionScale q)
    (correctionScale_nonneg hq) hsmall hScb n
  have hintertwine (n : ℕ) (x y : A) :
      correctionProducts S n (m x y) =
        (P n).mul (correctionProducts S n x) (correctionProducts S n y) := by
    induction n with
    | zero =>
      change m x y = (P 0).mul x y
      exact congrArg (fun f : A →ₗ[ℂ] A →ₗ[ℂ] A => f x y) hP0.symm
    | succ n ih =>
      simp only [correctionProducts_succ, ContinuousLinearMap.comp_apply, ih, hnext,
        conjugatedBilinear_apply, hSU, (U n).symm_apply_apply]
  have herror (n : ℕ) (x y : A) :
      ‖correctionProducts S n (m x y) -
          correctionProducts S n x * correctionProducts S n y‖ ≤
        (4 * correctionScale q n) * ‖x‖ * ‖y‖ := by
    rw [hintertwine]
    have h := (P n).bound.apply_norm_le (correctionProducts S n x) (correctionProducts S n y)
    change ‖(P n).mul (correctionProducts S n x) (correctionProducts S n y) -
      correctionProducts S n x * correctionProducts S n y‖ ≤ _ at h
    calc
      _ ≤ correctionScale q n * ‖correctionProducts S n x‖ * ‖correctionProducts S n y‖ := h
      _ ≤ correctionScale q n * (2 * ‖x‖) * (2 * ‖y‖) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left ((hLb n).2.apply_norm_le x) (correctionScale_nonneg hq n)
        · exact (hLb n).2.apply_norm_le y
        · exact norm_nonneg _
        · exact mul_nonneg (correctionScale_nonneg hq n) (mul_nonneg (by norm_num) (norm_nonneg x))
      _ = _ := by ring
  have hcsum : Summable (fun n => 2 * correctionScale q n) :=
    (correctionScale_summable q).mul_left 2
  have hctotal : (∑' n, 2 * correctionScale q n) = 4 * q := by
    rw [tsum_mul_left, correctionScale_tsum]
    ring
  have hcsmall : (∑' n, 2 * correctionScale q n) < 1 := by
    rw [hctotal]
    linarith
  have hLstep (n : ℕ) : CompletelyBoundedBy
      ((correctionProducts S (n+1)).toLinearMap - (correctionProducts S n).toLinearMap)
      (2 * correctionScale q n) := by
    rw [correctionProducts_increment]
    convert (hScb n).comp (hLb n).2 (correctionScale_nonneg hq n) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  obtain ⟨T, hTm, hTs, hTc⟩ := correction_of_summable_steps m (correctionProducts S)
    (correctionProducts_zero S) (fun n => 2 * correctionScale q n)
    (fun n => 4 * correctionScale q n)
    (fun n => mul_nonneg (by norm_num) (correctionScale_nonneg hq n)) hcsum hcsmall hLstep
    (correctionProducts_star S (fun n x => by simpa only [hSU] using hUs n x))
    (by simpa only [mul_zero] using (correctionScale_tendsto q).const_mul 4) herror
  exact ⟨T, hTm, hTs, by simpa only [hctotal] using hTc⟩

end

end KadisonKastler

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonKastler.multiplication_correction_of_quadratic_cochains_oai.{u_1} := @OAI.KadisonKastler.multiplication_correction_of_quadratic_cochains_oai.{u_1}
