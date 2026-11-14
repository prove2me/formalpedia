-- Prove2me | solution 1 for OAI.KadisonKastler.concrete_ucp_starEquiv_of_published
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:06:11.640843+00:00
-- url     : https://prove2.me/submissions/45c91c65-dea0-4726-b134-249ff8fac5d6

import Mathlib
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Algebra.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Matrix.Composition
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_StrongKadisonKastler
import Definitions.Def_Q260K015
import Definitions.Def_Q260K018
import Definitions.Def_Q260K021

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Transport
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Transport and correction of multiplication

These are the algebraic and norm estimates in the UCP criterion of §2 of
*Universal strong Kadison–Kastler stability* (2026). No perturbation theorem
is assumed here. If a linear equivalence correcting the transported product
is supplied, its composition with the original map gives an actual algebra
equivalence.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [NormedRing A] [NormedAlgebra ℂ A]
  [NormedRing B] [NormedAlgebra ℂ B]

theorem transportedMul_assoc (F : A ≃ₗ[ℂ] B) (x y z : A) :
    transportedMul F (transportedMul F x y) z =
      transportedMul F x (transportedMul F y z) := by
  apply F.injective
  simp only [map_transportedMul, mul_assoc]

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CorrectionBounds
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

/-- The inverse displacement estimate corresponding to a near-identity
linear equivalence. -/
theorem norm_inverse_sub_le_of_close_to_id (L : E ≃ₗ[ℂ] E) {η : ℝ}
    (hη₀ : 0 ≤ η) (hη : η < 1) (hclose : ∀ x, ‖L x - x‖ ≤ η * ‖x‖)
    (x : E) : ‖L.symm x - x‖ ≤ (η / (1 - η)) * ‖x‖ := by
  have herror := hclose (L.symm x)
  rw [L.apply_symm_apply, norm_sub_rev] at herror
  calc
    ‖L.symm x - x‖ ≤ η * ‖L.symm x‖ := herror
    _ ≤ η * ((1 - η)⁻¹ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (norm_inverse_le_of_close_to_id L hη hclose x) hη₀
    _ = (η / (1 - η)) * ‖x‖ := by rw [div_eq_mul_inv, mul_assoc]

/-- Composing a contraction with an inverse correction adds at most the
inverse displacement to the original comparison error. -/
theorem norm_correctedMap_sub_le (L : E ≃ₗ[ℂ] E) (F ρ : E →ₗ[ℂ] G)
    {η e : ℝ} (hη₀ : 0 ≤ η) (hη : η < 1)
    (hL : ∀ x, ‖L x - x‖ ≤ η * ‖x‖)
    (hF : ∀ x, ‖F x‖ ≤ ‖x‖) (hclose : ∀ x, ‖F x - ρ x‖ ≤ e * ‖x‖)
    (x : E) : ‖F (L.symm x) - ρ x‖ ≤ (e + η / (1 - η)) * ‖x‖ := by
  calc
    ‖F (L.symm x) - ρ x‖ ≤ ‖F (L.symm x) - F x‖ + ‖F x - ρ x‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ‖L.symm x - x‖ + e * ‖x‖ := by
      apply add_le_add _ (hclose x)
      simpa only [map_sub] using hF (L.symm x - x)
    _ ≤ (η / (1 - η)) * ‖x‖ + e * ‖x‖ :=
      add_le_add (norm_inverse_sub_le_of_close_to_id L hη₀ hη hL x) le_rfl
    _ = (e + η / (1 - η)) * ‖x‖ := by ring

/-- The correction parameter furnished by the multiplication estimate is
small enough for inversion at the manuscript's UCP tolerance. -/
theorem ucp_correction_parameter_bounds {e : ℝ} (he : 0 ≤ e) (he₁ : e < 1 / 1000) :
    0 ≤ 30 * e / (1 - e) ∧ 30 * e / (1 - e) < 1 := by
  have hden : 0 < 1 - e := by linarith
  constructor
  · exact div_nonneg (mul_nonneg (by norm_num) he) hden.le
  · apply (div_lt_one hden).mpr
    linarith

/-- The numerical estimate in the UCP criterion:
`e + η / (1 - η) ≤ 32e` for `η = 30e / (1 - e)`. -/
theorem ucp_correction_constant_le {e : ℝ} (he : 0 ≤ e) (he₁ : e < 1 / 1000) :
    e + (30 * e / (1 - e)) / (1 - 30 * e / (1 - e)) ≤ 32 * e := by
  have hden : 0 < 1 - e := by linarith
  have hden₃₁ : 0 < 1 - 31 * e := by linarith
  have hη := (ucp_correction_parameter_bounds he he₁).2
  have hdenη : 0 < 1 - 30 * e / (1 - e) := sub_pos.mpr hη
  have hid : (30 * e / (1 - e)) / (1 - 30 * e / (1 - e)) =
      30 * e / (1 - 31 * e) := by
    field_simp [hden.ne', hden₃₁.ne', hdenη.ne']
    ring
  rw [hid]
  have hbound : 30 * e / (1 - 31 * e) ≤ 31 * e := by
    apply (div_le_iff₀ hden₃₁).mpr
    have hproduct : 0 ≤ e * (1 - 961 * e) :=
      mul_nonneg he (by linarith)
    nlinarith
  linarith

/-- The corrected map is within `32e` of the comparison map under the
explicit correction bound appearing in the UCP criterion. -/
theorem norm_correctedMap_sub_le_thirty_two_mul
    (L : E ≃ₗ[ℂ] E) (F ρ : E →ₗ[ℂ] G) {e : ℝ}
    (he : 0 ≤ e) (he₁ : e < 1 / 1000)
    (hL : ∀ x, ‖L x - x‖ ≤ (30 * e / (1 - e)) * ‖x‖)
    (hF : ∀ x, ‖F x‖ ≤ ‖x‖) (hclose : ∀ x, ‖F x - ρ x‖ ≤ e * ‖x‖)
    (x : E) : ‖F (L.symm x) - ρ x‖ ≤ (32 * e) * ‖x‖ := by
  obtain ⟨hη₀, hη⟩ := ucp_correction_parameter_bounds he he₁
  exact (norm_correctedMap_sub_le L F ρ hη₀ hη hL hF hclose x).trans
    (mul_le_mul_of_nonneg_right (ucp_correction_constant_le he he₁) (norm_nonneg x))

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompletelyBounded
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.CompletelyBoundedBy.toContinuousLinearMap_apply _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
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

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
theorem matrix_map_mul (ρ : A →ₐ[ℂ] B) {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A) :
    CStarMatrix.mapₗ ρ.toLinearMap (X * Y) =
      CStarMatrix.mapₗ ρ.toLinearMap X * CStarMatrix.mapₗ ρ.toLinearMap Y := by
  ext i k
  simp [CStarMatrix.mul_apply, CStarMatrix.mapₗ_apply, CStarMatrix.map_apply, map_sum]

/-- The multiplicative defect estimate at all rectangular matrix sizes.
This is the estimate used before transporting multiplication through `F`. -/
theorem matrix_multiplicative_defect_le
    (ρ : A →ₐ[ℂ] B) (F : A →ₗ[ℂ] B) {e : ℝ} (he : 0 ≤ e)
    (hρ : CompletelyIsometric ρ.toLinearMap)
    (hF : CompletelyBoundedBy F 1)
    (hclose : CompletelyBoundedBy (F - ρ.toLinearMap) e)
    {p r q : ℕ} (X : CStarMatrix (Fin p) (Fin r) A)
    (Y : CStarMatrix (Fin r) (Fin q) A) :
    ‖CStarMatrix.mapₗ F (X * Y) - CStarMatrix.mapₗ F X * CStarMatrix.mapₗ F Y‖ ≤
      3 * e * ‖X‖ * ‖Y‖ := by
  have hclose' {m n : ℕ} (Z : CStarMatrix (Fin m) (Fin n) A) :
      ‖CStarMatrix.mapₗ F Z - CStarMatrix.mapₗ ρ.toLinearMap Z‖ ≤ e * ‖Z‖ := by
    simpa only [matrix_map_sub] using hclose m n Z
  have hexpand :
      CStarMatrix.mapₗ F (X * Y) - CStarMatrix.mapₗ F X * CStarMatrix.mapₗ F Y =
      (CStarMatrix.mapₗ F (X * Y) - CStarMatrix.mapₗ ρ.toLinearMap (X * Y)) +
      (CStarMatrix.mapₗ ρ.toLinearMap X - CStarMatrix.mapₗ F X) *
        CStarMatrix.mapₗ ρ.toLinearMap Y +
      CStarMatrix.mapₗ F X *
        (CStarMatrix.mapₗ ρ.toLinearMap Y - CStarMatrix.mapₗ F Y) := by
    rw [matrix_map_mul]
    ext i k
    simp only [CStarMatrix.add_apply, CStarMatrix.sub_apply, CStarMatrix.mul_apply,
      sub_mul, mul_sub, Finset.sum_sub_distrib]
    abel
  rw [hexpand]
  calc
    _ ≤ ‖CStarMatrix.mapₗ F (X * Y) - CStarMatrix.mapₗ ρ.toLinearMap (X * Y)‖ +
        ‖(CStarMatrix.mapₗ ρ.toLinearMap X - CStarMatrix.mapₗ F X) *
          CStarMatrix.mapₗ ρ.toLinearMap Y‖ +
        ‖CStarMatrix.mapₗ F X *
          (CStarMatrix.mapₗ ρ.toLinearMap Y - CStarMatrix.mapₗ F Y)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ e * (‖X‖ * ‖Y‖) + (e * ‖X‖) * ‖Y‖ + ‖X‖ * (e * ‖Y‖) := by
      apply add_le_add
      · apply add_le_add
        · exact (hclose' _).trans (mul_le_mul_of_nonneg_left
            (rectangular_norm_mul_le X Y) he)
        · refine (rectangular_norm_mul_le _ _).trans ?_
          rw [hρ r q Y, norm_sub_rev]
          exact mul_le_mul_of_nonneg_right (hclose' X) (norm_nonneg Y)
      · refine (rectangular_norm_mul_le _ _).trans ?_
        rw [norm_sub_rev]
        exact mul_le_mul (by simpa using hF p r X) (hclose' Y)
          (norm_nonneg _) (norm_nonneg _)
    _ = 3 * e * ‖X‖ * ‖Y‖ := by ring

theorem transportedProductBound_of_defect (F : A ≃ₗ[ℂ] B) {K c : ℝ}
    (hK : 0 ≤ K) (hinv : CompletelyBoundedBy F.symm.toLinearMap K)
    (hdefect : ∀ (p r q : ℕ) (X : CStarMatrix (Fin p) (Fin r) A)
        (Y : CStarMatrix (Fin r) (Fin q) A),
      ‖CStarMatrix.mapₗ F.toLinearMap (X * Y) -
          CStarMatrix.mapₗ F.toLinearMap X * CStarMatrix.mapₗ F.toLinearMap Y‖ ≤
        c * ‖X‖ * ‖Y‖) :
    TransportedProductBound F (K * c) := by
  intro p r q X Y
  have hid : CStarMatrix.mapₗ F.symm.toLinearMap
      (CStarMatrix.mapₗ F.toLinearMap (X * Y)) = X * Y := by
    ext i j
    exact F.symm_apply_apply _
  rw [← hid, ← map_sub]
  exact (hinv p q _).trans (by
    rw [norm_sub_rev]
    calc
      K * ‖CStarMatrix.mapₗ F.toLinearMap (X * Y) -
          CStarMatrix.mapₗ F.toLinearMap X * CStarMatrix.mapₗ F.toLinearMap Y‖ ≤
          K * (c * ‖X‖ * ‖Y‖) :=
        mul_le_mul_of_nonneg_left (hdefect p r q X Y) hK
      _ = (K * c) * ‖X‖ * ‖Y‖ := by ring)

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_CompletelyPositive
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
attribute [-simp] _root_.OAI.KadisonKastler.matrix_map_add _root_.OAI.KadisonKastler.matrix_map_zero _root_.OAI.KadisonSimilarity.hilbertTensor_coe_add _root_.OAI.KadisonSimilarity.inner_hilbertTensor_coe _root_.OAI.KadisonSimilarity.norm_hilbertTensor_coe _root_.OAI.NaimarkZFC.gns_apply_coe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Contractivity of unital completely positive maps

The proofs use Mathlib's completely positive maps and the spectral order
on C⋆-matrices. The Schwarz inequality is obtained from positivity of a
two-by-two Gram matrix.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- Every square amplification of a unital completely positive map is contractive. -/
theorem unital_completelyPositive_matrix_norm_le (φ : A →CP B) (hφ : φ 1 = 1)
    {n : Type*} [Fintype n] [DecidableEq n] (X : CStarMatrix n n A) :
    ‖CStarMatrix.mapₗ φ.toLinearMap X‖ ≤ ‖X‖ := by
  have hone : completelyPositiveAmplification φ n 1 = 1 := by
    ext i j
    change φ ((1 : CStarMatrix n n A) i j) =
      (1 : CStarMatrix n n B) i j
    by_cases hij : i = j
    · subst j
      simp [hφ]
    · simp [hij]
  exact unital_completelyPositive_norm_le (completelyPositiveAmplification φ n) hone X

/-- Unital complete positivity implies complete contractivity with the
rectangular convention used in the multiplication-correction argument. -/
theorem unital_completelyPositive_completelyBoundedBy (φ : A →CP B) (hφ : φ 1 = 1) :
    CompletelyBoundedBy φ.toLinearMap 1 := by
  intro p q X
  have h := unital_completelyPositive_matrix_norm_le φ hφ (rectangularCorner X)
  rw [← rectangularCorner_map, norm_rectangularCorner, norm_rectangularCorner] at h
  simpa only [one_mul] using h

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_FaithfulRepresentation
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Faithful representations are completely isometric

Injective star-algebra homomorphisms preserve C⋆-norms at each square
matrix level. The isometric corner embedding then gives the same statement
for every rectangular matrix size used in the perturbation estimates.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

/-- Faithfulness preserves the norm of each square amplification. -/
theorem injective_starAlgHom_matrix_norm (φ : A →⋆ₐ[ℂ] B) (hφ : Function.Injective φ)
    {n : Type*} [Fintype n] (X : CStarMatrix n n A) :
    ‖CStarMatrix.mapₗ φ.toAlgHom.toLinearMap X‖ = ‖X‖ := by
  change ‖CStarMatrix.mapₙₐ φ.toNonUnitalStarAlgHom X‖ = ‖X‖
  exact NonUnitalStarAlgHom.norm_map _ (injective_starAlgHom_matrix φ hφ) X

/-- Every faithful star representation preserves all rectangular matrix norms. -/
theorem injective_starAlgHom_completelyIsometric (φ : A →⋆ₐ[ℂ] B)
    (hφ : Function.Injective φ) : CompletelyIsometric φ.toAlgHom.toLinearMap := by
  intro p q X
  calc
    ‖CStarMatrix.mapₗ φ.toAlgHom.toLinearMap X‖ =
        ‖rectangularCorner (CStarMatrix.mapₗ φ.toAlgHom.toLinearMap X)‖ :=
      (norm_rectangularCorner _).symm
    _ = ‖CStarMatrix.mapₗ φ.toAlgHom.toLinearMap (rectangularCorner X)‖ := by
      rw [rectangularCorner_map]
    _ = ‖rectangularCorner X‖ := injective_starAlgHom_matrix_norm φ hφ _
    _ = ‖X‖ := norm_rectangularCorner X

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_MatrixCorrection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
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

/-- A linear equivalence which is completely close to a complete isometry
has completely bounded inverse, with the same bound at every matrix size. -/
theorem inverse_completelyBoundedBy_of_close_isometries
    (F : A ≃ₗ[ℂ] B) (ρ : A →ₗ[ℂ] C) (ι : B →ₗ[ℂ] C) {e : ℝ}
    (he : e < 1) (hρ : CompletelyIsometric ρ) (hι : CompletelyIsometric ι)
    (hclose : CompletelyBoundedBy (ι.comp F.toLinearMap - ρ) e) :
    CompletelyBoundedBy F.symm.toLinearMap ((1 - e)⁻¹) := by
  intro p q Y
  let X := (matrixLinearEquiv F p q).symm Y
  have hFX : CStarMatrix.mapₗ F.toLinearMap X = Y :=
    (matrixLinearEquiv F p q).apply_symm_apply Y
  have hcomparison : ‖CStarMatrix.mapₗ ρ X - CStarMatrix.mapₗ ι Y‖ ≤ e * ‖X‖ := by
    have h := hclose p q X
    rw [matrix_map_sub, matrix_map_comp, hFX, norm_sub_rev] at h
    exact h
  have htriangle := norm_le_norm_sub_add (CStarMatrix.mapₗ ρ X) (CStarMatrix.mapₗ ι Y)
  rw [hρ p q X, hι p q Y] at htriangle
  have hlower : (1 - e) * ‖X‖ ≤ ‖Y‖ := by linarith
  exact (le_inv_mul_iff₀ (sub_pos.mpr he)).mpr hlower

/-- Correcting multiplication changes the represented map by at most `32e`
at every rectangular matrix size, under the explicit UCP tolerance. -/
theorem correctedMap_completelyBoundedBy_thirty_two_mul
    (F : A ≃ₗ[ℂ] B) (L : A ≃ₗ[ℂ] A) (ρ : A →ₗ[ℂ] C) (ι : B →ₗ[ℂ] C)
    {e : ℝ} (he : 0 ≤ e) (he₁ : e < 1 / 1000)
    (hι : CompletelyIsometric ι) (hF : CompletelyBoundedBy F.toLinearMap 1)
    (hclose : CompletelyBoundedBy (ι.comp F.toLinearMap - ρ) e)
    (hL : CompletelyBoundedBy (L.toLinearMap - LinearMap.id) (30 * e / (1 - e))) :
    CompletelyBoundedBy (ι.comp (F.toLinearMap.comp L.symm.toLinearMap) - ρ) (32 * e) := by
  intro p q X
  have hLmatrix (Y : CStarMatrix (Fin p) (Fin q) A) :
      ‖matrixLinearEquiv L p q Y - Y‖ ≤ (30 * e / (1 - e)) * ‖Y‖ := by
    have h := hL p q Y
    rw [matrix_map_sub, matrix_map_id] at h
    exact h
  have hFmatrix (Y : CStarMatrix (Fin p) (Fin q) A) :
      ‖(CStarMatrix.mapₗ ι).comp (CStarMatrix.mapₗ F.toLinearMap) Y‖ ≤ ‖Y‖ := by
    change ‖CStarMatrix.mapₗ ι (CStarMatrix.mapₗ F.toLinearMap Y)‖ ≤ ‖Y‖
    rw [hι p q]
    simpa only [one_mul] using hF p q Y
  have hcloseMatrix (Y : CStarMatrix (Fin p) (Fin q) A) :
      ‖(CStarMatrix.mapₗ ι).comp (CStarMatrix.mapₗ F.toLinearMap) Y -
          CStarMatrix.mapₗ ρ Y‖ ≤ e * ‖Y‖ := by
    have h := hclose p q Y
    rw [matrix_map_sub, matrix_map_comp] at h
    exact h
  have hbound := norm_correctedMap_sub_le_thirty_two_mul (matrixLinearEquiv L p q)
    ((CStarMatrix.mapₗ ι).comp (CStarMatrix.mapₗ F.toLinearMap))
    (CStarMatrix.mapₗ ρ) he he₁ hLmatrix hFmatrix hcloseMatrix X
  rw [matrix_map_sub, matrix_map_comp, matrix_map_comp]
  exact hbound

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_StarCorrection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# The involution in multiplication correction

This is the algebraic star-preserving part of the UCP criterion. The
linear correction itself remains an explicit hypothesis.
-/

namespace KadisonKastler

variable {A B : Type*} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A]
  [NormedRing B] [NormedAlgebra ℂ B] [StarRing B]

theorem transportedMul_star (F : A ≃ₗ[ℂ] B)
    (hstar : ∀ x, F (star x) = star (F x)) (x y : A) :
    star (transportedMul F x y) = transportedMul F (star y) (star x) := by
  apply F.injective
  rw [hstar, map_transportedMul, star_mul, map_transportedMul, hstar, hstar]

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Haagerup
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# Row-column bounds for bilinear multiplication

The Haagerup bound is expressed directly by all finite rectangular matrix
products, as in the UCP criterion of §2 of *Universal strong
Kadison–Kastler stability* (2026). For multiplication transported through
a linear equivalence, this is exactly the matrix defect already bounded
in `CompletelyBounded`.
-/

namespace KadisonKastler

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
/-- Associativity of the bundled transported product. -/
theorem transportedBilinear_assoc (F : A ≃ₗ[ℂ] B) (x y z : A) :
    transportedBilinear F (transportedBilinear F x y) z =
      transportedBilinear F x (transportedBilinear F y z) :=
  transportedMul_assoc F x y z

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
/-- Star compatibility of the bundled transported product. -/
theorem transportedBilinear_star (F : A ≃ₗ[ℂ] B)
    (hstar : ∀ x, F (star x) = star (F x)) (x y : A) :
    star (transportedBilinear F x y) = transportedBilinear F (star y) (star x) :=
  transportedMul_star F hstar x y

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
/-- Exact equality between the row-column bilinear defect and the matrix
defect of multiplication transported through `F`. -/
theorem bilinearProduct_transported_defect (F : A ≃ₗ[ℂ] B) {p r q : ℕ}
    (X : CStarMatrix (Fin p) (Fin r) A) (Y : CStarMatrix (Fin r) (Fin q) A) :
    bilinearProduct (transportedBilinear F - LinearMap.mul ℂ A) X Y =
      CStarMatrix.mapₗ F.symm.toLinearMap
        (CStarMatrix.mapₗ F.toLinearMap X * CStarMatrix.mapₗ F.toLinearMap Y) - X * Y := by
  ext i k
  change (∑ j, (F.symm (F (X i j) * F (Y j k)) - X i j * Y j k)) =
    F.symm (∑ j, F (X i j) * F (Y j k)) - ∑ j, X i j * Y j k
  rw [map_sum, Finset.sum_sub_distrib]

omit [PartialOrder B] [StarOrderedRing B] in
/-- The transported-product matrix estimate is precisely the Haagerup bound
on the difference between transported and original multiplication. -/
theorem haagerupBound_transported_defect_iff (F : A ≃ₗ[ℂ] B) (c : ℝ) :
    HaagerupBound (transportedBilinear F - LinearMap.mul ℂ A) c ↔
      TransportedProductBound F c := by
  constructor
  · intro h p r q X Y
    simpa only [bilinearProduct_transported_defect] using h p r q X Y
  · intro h p r q X Y
    simpa only [bilinearProduct_transported_defect] using h p r q X Y

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_PublishedCorrection
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedAlgebraComplexSubtypeMemNonUnitalStarSubalgebra _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# The published multiplication-correction input

`PublishedMultiplicationCorrection` is the application of Ricard--Roydor,
*A non-commutative Amir--Cambern theorem for von Neumann algebras and
nuclear C*-algebras*, J. Funct. Anal. 267 (2014), Proposition 3.2
(arXiv:1108.1970v2), to associative, involution-compatible products on a
concrete von Neumann algebra. It is an explicit hypothesis, not an axiom.

The downstream theorem constructs the corrected star-algebra equivalence
and proves the `32e` complete bound. Surjectivity of the original map and
spatial implementation are treated separately.
-/

namespace KadisonKastler

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.instStarOrderedRingSubtypeContinuousLinearMapComplexIdMemStarSubalgebraAlgebra
variable {B C : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

attribute [local instance] OAI.KadisonKastler.instPartialOrderSubtypeContinuousLinearMapComplexIdMemStarSubalgebraAlgebra
omit [PartialOrder B] [StarOrderedRing B] in
theorem linear_correction_of_published (M : VonNeumannAlgebra H)
    (hPublished : PublishedMultiplicationCorrection M)
    (F : Algebra M ≃ₗ[ℂ] B) (hFstar : ∀ x, F (star x) = star (F x))
    {q : ℝ} (hq₀ : 0 ≤ q) (hq : q ≤ 1 / 11)
    (hdefect : TransportedProductBound F q) :
    ∃ L : Algebra M ≃ₗ[ℂ] Algebra M,
      (∀ x y, L (transportedMul F x y) = L x * L y) ∧
      (∀ x, L (star x) = star (L x)) ∧
      CompletelyBoundedBy (L.toLinearMap - LinearMap.id) (10 * q) := by
  exact hPublished (transportedBilinear F) (transportedBilinear_assoc F)
    (transportedBilinear_star F hFstar) q hq₀ hq
    ((haagerupBound_transported_defect_iff F q).mpr hdefect)

/-- The algebraic-isomorphism part of the UCP criterion, conditional only
on the published correction theorem. Complete contractivity and the linear
equivalence are explicit here; later steps supply them from positivity and
the reverse unit-ball gap. -/
theorem corrected_equivalence_of_published (M : VonNeumannAlgebra H)
    (hPublished : PublishedMultiplicationCorrection M)
    (F : Algebra M ≃ₗ[ℂ] B) (ρ : Algebra M →ₐ[ℂ] C) (ι : B →ₐ[ℂ] C)
    (hFstar : ∀ x, F (star x) = star (F x))
    {e : ℝ} (he : 0 ≤ e) (he₁ : e < 1 / 1000)
    (hρ : CompletelyIsometric ρ.toLinearMap)
    (hι : CompletelyIsometric ι.toLinearMap)
    (hF : CompletelyBoundedBy F.toLinearMap 1)
    (hclose : CompletelyBoundedBy (ι.toLinearMap.comp F.toLinearMap - ρ.toLinearMap) e) :
    ∃ θ : Algebra M ≃⋆ₐ[ℂ] B,
      CompletelyBoundedBy (ι.toLinearMap.comp θ.toAlgEquiv.toLinearMap - ρ.toLinearMap)
        (32 * e) := by
  have he2 : e < 1 := by linarith
  have hden : 0 < 1 - e := sub_pos.mpr he2
  have hq₀ : 0 ≤ 3 * e / (1 - e) := div_nonneg (by positivity) hden.le
  have hq : 3 * e / (1 - e) ≤ 1 / 11 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  have hFambient : CompletelyBoundedBy (ι.toLinearMap.comp F.toLinearMap) 1 := by
    intro p q X
    rw [matrix_map_comp, hι p q]
    exact hF p q X
  have hdefect : ∀ (p r q : ℕ) (X : CStarMatrix (Fin p) (Fin r) (Algebra M))
      (Y : CStarMatrix (Fin r) (Fin q) (Algebra M)),
      ‖CStarMatrix.mapₗ F.toLinearMap (X * Y) -
          CStarMatrix.mapₗ F.toLinearMap X * CStarMatrix.mapₗ F.toLinearMap Y‖ ≤
        3 * e * ‖X‖ * ‖Y‖ := by
    intro p r q X Y
    calc
      _ = ‖CStarMatrix.mapₗ ι.toLinearMap
          (CStarMatrix.mapₗ F.toLinearMap (X * Y) -
            CStarMatrix.mapₗ F.toLinearMap X * CStarMatrix.mapₗ F.toLinearMap Y)‖ :=
        (hι p q _).symm
      _ = ‖CStarMatrix.mapₗ (ι.toLinearMap.comp F.toLinearMap) (X * Y) -
          CStarMatrix.mapₗ (ι.toLinearMap.comp F.toLinearMap) X *
            CStarMatrix.mapₗ (ι.toLinearMap.comp F.toLinearMap) Y‖ := by
        rw [map_sub, matrix_map_mul, ← matrix_map_comp, ← matrix_map_comp,
          ← matrix_map_comp]
      _ ≤ 3 * e * ‖X‖ * ‖Y‖ :=
        matrix_multiplicative_defect_le ρ _ he hρ hFambient hclose X Y
  have hinv := inverse_completelyBoundedBy_of_close_isometries F
    ρ.toLinearMap ι.toLinearMap he2 hρ hι hclose
  have htransport := transportedProductBound_of_defect F (inv_nonneg.mpr hden.le)
    hinv hdefect
  have htransport' : TransportedProductBound F (3 * e / (1 - e)) := by
    convert htransport using 1 <;> first | rfl | ring
  obtain ⟨L, hLmul, hLstar, hLbound⟩ :=
    linear_correction_of_published M hPublished F hFstar hq₀ hq htransport'
  have hLbound' : CompletelyBoundedBy (L.toLinearMap - LinearMap.id)
      (30 * e / (1 - e)) := by
    convert hLbound using 1 <;> first | rfl | ring
  refine ⟨correctedStarAlgEquiv F L hLmul hFstar hLstar, ?_⟩
  exact correctedMap_completelyBoundedBy_thirty_two_mul F L ρ.toLinearMap ι.toLinearMap
    he he₁ hι hF hclose hLbound'

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_Range
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# The surjectivity step in the completely positive criterion

The first paragraph of Proposition 2.4 in the manuscript proves surjectivity
from a reverse unit-ball gap strictly below one. The normed-space argument
uses Riesz's lemma and requires no operator-algebra perturbation theorem.
-/

namespace KadisonKastler

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A closed complex subspace that uniformly approximates the unit ball to
an error strictly below one must be the whole space. -/
theorem eq_top_of_unitBall_approx (V : Submodule ℂ E)
    (hclosed : IsClosed (V : Set E)) {c : ℝ} (hc : c < 1)
    (happrox : ∀ x : E, ‖x‖ ≤ 1 → ∃ y ∈ V, ‖x - y‖ ≤ c) : V = ⊤ := by
  by_contra hproper
  have hout : ∃ x : E, x ∉ V := by
    by_contra h
    push Not at h
    exact hproper (Submodule.eq_top_iff'.mpr h)
  obtain ⟨x, _, hx, hsep⟩ :=
    riesz_lemma_of_lt_one hclosed hout (show (c + 1) / 2 < 1 by linarith)
  obtain ⟨y, hy, hxy⟩ := happrox x hx.le
  have := hsep y hy
  linarith

variable {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
  [NormedAddCommGroup Q] [NormedSpace ℂ Q]

/-- The reverse-gap argument for a continuous linear map with closed range.
The domain and codomain may have different norms and need not be algebras. -/
theorem surjective_of_closed_range_unitBall_approx (F : P →L[ℂ] Q)
    (hclosed : IsClosed (Set.range F)) {c : ℝ} (hc : c < 1)
    (happrox : ∀ y : Q, ‖y‖ ≤ 1 → ∃ x : P, ‖y - F x‖ ≤ c) :
    Function.Surjective F := by
  have htop : F.toLinearMap.range = ⊤ :=
    eq_top_of_unitBall_approx F.toLinearMap.range hclosed hc (by
      intro y hy
      obtain ⟨x, hx⟩ := happrox y hy
      exact ⟨F x, ⟨x, rfl⟩, hx⟩)
  exact LinearMap.range_eq_top.mp htop

/-- The range argument used in the manuscript's UCP criterion. Here `ρ`
and `ι` are isometric embeddings into one ambient operator space. The
reverse gap is expressed with arbitrary positive slack, so no nearest
point or compactness hypothesis is hidden in the statement. -/
theorem bijective_of_close_isometry_and_reverse_gap [CompleteSpace P]
    (ρ : P →L[ℂ] E) (ι : Q →L[ℂ] E) (F : P →L[ℂ] Q)
    (hρ : ∀ x, ‖ρ x‖ = ‖x‖) (hι : ∀ y, ‖ι y‖ = ‖y‖)
    {e g : ℝ} (he : 0 ≤ e) (he1 : e < 1) (hge : g + e < 1)
    (hclose : ∀ x, ‖ι (F x) - ρ x‖ ≤ e * ‖x‖)
    (hgap : ∀ y : Q, ‖y‖ ≤ 1 → ∀ r : ℝ, g < r →
      ∃ x : P, ‖x‖ ≤ 1 ∧ ‖ι y - ρ x‖ < r) :
    Function.Bijective F := by
  have hpos : 0 < 1 - e := sub_pos.mpr he1
  have hlower (x : P) : (1 - e) * ‖x‖ ≤ ‖F x‖ := by
    have ht := norm_add_le (ρ x - ι (F x)) (ι (F x))
    have hc := hclose x
    rw [norm_sub_rev] at hc
    rw [sub_add_cancel, hρ, hι] at ht
    nlinarith
  have hanti : AntilipschitzWith ⟨(1 - e)⁻¹, inv_nonneg.mpr hpos.le⟩ F := by
    apply F.antilipschitz_of_bound
    intro x
    change ‖x‖ ≤ (1 - e)⁻¹ * ‖F x‖
    exact (le_inv_mul_iff₀ hpos).mpr (hlower x)
  refine ⟨hanti.injective, ?_⟩
  apply surjective_of_closed_range_unitBall_approx F
    (hanti.isClosed_range F.uniformContinuous)
    (c := (g + 1 - e) / 2 + e) (by linarith)
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hgap y hy ((g + 1 - e) / 2) (by linarith)
  refine ⟨x, ?_⟩
  calc
    ‖y - F x‖ = ‖ι y - ι (F x)‖ := by rw [← map_sub, hι]
    _ ≤ ‖ι y - ρ x‖ + ‖ρ x - ι (F x)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (g + 1 - e) / 2 + e := by
      have hc := hclose x
      rw [norm_sub_rev] at hc
      have hehx : e * ‖x‖ ≤ e := by nlinarith
      linarith

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_UCP
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCompleteSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAddCommGroup _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildPatching.instFintypeBoundedWordOfFinite _root_.OAI.HochschildPatching.instFintypeLinearLabelOfFinite _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.instFintypeSignedPermutation _root_.OAI.KadisonKastler.matrixSiteBlockIndexDecidableEq _root_.OAI.KadisonKastler.matrixSiteBlockIndexFintype _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.cycleMembersFintype _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.matchingRepresentativesFintype _root_.OAI.KadisonSimilarity.perfectMatchingFintype _root_.OAI.KadisonSimilarity.permutationCyclesDecidableEq _root_.OAI.KadisonSimilarity.permutationCyclesFintype _root_.OAI.KadisonSimilarity.sourcePairClassesFintype _root_.OAI.KadisonSimilarity.testPairClassesFintype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# From a close UCP map to a star-algebra equivalence

The range argument and the multiplication-correction estimates give the
isomorphism part of the manuscript's UCP criterion under
`PublishedMultiplicationCorrection`. Complete positivity gives complete
contractivity and star preservation.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

variable {A B : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- A complete bound implies the corresponding scalar bound. -/
theorem norm_le_of_completelyBoundedBy (F : A →ₗ[ℂ] B) {c : ℝ}
    (hF : CompletelyBoundedBy F c) (x : A) : ‖F x‖ ≤ c * ‖x‖ := by
  let eA := CStarMatrix.toOneByOne (Fin 1) ℂ A
  let eB := CStarMatrix.toOneByOne (Fin 1) ℂ B
  have heq : CStarMatrix.mapₗ F (eA x) = eB (F x) := by
    ext i j
    rfl
  have h := hF 1 1 (eA x)
  have hnA : ‖eA x‖ = ‖x‖ :=
    NonUnitalStarAlgHom.norm_map eA.toStarAlgHom eA.injective x
  have hnB : ‖eB (F x)‖ = ‖F x‖ :=
    NonUnitalStarAlgHom.norm_map eB.toStarAlgHom eB.injective (F x)
  rw [heq, hnA, hnB] at h
  exact h

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.instStarOrderedRingSubtypeContinuousLinearMapComplexIdMemStarSubalgebraAlgebra_1
variable {C : Type*} [CStarAlgebra C] [PartialOrder C] [StarOrderedRing C]

attribute [local instance] OAI.KadisonKastler.instPartialOrderSubtypeContinuousLinearMapComplexIdMemStarSubalgebraAlgebra_1
/-- A UCP map completely close to a faithful representation and with
strict reverse unit-ball gap is bijective. Its normality is not needed. -/
theorem bijective_ucp_of_reverse_gap (M : VonNeumannAlgebra H)
    (φ : Algebra M →CP B) (hφ : φ 1 = 1)
    (ρ : Algebra M →⋆ₐ[ℂ] C) (ι : B →⋆ₐ[ℂ] C)
    (hρ : Function.Injective ρ) (hι : Function.Injective ι)
    {e g : ℝ} (he : 0 ≤ e) (he₁ : e < 1) (hge : g + e < 1)
    (hclose : CompletelyBoundedBy
      (ι.toAlgHom.toLinearMap.comp φ.toLinearMap - ρ.toAlgHom.toLinearMap) e)
    (hgap : ∀ y : B, ‖y‖ ≤ 1 → ∀ r : ℝ, g < r →
      ∃ x : Algebra M, ‖x‖ ≤ 1 ∧ ‖ι y - ρ x‖ < r) :
    Function.Bijective φ := by
  apply bijective_of_close_isometry_and_reverse_gap
    (starAlgHomToContinuousLinearMap ρ) (starAlgHomToContinuousLinearMap ι)
    (unitalCompletelyPositiveToContinuousLinearMap φ hφ)
    (injective_starAlgHom_norm ρ hρ) (injective_starAlgHom_norm ι hι) he he₁ hge
  · exact fun x => norm_le_of_completelyBoundedBy _ hclose x
  · exact hgap

/-- The complete `32e` isomorphism conclusion of the UCP criterion.
The source is a concrete von Neumann algebra; the target may be any
faithfully represented C*-algebra. Multiplication correction gives the
star-algebra equivalence. -/
theorem ucp_starEquiv_of_published (M : VonNeumannAlgebra H)
    (hPublished : PublishedMultiplicationCorrection M)
    (φ : Algebra M →CP B) (hφ : φ 1 = 1)
    (ρ : Algebra M →⋆ₐ[ℂ] C) (ι : B →⋆ₐ[ℂ] C)
    (hρ : Function.Injective ρ) (hι : Function.Injective ι)
    {e g : ℝ} (he : 0 ≤ e) (he₁ : e < 1 / 1000) (hge : g + e < 1)
    (hclose : CompletelyBoundedBy
      (ι.toAlgHom.toLinearMap.comp φ.toLinearMap - ρ.toAlgHom.toLinearMap) e)
    (hgap : ∀ y : B, ‖y‖ ≤ 1 → ∀ r : ℝ, g < r →
      ∃ x : Algebra M, ‖x‖ ≤ 1 ∧ ‖ι y - ρ x‖ < r) :
    ∃ θ : Algebra M ≃⋆ₐ[ℂ] B,
      CompletelyBoundedBy
        (ι.toAlgHom.toLinearMap.comp θ.toAlgEquiv.toLinearMap - ρ.toAlgHom.toLinearMap)
        (32 * e) := by
  have hbij := bijective_ucp_of_reverse_gap M φ hφ ρ ι hρ hι he
    (by linarith) hge hclose hgap
  let F : Algebra M ≃ₗ[ℂ] B := LinearEquiv.ofBijective φ.toLinearMap hbij
  exact corrected_equivalence_of_published M hPublished F ρ.toAlgHom ι.toAlgHom
    (completelyPositive_map_star φ) he he₁
    (injective_starAlgHom_completelyIsometric ρ hρ)
    (injective_starAlgHom_completelyIsometric ι hι)
    (unital_completelyPositive_completelyBoundedBy φ hφ) hclose

end

end KadisonKastler

end OAI
end

section
-- module Solutions.OAIQ075_KS.KadisonKastler_ConcreteUCP
attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductCStar _root_.OAI.ComparatorModel.CurrentMain.boundedFamilyProductOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealPartialOrder _root_.OAI.CuntzPureness.ClosedStarIdeal.idealStarAlgebraCStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientCStarAlgebra _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedRing _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientNormedSpace _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStar _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarModule _root_.OAI.CuntzPureness.ClosedStarIdeal.quotientStarRing _root_.OAI.CurrentMain.boundedFamilyProductCStar _root_.OAI.CurrentMain.boundedFamilyProductOrder _root_.OAI.Generator.Tracial.algebraDualNormed _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.Generator.Tracial.cyclicPredual_complete _root_.OAI.Generator.Tracial.cyclicPredual_normed _root_.OAI.Generator.Tracial.cyclicPredual_normedSpace _root_.OAI.Generator.Tracial.functionalSubspaceNormed _root_.OAI.Generator.Tracial.functionalSubspaceNormedSpace _root_.OAI.Generator.Tracial.functionalSubspaceWeakLocallyConvex _root_.OAI.Generator.Tracial.functionalSubspaceWeakScalarTower _root_.OAI.Generator.Tracial.insideAlgebra_complete _root_.OAI.Generator.Tracial.predualWeakLocallyConvex _root_.OAI.Generator.Tracial.predualWeakScalarTower _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildCorners.cornerCStarAlgebra _root_.OAI.HochschildCorners.cornerNormedRing _root_.OAI.HochschildCorners.cornerOne _root_.OAI.HochschildCorners.cornerRing _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.boundedSequenceCStarAlgebra _root_.OAI.KadisonKastler.characterCommutantCStarAlgebra _root_.OAI.KadisonKastler.generatedExtension_cstar _root_.OAI.KadisonKastler.hilbertULiftInner _root_.OAI.KadisonKastler.measurableOperatorSubalgebra_closed _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.tracialSequenceQuotientCStarAlgebra _root_.OAI.KadisonKastler.varyingSequenceCStarAlgebra _root_.OAI.KadisonKastler.weakOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.CStarCorner.instCStarAlgebraSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instNormedRingSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.CStarCorner.instPartialOrderSubtypeMemNonUnitalStarSubalgebraComplex _root_.OAI.KadisonSimilarity.instCoeOutConcretePredualStrongDualComplexSubtypeContinuousLinearMapIdMemStarSubalgebra _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.NaimarkZFC.cornerCStarAlgebra _root_.OAI.NaimarkZFC.cornerNormedRing _root_.OAI.NaimarkZFC.cornerOne _root_.OAI.NaimarkZFC.cornerPartialOrder _root_.OAI.NaimarkZFC.cornerRing _root_.OAI.NuclearUltrapower.UltraPreHilbert.instSeminormedAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.PopaCorner.instCStarAlgebra _root_.OAI.PopaCorner.instNormedRing _root_.OAI.PopaCorner.instOne _root_.OAI.PopaCorner.instRing _root_.OAI.Pureness.NuclearLift.instCStarAlgebraULift_solutions _root_.OAI.Pureness.NuclearLift.instStarRingULift_solutions _root_.OAI.Pureness.NuclearLift.instStarULift_solutions _root_.OAI.UltrapowerBridge.instStarModuleComplexTracialQuotient _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

/-!
# The UCP criterion for concrete von Neumann algebras

The ordinary Kadison--Kastler gap supplies precisely the reverse unit-ball
approximation used in the UCP range argument.
-/

namespace KadisonKastler

open scoped CStarAlgebra

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.KadisonKastler.instStarOrderedRingContinuousLinearMapComplexId_solutions_1
attribute [local instance] OAI.KadisonKastler.instPartialOrderSubtypeContinuousLinearMapComplexIdMemStarSubalgebraAlgebra_2
attribute [local instance] OAI.KadisonKastler.instStarOrderedRingSubtypeContinuousLinearMapComplexIdMemStarSubalgebraAlgebra_2
theorem reverse_gap_of_kkDistance_lt {M N : VonNeumannAlgebra H} {g : ℝ}
    (hgap : kkDistance M N < g) :
    ∀ y : Algebra N, ‖y‖ ≤ 1 → ∀ r : ℝ, g < r →
      ∃ x : Algebra M, ‖x‖ ≤ 1 ∧
        ‖algebraInclusion N y - algebraInclusion M x‖ < r := by
  intro y hy r hr
  have hdist : kkDistance N M < r := by rw [kkDistance_comm]; exact hgap.trans hr
  obtain ⟨x, hx, hxy⟩ := exists_unitBall_approx
    (M := N) (N := M) (x := (y : H →L[ℂ] H)) ⟨y.property, hy⟩ hdist
  exact ⟨⟨x, hx.1⟩, hx.2, hxy⟩

attribute [local instance] OAI.KadisonKastler.instPartialOrderContinuousLinearMapComplexId_solutions_1
/-- The concrete-algebra isomorphism part of the UCP criterion, with the
ordinary metric used only for the reverse gap. -/
theorem concrete_ucp_starEquiv_of_published_oai {M N : VonNeumannAlgebra H}
    (hPublished : PublishedMultiplicationCorrection M)
    (φ : Algebra M →CP Algebra N) (hφ : φ 1 = 1)
    {e g : ℝ} (he : 0 ≤ e) (he₁ : e < 1 / 1000) (hge : g + e < 1)
    (hclose : CompletelyBoundedBy
      ((algebraInclusion N).toAlgHom.toLinearMap.comp φ.toLinearMap -
        (algebraInclusion M).toAlgHom.toLinearMap) e)
    (hgap : kkDistance M N < g) :
    ∃ θ : Algebra M ≃⋆ₐ[ℂ] Algebra N,
      CompletelyBoundedBy
        ((algebraInclusion N).toAlgHom.toLinearMap.comp θ.toAlgEquiv.toLinearMap -
          (algebraInclusion M).toAlgHom.toLinearMap) (32 * e) := by
  exact ucp_starEquiv_of_published M hPublished φ hφ
    (algebraInclusion M) (algebraInclusion N) Subtype.val_injective Subtype.val_injective
    he he₁ hge hclose (reverse_gap_of_kkDistance_lt hgap)

end

end KadisonKastler

end OAI
end

theorem solution.{u} : type_of% @OAI.KadisonKastler.concrete_ucp_starEquiv_of_published_oai.{u} := @OAI.KadisonKastler.concrete_ucp_starEquiv_of_published_oai.{u}
