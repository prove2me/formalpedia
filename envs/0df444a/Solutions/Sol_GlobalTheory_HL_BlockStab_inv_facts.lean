-- Prove2me | solution 1 for GlobalTheory.HL.BlockStab.inv_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:29:07.890796+00:00
-- url     : https://prove2.me/submissions/12c1e4e4-762f-45ad-9b5f-8e3ce005734d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFramesPairingStabilizerBlockDiagonal
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.BlockStab
variable {E : Type} [CommRing E] {n : ℕ}
namespace GlobalTheory.HL.BlockStab
theorem _root_.solution (A : Matrix (Fin n) (Fin n) E) (hA : IsUni A) :
    ∃ B : Matrix (Fin n) (Fin n) E, A * B = 1 ∧ B * A = 1 ∧ IsUni B ∧
      (∀ O : Subring E, (∀ i j, A i j ∈ O) → ∀ i j, B i j ∈ O) ∧
      ∀ β : Fin n → ℕ, (∀ i j, β i < β j → A i j = 0) → ∀ i j, β i < β j → B i j = 0 := by
  have hT : A.BlockTriangular id := fun i j h => hA.1 i j h
  have hd : A.det = 1 := by rw [Matrix.det_of_upperTriangular hT]; simp [hA.2]
  have hu : IsUnit A.det := by rw [hd]; exact isUnit_one
  letI : Invertible A := Matrix.invertibleOfIsUnitDet A hu
  have hT' := Matrix.blockTriangular_inv_of_blockTriangular hT
  refine ⟨A⁻¹, Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu, ⟨fun i j h => hT' h, fun i => ?_⟩,
    fun O hO i j => ?_, fun β hβ i j h => ?_⟩
  · have h1 : (A * A⁻¹) i i = 1 := by rw [Matrix.mul_nonsing_inv _ hu]; simp
    rw [Matrix.mul_apply, Finset.sum_eq_single i, hA.2, one_mul] at h1
    · exact h1
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hA.1 i k h, zero_mul]
      · rw [hT' (show id i < id k from h), mul_zero]
    · simp
  · have h1 : A = O.subtype.mapMatrix (Matrix.of fun i j => (⟨A i j, hO i j⟩ : O)) := by
      ext i j; simp
    rw [Matrix.inv_def, hd, Ring.inverse_one, one_smul, h1, ← RingHom.map_adjugate]
    simp
  · have h1 : A.BlockTriangular (OrderDual.toDual ∘ β) := fun i j h => hβ i j h
    exact Matrix.blockTriangular_inv_of_blockTriangular h1 (i := i) (j := j) h
end GlobalTheory.HL.BlockStab
