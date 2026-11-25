-- Prove2me | solution 1 for GlobalTheory.HL.PairingClass.UT.inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:58:33.554715+00:00
-- url     : https://prove2.me/submissions/e2456f8b-e499-4863-8f30-b73124287ae4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NotField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermOverRelationUniqueness
import Theorems.Thm_GlobalTheory_HL_PairingClass_diag_mul
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
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PairingClass
variable {E : Type} [CommRing E] {n : ℕ}
namespace GlobalTheory.HL.PairingClass
namespace UT
theorem _root_.solution {A : Matrix (Fin n) (Fin n) E} (hA : UT A) :
    ∃ B, UT B ∧ A * B = 1 ∧ B * A = 1 ∧ ∀ O : Subring E, IntM O A → IntM O B := by
  have h1 : A.BlockTriangular id := fun i j h => hA.1 i j h
  have hd : A.det = 1 := by
    rw [Matrix.det_of_upperTriangular h1]; simp [hA.2]
  have hu : IsUnit A.det := by rw [hd]; exact isUnit_one
  letI := A.invertibleOfIsUnitDet hu
  have h2 : (A⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular h1
  have h3 : ∀ i j, j < i → A⁻¹ i j = 0 := fun i j h => h2 h
  refine ⟨A⁻¹, ⟨h3, fun i => ?_⟩, Matrix.mul_nonsing_inv A hu, Matrix.nonsing_inv_mul A hu, ?_⟩
  · have := diag_mul hA.1 h3 i
    rw [Matrix.mul_nonsing_inv A hu, hA.2, one_mul] at this
    rw [← this]; simp
  · intro O hO i j
    let A₀ : Matrix (Fin n) (Fin n) O := fun i j => ⟨A i j, hO i j⟩
    have hA₀ : O.subtype.mapMatrix A₀ = A := by ext i j; rfl
    rw [Matrix.inv_def, hd, Ring.inverse_one, one_smul, ← hA₀, ← RingHom.map_adjugate]
    exact (A₀.adjugate i j).2
end UT
end GlobalTheory.HL.PairingClass
