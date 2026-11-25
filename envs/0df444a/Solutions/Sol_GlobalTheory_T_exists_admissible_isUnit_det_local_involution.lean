-- Prove2me | solution 1 for GlobalTheory.T.exists_admissible_isUnit_det_local_involution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:14:34.093652+00:00
-- url     : https://prove2.me/submissions/0f75d8cd-08ad-4379-ad78-a8a9bf230c20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAdmissibleIsUnitDetLocalInvolution
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAdmissibleIsUnitDetLocalInvolutionStatement
import Theorems.Thm_GlobalTheory_LocalLift_exists_admissible_isUnit_det


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) O), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A B C D : Matrix (Fin n) (Fin n) O), IsUnit (Matrix.fromBlocks A B C D).det →
      (Matrix.fromBlocks A B C D)ᵀ * Matrix.fromBlocks 0 S S 0 * (Matrix.fromBlocks A B C D).map c =
        Matrix.fromBlocks 0 S S 0 →
      ∃ X : Matrix (Fin n) (Fin n) O, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det := by
  first | exact @GlobalTheory.LocalLift.exists_admissible_isUnit_det | exact GlobalTheory.LocalLift.exists_admissible_isUnit_det | (intros; apply GlobalTheory.LocalLift.exists_admissible_isUnit_det <;> assumption)
end _root_.GlobalTheory.T
