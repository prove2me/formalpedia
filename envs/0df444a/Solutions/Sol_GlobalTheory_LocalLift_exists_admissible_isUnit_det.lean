-- Prove2me | solution 1 for GlobalTheory.LocalLift.exists_admissible_isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:58:42.205848+00:00
-- url     : https://prove2.me/submissions/c88578e4-7fbe-4aaf-85a0-3ed08c7416f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAdmissibleLagrangianTransverseFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAdmissibleIsUnitDetLocalInvolution
import Theorems.Thm_GlobalTheory_LocalLift_lift_of_field
import Theorems.Thm_GlobalTheory_T_exists_admissible_lagrangian_transverse_field


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.LocalLift
namespace GlobalTheory.LocalLift
theorem _root_.solution :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) O), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A B C D : Matrix (Fin n) (Fin n) O), IsUnit (Matrix.fromBlocks A B C D).det →
      (Matrix.fromBlocks A B C D)ᵀ * Matrix.fromBlocks 0 S S 0 * (Matrix.fromBlocks A B C D).map c =
        Matrix.fromBlocks 0 S S 0 →
      ∃ X : Matrix (Fin n) (Fin n) O, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det :=
  lift_of_field GlobalTheory.T.exists_admissible_lagrangian_transverse_field
end GlobalTheory.LocalLift
