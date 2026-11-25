-- Prove2me | solution 1 for GlobalTheory.T.exists_isUnit_det_add_mul_of_fromBlocks_localRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:16:02.43606+00:00
-- url     : https://prove2.me/submissions/75d16e8a-2982-468b-b5bc-944a8c169ad6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsUnitDetAddMulOfFromBlocksLocalRing
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsUnitDetAddMulOfFromBlocksLocalRingStatement
import Theorems.Thm_GlobalTheory_BlockInvertibleLocal_exists_isUnit_det_add_mul


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
theorem _root_.solution : ∀ {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) O),
    IsUnit (Matrix.fromBlocks A B C D).det → ∃ X : Matrix (Fin n) (Fin n) O, IsUnit (A + X * C).det := by
  first | exact @GlobalTheory.BlockInvertibleLocal.exists_isUnit_det_add_mul | exact GlobalTheory.BlockInvertibleLocal.exists_isUnit_det_add_mul | (intros; apply GlobalTheory.BlockInvertibleLocal.exists_isUnit_det_add_mul <;> assumption)
end _root_.GlobalTheory.T
