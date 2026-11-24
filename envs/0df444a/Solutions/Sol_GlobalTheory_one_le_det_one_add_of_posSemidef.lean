-- Prove2me | solution 1 for GlobalTheory.one_le_det_one_add_of_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:28:12.92104+00:00
-- url     : https://prove2.me/submissions/2a559c00-c9e3-430d-b67a-2f2657fbee4f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_OneLeDetOneAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Theorems.Thm_GlobalTheory_OneLeDetOneAdd_one_le_det_one_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder MatrixOrder
open GlobalTheory
variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]
variable [DecidableEq n]
namespace GlobalTheory
theorem _root_.solution {D : Matrix n n 𝕜} (hD : D.PosSemidef) :
    1 ≤ (1 + D).det := by
  first
  | exact @_root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add
  | exact _root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add
  | (apply _root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add <;> assumption)
  | (intros; apply _root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add ..)
end GlobalTheory
