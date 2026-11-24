-- Prove2me | solution 1 for GlobalTheory.T.exists_normOne_cmField_det_one_add_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:06:59.649808+00:00
-- url     : https://prove2.me/submissions/60aab7f3-cbba-4336-8646-5a98ee5fb8fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsNormOneCmFieldDetOneAddNeZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsNormOneCmFieldDetOneAddNeZeroStatement
import Theorems.Thm_GlobalTheory_exists_normOne_det_one_add_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ), ∃ a : L, a * (IsCMField.complexConj L : L →+* L) a = 1 ∧ ∀ σ : L →+* ℂ, (1 + σ a • X σ).det ≠ 0 := by
  first | exact @GlobalTheory.exists_normOne_det_one_add_ne_zero | exact GlobalTheory.exists_normOne_det_one_add_ne_zero | (intros; apply GlobalTheory.exists_normOne_det_one_add_ne_zero <;> assumption)
end _root_.GlobalTheory.T
