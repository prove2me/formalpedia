-- Prove2me | solution 1 for GlobalTheory.StandardAdditiveCharacter.exists_stdAddChar_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:58:40.7925+00:00
-- url     : https://prove2.me/submissions/f82b7dab-c645-41d2-90ec-a84b01f8c411

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveDualAddChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.StandardAdditiveCharacter
namespace GlobalTheory.StandardAdditiveCharacter
theorem _root_.solution (n : ℕ) [NeZero n] (z : ℂ) (hz : z ^ n = 1) :
    ∃ j : ZMod n, ZMod.stdAddChar j = z := by
  obtain ⟨i, -, hi⟩ := (Complex.isPrimitiveRoot_exp n (NeZero.ne n)).eq_pow_of_pow_eq_one hz
  refine ⟨((i : ℤ) : ZMod n), ?_⟩
  rw [ZMod.stdAddChar_coe, ← hi, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring
end GlobalTheory.StandardAdditiveCharacter
