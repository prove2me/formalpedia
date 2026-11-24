-- Prove2me | solution 1 for GlobalTheory.CuspGL.sepIneq_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:05:31.695653+00:00
-- url     : https://prove2.me/submissions/d04c4575-1cda-4a3a-97d2-487efd86e66c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SeparationNumericalIneqCuspidalGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL
namespace GlobalTheory.CuspGL
theorem _root_.solution (t k c : ℕ) (hc : c ≤ 2) (hk : 0 < k) : (((2 + t) ^ k - c : ℕ) : ℤ) = (2 + (t : ℤ)) ^ k - c := by
  have : 2 ≤ (2 + t) ^ k := le_trans (by omega) (Nat.le_self_pow hk.ne' _)
  rw [Nat.cast_sub (by omega)]
  push_cast
  rfl
end GlobalTheory.CuspGL
