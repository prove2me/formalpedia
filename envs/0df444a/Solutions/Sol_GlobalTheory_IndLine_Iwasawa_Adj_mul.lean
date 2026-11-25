-- Prove2me | solution 1 for GlobalTheory.IndLine.Iwasawa.Adj.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:41:41.706797+00:00
-- url     : https://prove2.me/submissions/b58cd28c-e1c5-46bf-a27a-02d6134dab80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapStarMul
import Theorems.Thm_P2M_GlobalTheory_IndLine_Iwasawa_map_star_mul__5f024dfe3853

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Matrix
open GlobalTheory GlobalTheory.IndLine GlobalTheory.IndLine.Iwasawa
variable {m : Type} [Fintype m] [DecidableEq m]
variable {N A B A' B' : Matrix m m ℂ}
namespace GlobalTheory.IndLine.Iwasawa
namespace Adj
theorem _root_.solution (h : Adj N A B) (h' : Adj N A' B') : Adj N (A * A') (B' * B) := by
  rw [Adj, Matrix.transpose_mul, Matrix.mul_assoc, h, ← Matrix.mul_assoc, h', map_star_mul',
    Matrix.mul_assoc]
end Adj
end GlobalTheory.IndLine.Iwasawa
