-- Prove2me | solution 1 for GlobalTheory.JacobiClassSum.jacobiSym_val_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:53:10.37364+00:00
-- url     : https://prove2.me/submissions/db1b06dd-1c50-4741-915a-2a2d6a7f8f13

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsJacobiSymEqNegOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.JacobiClassSum
namespace GlobalTheory.JacobiClassSum
theorem _root_.solution {s : ℕ} [NeZero s] (b : ℕ) :
    jacobiSym (((b : ZMod s).val : ℕ) : ℤ) s = jacobiSym (b : ℤ) s := by
  rw [ZMod.val_natCast, Int.natCast_mod, ← jacobiSym.mod_left]
end GlobalTheory.JacobiClassSum
