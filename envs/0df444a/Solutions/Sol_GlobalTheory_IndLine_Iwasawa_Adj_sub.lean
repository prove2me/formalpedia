-- Prove2me | solution 1 for GlobalTheory.IndLine.Iwasawa.Adj.sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:38:39.452771+00:00
-- url     : https://prove2.me/submissions/9a6f5bb6-43bf-413b-990e-3529b2f8fbc0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MapStarMul

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
theorem _root_.solution (h : Adj N A B) (h' : Adj N A' B') : Adj N (A - A') (B - B') := by
  rw [Adj, Matrix.transpose_sub, Matrix.sub_mul, h, h', Matrix.map_sub _ star_sub, Matrix.mul_sub]
end Adj
end GlobalTheory.IndLine.Iwasawa
