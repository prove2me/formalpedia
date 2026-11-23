-- Prove2me | solution 1 for GlobalTheory.IndLine.Iwasawa.Adj.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:36:09.525659+00:00
-- url     : https://prove2.me/submissions/04eabd15-d26d-4fb4-ad18-424e3ad2c68b

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
theorem _root_.solution (h : Adj N A B) (h' : Adj N A' B') : Adj N (A + A') (B + B') := by
  rw [Adj, Matrix.transpose_add, Matrix.add_mul, h, h', Matrix.map_add _ star_add, Matrix.mul_add]
end Adj
end GlobalTheory.IndLine.Iwasawa
