-- Prove2me | solution 1 for GlobalTheory.IndLine.Iwasawa.Adj.one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:38:37.773751+00:00
-- url     : https://prove2.me/submissions/eeab3819-2ae3-4044-83ff-372438fd5f79

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
theorem _root_.solution : Adj N 1 1 := by
  rw [Adj, Matrix.transpose_one, Matrix.map_one _ (star_zero _) (star_one _), Matrix.one_mul, Matrix.mul_one]
end Adj
end GlobalTheory.IndLine.Iwasawa
