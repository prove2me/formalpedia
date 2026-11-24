-- Prove2me | solution 1 for GlobalTheory.FunObj.toFrame_stair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:52:48.333503+00:00
-- url     : https://prove2.me/submissions/908b1aee-a6df-482f-bd60-49388d87865d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] (G : Grid k)
variable {G}
variable (hs : 1 ≤ G.s)
variable {hs}
namespace GlobalTheory.FunObj
theorem _root_.solution (ϖ : kˣ) (e : ℕ) {j : ℕ} (hj : j < G.m) : toFrame hs hj (stair G ϖ e j) =
    diagGL (Sum.elim (fun _ => 1) fun p => ϖ ^ (e * (p.val + 1))) := by
  refine Units.ext ?_
  have h : topRank G j + (G.m - 1 - j) = G.rank (G.m, j) := by have := topRank_add hs j; omega
  show (stair G ϖ e j).val.submatrix (frame h) (frame h) = _
  rw [stair, diagGL_val, diagGL_val, submatrix_diagonal_equiv]
  congr 1
  funext x
  rcases x with a | p
  · simp [frame, Nat.sub_eq_zero_of_le (Nat.succ_le_of_lt a.2)]
  · simp [frame, add_assoc]
end GlobalTheory.FunObj
