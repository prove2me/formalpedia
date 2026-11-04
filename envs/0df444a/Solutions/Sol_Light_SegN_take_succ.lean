-- Prove2me | solution 1 for Light.SegN.take_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:08:35.349854+00:00
-- url     : https://prove2.me/submissions/e1488507-e9ed-49d7-ad66-1e1153e57bce

import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
import Definitions.Def_Submission_ThreeSumApsp_Lang_Regions
import Definitions.Def_Submission_ThreeSumApsp_Util_Index
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic.Positivity
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Theorems.Thm_Light_Seg_snoc
import Theorems.Thm_Light_SegN_snoc
import Theorems.Thm_List_take_succ_getD


set_option autoImplicit false
section
open Light
open ThreeSumApsp
variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}
namespace Light
namespace SegN
theorem _root_.solution {l : List ℕ} {k : ℕ} (h : SegN μ a (l.take k)) (hk : k < l.length) :
    SegN (Function.update μ (a + k) ((l.getD k 0 : ℕ) : ℤ)) a (l.take (k + 1)) := by
  have hsnoc := h.snoc (l.getD k 0)
  rwa [List.length_take, Nat.min_eq_left hk.le, ← List.take_succ_getD l hk 0] at hsnoc
end SegN
end Light
