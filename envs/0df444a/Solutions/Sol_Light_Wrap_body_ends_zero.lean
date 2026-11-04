-- Prove2me | solution 1 for Light.Wrap.body_ends_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:33:42.353527+00:00
-- url     : https://prove2.me/submissions/fe727ace-8579-4136-aeb4-07ef71f403b8

import Definitions.Def_Submission_ThreeSumApsp_Lang_RowMajor
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSumApsp_Lang_ToMachine
import Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
import Definitions.Def_Submission_ThreeSumApsp_Util_Flag
import Definitions.Def_Submission_ThreeSumApsp_Lang_TopProcedure
import Theorems.Thm_Light_ofEnd_cell0
import Theorems.Thm_Light_safe_cell0
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_setToThen
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil
set_option autoImplicit false
section
open Light
open ThreeSumApsp ThreeSumApsp.WordRam
variable {lim : Limits} {P : Program} {d : ℕ}
open Light.Wrap
variable {Q : EndStatement.Problem} {task : Task} {dec : Bool}
namespace Light.Wrap
theorem _root_.solution (w : Wrap Q task dec) (P : Program) (p κ : ℕ) (x : Bounded Q) (hn : x.n = 0)
    {need : ℕ → ℕ → Need} {lim : Limits} (hroom : w.Room need x lim) :
    Ends lim (P ++ [topBody κ p w.args dec]) 1 (topBody κ p w.args dec) ⟨frame [0, 0], memOf ((ofEnd Q).input x)⟩ 9
      (Answered x dec) :=
  by
  have hbound := hroom.bound
  push_cast at hbound
  unfold topBody
  refine
    Ends.setToThen (x.n : ℤ) ?_
      ⟨safe_cell0 (by omega) hroom.space, ofEnd_cell0 x _⟩
        -- if n ≠ 0 … else result := 0 or 1
        
  refine Ends.iteLast (fun _ => ?_) (fun h => absurd (by simp [hn]) h)
  have hanswer := w.zero x hn
  cases dec <;>
    exact
      Ends.set (by simp; omega)
        (by
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [] <;>
                first
                | omega
                | (ring_nf; omega)))
        (by simpa [Answered, verdictOf] using hanswer _)
end Light.Wrap
