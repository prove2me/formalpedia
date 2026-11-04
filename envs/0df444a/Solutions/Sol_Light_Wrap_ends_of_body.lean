-- Prove2me | solution 1 for Light.Wrap.ends_of_body
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:31:47.191194+00:00
-- url     : https://prove2.me/submissions/9bdc631c-a36a-4b50-a621-b172dcb0c1ec

import Definitions.Def_Submission_ThreeSumApsp_Lang_RowMajor
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSumApsp_Lang_ToMachine
import Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
import Definitions.Def_Submission_ThreeSumApsp_Util_Flag
import Definitions.Def_Submission_ThreeSumApsp_Lang_TopProcedure
import Theorems.Thm_Light_Ends_call
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_Need_Ok_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_SolvedIn_mono
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_mono
import Theorems.Thm_ThreeSumApsp_WordRam_IsDataStructure_mono
import Theorems.Thm_ThreeSumApsp_WordRam_Solves_mono
import Theorems.Thm_ThreeSumApsp_WordRam_WritesIn_mono
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
theorem _root_.solution (w : Wrap Q task dec) {P : Program} {p κ T : ℕ} (x : Bounded Q) {need : ℕ → ℕ → Need}
    (h :
      Ends (w.limits need x) (P ++ [topBody κ p w.args dec]) 1 (topBody κ p w.args dec)
        ⟨frame [0, 0], memOf ((ofEnd Q).input x)⟩ T (Answered x dec)) :
    Ends (w.limits need x) (P ++ [topBody κ p w.args dec]) 0 (mainStmt P.length)
      ⟨frame [0, 0, 0], memOf ((ofEnd Q).input x)⟩ (T + 4) (Answered x dec) :=
  Ends.call T (by simp) (by simp) (by simp only [limits]; omega)
    (h.mono le_rfl fun _ hσ => by simpa [Answered] using hσ)
    (by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;>
            first
            | omega
            | (ring_nf; omega)))
end Light.Wrap
