-- Prove2me | solution 1 for Light.Wrap.body_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:35:50.588999+00:00
-- url     : https://prove2.me/submissions/6f77a907-f619-4f98-8736-cd7279752b5d

import Definitions.Def_Submission_ThreeSumApsp_Lang_RowMajor
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSumApsp_Lang_ToMachine
import Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
import Definitions.Def_Submission_ThreeSumApsp_Util_Flag
import Definitions.Def_Submission_ThreeSumApsp_Lang_TopProcedure
import Theorems.Thm_Light_pow_spec
import Theorems.Thm_Light_ofEnd_cell0
import Theorems.Thm_Light_safe_cell0
import Theorems.Thm_Light_Ends_callToThen
import Theorems.Thm_Light_Ends_iteLast
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_setToThen
import Theorems.Thm_Light_Ends_skip
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_Need_Ok_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_SolvedIn_mono
import Theorems.Thm_Light_SolvesN_meets
import Theorems.Thm_Light_Solves_meets
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
theorem _root_.solution (w : Wrap Q task dec) {P : Program} {p : ℕ} {Tn : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Need}
    (hsol : Solves task P p Tn need) (κ : ℕ) (x : Bounded Q) (hn : 1 ≤ x.n) (hU : x.U = x.n ^ κ) {lim : Limits}
    (hroom : w.Room need x lim) :
    Ends lim (P ++ [topBody κ p w.args dec]) 1 (topBody κ p w.args dec) ⟨frame [0, 0], memOf ((ofEnd Q).input x)⟩
      (Tn x.n x.U + w.bodySteps κ) (Answered x dec) :=
  by
  have hbound := hroom.bound
  have hcells := hroom.cells
  have hdepth := hroom.depth
  have hcst : x.n * x.n + 1 ≤ w.cst * (x.n * x.n + 1) := Nat.le_mul_of_pos_left _ w.cst_pos
  have hsquare : ((x.n * x.n : ℕ) : ℤ) ≤ lim.word := le_trans (Nat.cast_le.2 (by omega)) hcells
  have hU1 : 1 ≤ x.U := hU ▸ Nat.one_le_pow _ _ hn
  push_cast at hbound hsquare
  unfold topBody bodySteps
  refine
    Ends.setToThen (x.n : ℤ) ?_
      ⟨safe_cell0 (by omega) hroom.space, ofEnd_cell0 x _⟩
        -- if n ≠ 0
        
  refine
    Ends.iteLast (fun h => absurd h (by simp; omega))
      (fun _ => ?_)
        -- U := 1
        
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine
      _root_.Light.Ends.setToThen
        1
          -- U := U * n, κ times
          
        ?_ ?_ ?_
    on_goal -1 =>
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
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine Ends.next (4 * κ) ((pow_spec hn 0 _ κ (by rw [← hU]; omega)).mono le_rfl ?_)
  rintro _ rfl
  rw [← hU]
    -- local 3 := n * n
    
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine
      _root_.Light.Ends.setToThen
        (x.n * x.n : ℕ)
          -- result := solver(…)
          
        ?_ ?_ ?_
    on_goal -1 =>
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
            | (ring_nf; omega))
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
    try with_unfolding_none refine _root_.Light.Ends.skip ?_
  refine
    Ends.callToThen
      (hsol.meets _ (w.inst x) (w.fr x) (w.pre x hn hU1) (by rw [w.size_eq, w.bound_eq]; exact hroom.solver)) ?_
      ⟨w.safe x lim _ rfl rfl rfl hcells, w.vals x _ rfl rfl rfl⟩ (by omega)
      (by
        rw [w.size_eq, w.bound_eq]
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
  intro r μ' hpost
  rw [w.size_eq, w.bound_eq]
  have hanswer := w.post x r μ' hn hpost
  cases dec
  ·
    exact
      Ends.set
        (by
          simp only [_root_.Light.Expr.Safe, _root_.Light.Expr.val, _root_.Light.Expr.cost, _root_.Light.Op.eval,
            _root_.Light.Cond.Holds, _root_.Light.Cond.cost, _root_.Light.Cond.Safe, _root_.Function.update_apply,
            _root_.reduceIte, _root_.true_and, _root_.and_true, _root_.Nat.reduceEqDiff, _root_.Nat.cast_ofNat,
            _root_.Nat.cast_zero, _root_.Nat.cast_one, ];
          omega)
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
        (by simpa [Answered] using hanswer)
  · exact Ends.skip (by simpa [Answered] using hanswer)
end Light.Wrap
