-- Prove2me | solution 1 for Light.emod_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:30:14.356895+00:00
-- url     : https://prove2.me/submissions/3fd57a10-3088-493e-9f1d-6dfb83110559

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.NormNum
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Emod
import Definitions.Def_WeightedCache3SUM_Alias_098d1280a620df21
import Definitions.Def_WeightedCache3SUM_Alias_acc0ea29d744b7ad
import Definitions.Def_WeightedCache3SUM_Alias_2b039bb07dd5c7dd
import Theorems.Thm_Light_Ends_iteThen
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_Ends_setToThen
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
open Light.Emod
variable {μ : ℕ → ℤ} {x : ℤ} {Mo V fr a : ℕ}
namespace Light.Emod
namespace _root_.Light
theorem _root_.solution {p : ℕ} (hp : P[p]? = some emodBody) (F : Pre lim Mo V fr) (hx : |x| ≤ (V : ℤ)) :
    Meets lim P p d [x, Mo, fr] μ (emodTime x.natAbs Mo) fun r μ' => r = x % (Mo : ℤ) ∧ Kept μ μ' fr :=
  by
  have hword := F.word
  have hax : ((x.natAbs : ℕ) : ℤ) = |x| := Int.natCast_natAbs x
  have haV : x.natAbs ≤ V := by omega
  refine .of_body hp ?_
  unfold emodTime
  generalize x.natAbs =
    a at hax haV ⊢
        -- count := 0; mult := M; the table; the subtractions; the sign
        
  have tail :
    Ends lim P d
      (_root_.Light.Stmt.seq (.set Count (k 0))
        (_root_.Light.Stmt.seq (.set Mult (v Modulus))
          (_root_.Light.Stmt.seq emodTable (_root_.Light.Stmt.seq emodReduce emodSign))))
      ⟨frame [x, Mo, fr, a], μ⟩ (43 * emodRounds a Mo + 26) fun σ' => σ'.loc 0 = x % (Mo : ℤ) ∧ Kept μ σ'.mem fr :=
    by
    refine Ends.setToThen (0 : ℕ) (Ends.setToThen (Mo : ℕ) ?_)
    refine Ends.next _ ((table_ends F haV).mono le_rfl ?_)
    rintro _ ⟨μ', rfl, tab⟩
    refine Ends.next _ ((reduce_ends F haV tab).mono le_rfl ?_)
    rintro _ rfl
    exact
      (sign_ends F hax).mono
        (by
          first
          | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
              first
              | omega
              | (ring_nf; omega))
          | omega
          |
            (simp [] <;> first
                | omega
                | (ring_nf; omega)))
        fun σ' h =>
        ⟨h.1, fun b hb => by rw [h.2]; exact tab.2 b hb⟩
          -- rest := |x|
          
  refine Ends.iteThen (fun hneg => ?_) (fun hpos => ?_)
  · have hneg : x < 0 := by simpa using hneg
    rw [abs_of_neg hneg] at hax
    exact
      Ends.setToThen (a : ℕ)
        (tail.mono
          (by
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [] <;> first
                  | omega
                  | (ring_nf; omega)))
          fun _ h => h)
  · have hpos : 0 ≤ x := by simpa using hpos
    rw [abs_of_nonneg hpos] at hax
    exact
      Ends.setToThen (a : ℕ)
        (tail.mono
          (by
            first
            | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost,
                  _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                first
                | omega
                | (ring_nf; omega))
            | omega
            |
              (simp [] <;> first
                  | omega
                  | (ring_nf; omega)))
          fun _ h => h)
end _root_.Light
end Light.Emod
