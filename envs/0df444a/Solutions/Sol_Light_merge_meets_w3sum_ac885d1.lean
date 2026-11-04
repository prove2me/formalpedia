-- Prove2me | solution 1 for Light.merge_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:32:20.536789+00:00
-- url     : https://prove2.me/submissions/be238c1b-dd6d-474d-a136-25cc04bcf6b7

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Merge
import Theorems.Thm_Light_Merge_step_left
import Theorems.Thm_Light_Merge_step_right
import Theorems.Thm_Light_Merge_step_left_end
import Theorems.Thm_Light_Merge_step_right_end
import Theorems.Thm_Light_Merge_takeLeft
import Theorems.Thm_Light_Merge_takeRight
import Theorems.Thm_Light_Ends_whileBlock
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SameOn_refl
import Theorems.Thm_Light_SameOutside2_refl
import Theorems.Thm_Light_SameOutside_refl
import Theorems.Thm_Light_Seg_get
import Theorems.Thm_Light_Stmt_Runs_ite_neg
import Theorems.Thm_Light_Stmt_Runs_ite_pos
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
open Light.Merge
variable {μ : ℕ → ℤ} {a b dst : ℕ} {l r : List ℤ} {i j : ℕ}
namespace Light.Merge
namespace _root_.Light
theorem _root_.solution {p : ℕ} (hp : P[p]? = some mergeBody) (C : Pre lim μ a b dst l r) :
    Meets lim P p d [a, l.length, b, r.length, dst] μ (mergeTime (l.length + r.length)) fun _ μ' =>
      Seg μ' dst (l.merge r) ∧ SameOutside μ μ' dst (l.length + r.length) :=
  by
  (obtain ⟨⟩ := _root_.id C)
  refine .of_body hp ?_
  unfold mergeTime
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      repeat
        with_unfolding_none
          first
          | refine _root_.Light.Ends.seqAssoc ?_
          | refine _root_.Light.Ends.skipThen ?_)
    refine _root_.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
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
        (0 : ℕ)
          -- while i + j < na + nb
          
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
    Ends.whileBlock (Taken μ a b dst l r) (l.length + r.length) ?start ?round ?done
      (by simp [mergeTakeLeft, mergeTakeRight]; omega)
  case start => exact ⟨0, 0, rfl, μ, [], rfl, Nat.zero_le _, Nat.zero_le _, .refl, rfl, Seg.nil, by simp⟩
  case done =>
    rintro _ ⟨i, j, hij, μ', out, rfl, hi, hj, same, hlen, seg, hout⟩
    rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)] at hout
    exact
      ⟨by (
          (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega), by simp; omega, by
        simpa [← hout] using seg, same⟩
  case round =>
    rintro _ σ ht ⟨i, j, rfl, hI⟩
    have left := takeLeft C hI
    have right := takeRight C hI
    obtain ⟨μ', out, rfl, hi, hj, same, -⟩ := hI
    refine
      ⟨by (
          (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega), by simp; omega, ?_⟩
        -- The next output is the head of the first list unless the head of the second list is smaller.
        
    by_cases c1 : i < l.length
    · refine .ite_pos ?_
      by_cases c2 : j < r.length
      · have hreadL : μ' (a + i) = l[i] := (same _ (by omega)).trans (C.segL.get c1)
        have hreadR : μ' (b + j) = r[j] := (same _ (by omega)).trans (C.segR.get c2)
        refine .ite_pos ?_
        by_cases c3 : r[j] < l[i]
        · exact .ite_pos (right c2 (step_right c1 c2 c3)) (by simpa [hreadL, hreadR] using c3)
        · exact .ite_neg (left c1 (step_left c1 c2 (not_lt.1 c3))) (by simpa [hreadL, hreadR] using c3)
      · exact .ite_neg (left c1 (step_left_end c1 (by omega)))
    · exact .ite_neg (right (by omega) (step_right_end (by omega) (by omega)))
end _root_.Light
end Light.Merge
