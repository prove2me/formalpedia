-- Prove2me | solution 1 for Light.cbrtCeil_meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:08:29.819728+00:00
-- url     : https://prove2.me/submissions/08fd405f-b63c-463e-9fc3-9ea845a75cc0

import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Theorems.Thm_Light_le_cbrtLeast_pow
import Theorems.Thm_Light_pow_lt_of_lt_cbrtLeast
import Theorems.Thm_Light_cbrtLeast_le_self
import Definitions.Def_WeightedCache3SUM_Alias_ddf946abc9d6a0ed
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_Light_Ends_whileBlock
import Theorems.Thm_Light_Limits_Addr_abs_le
import Theorems.Thm_Light_Meets_of_body
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
section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Logs
end Logs
open Logs
private theorem abs_cube_le {n i : ℕ} (hword : ((8 * n + 1 : ℕ) : ℤ) ≤ lim.word) (hi : i ≤ cbrtLeast n) :
    |(i : ℤ) * i| ≤ lim.word ∧ |(i : ℤ) * i * i| ≤ lim.word :=
  by
  have hcube : i * i * i ≤ 8 * n :=
    calc
      i * i * i = i ^ 3 := by ring
      _ ≤ cbrtLeast n ^ 3 := (Nat.pow_le_pow_left hi 3)
      _ ≤ 8 * n := cbrtLeast_pow_le n
  have hsquare : i * i ≤ i * i * i := by
    rcases Nat.eq_zero_or_pos i with rfl | h
    · simp
    · exact Nat.le_mul_of_pos_right _ h
  have hcube' : (i : ℤ) * i * i ≤ 8 * n := by exact_mod_cast hcube
  have hsquare' : (i : ℤ) * i ≤ 8 * n := by exact_mod_cast hsquare.trans hcube
  have h2 : (0 : ℤ) ≤ (i : ℤ) * i := by positivity
  have h3 : (0 : ℤ) ≤ (i : ℤ) * i * i := by positivity
  push_cast at hword
  exact ⟨abs_le.2 ⟨by omega, by omega⟩, abs_le.2 ⟨by omega, by omega⟩⟩
end Light
set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
open Logs
namespace Light
theorem _root_.solution {p n : ℕ} (hp : P[p]? = some cbrtCeilBody) (μ : ℕ → ℤ)
    (hword : ((8 * n + 1 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [n] μ (cbrtCeilTime n) fun r μ' => r = (cbrtLeast n : ℤ) ∧ μ' = μ :=
  by
  have hsn : cbrtLeast n ≤ n := cbrtLeast_le_self n
  refine .of_body hp ?_
  unfold cbrtCeilBody cbrtCeilTime
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
        0
          -- while s³ < n.  Before round i, s = i.
          
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
  refine Ends.next _ (Ends.whileBlock (fun i σ => σ = ⟨frame [n, i], μ⟩) (cbrtLeast n) (by simp) ?round ?done le_rfl)
  case round =>
    rintro i _ hi rfl
    have hlt : (i : ℤ) * i * i < n := by
      have := pow_lt_of_lt_cbrtLeast hi
      rw [show i ^ 3 = i * i * i by ring] at this
      exact_mod_cast this
    exact
      ⟨by simpa using abs_cube_le hword hi.le, by simpa using hlt, by
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega), by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    have hle : (n : ℤ) ≤ (cbrtLeast n : ℤ) * cbrtLeast n * cbrtLeast n :=
      by
      have := le_cbrtLeast_pow n
      rw [show cbrtLeast n ^ 3 = cbrtLeast n * cbrtLeast n * cbrtLeast n by ring] at this
      exact_mod_cast this
    refine
      ⟨by simpa using abs_cube_le hword le_rfl, by simpa using hle, ?_⟩
        -- the result is s
        
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (cbrtLeast n) ?_ ?_ ?_
      on_goal -1 =>
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
              | (ring_nf; omega))
      on_goal -1 =>
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
      try with_unfolding_none refine _root_.Light.Ends.skip ?_
    exact ⟨rfl, rfl⟩
end Light
