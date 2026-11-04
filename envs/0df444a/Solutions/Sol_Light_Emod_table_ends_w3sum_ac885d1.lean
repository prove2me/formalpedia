-- Prove2me | solution 1 for Light.Emod.table_ends_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:40:11.954594+00:00
-- url     : https://prove2.me/submissions/262326d7-8138-4cfa-ab8f-242461e80903

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Size
public import Mathlib.Tactic.NormNum
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Emod
public import Theorems.Thm_Light_mul_two_pow_le_iff
public import Theorems.Thm_Light_emodRounds_le
public import Theorems.Thm_Light_Ends_whileConst
public import Theorems.Thm_Light_sameFrame_cons_cons
public import Theorems.Thm_Light_sameFrame_cons_nil
public import Theorems.Thm_Light_sameFrame_nil
public import Theorems.Thm_Light_sameFrame_nil_cons
public import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
open Light.Emod
variable {μ : ℕ → ℤ} {x : ℤ} {Mo V fr a : ℕ}
namespace Light.Emod
theorem _root_.solution (F : Pre lim Mo V fr) (haV : a ≤ V) :
    Ends lim P d emodTable ⟨frame [x, Mo, fr, a, 0, Mo], μ⟩ (19 * emodRounds a Mo + 6) fun σ' =>
      ∃ μ',
        σ' = ⟨frame [x, Mo, fr, a, emodRounds a Mo, ((Mo * 2 ^ emodRounds a Mo : ℕ) : ℤ)], μ'⟩ ∧
          Table μ μ' Mo fr (emodRounds a Mo) :=
  by
  (obtain ⟨⟩ := _root_.id F)
  have hK : emodRounds a Mo ≤ Nat.log 2 (V + 1) + 1 := emodRounds_le haV
  refine
    Ends.whileConst (fun i σ => ∃ μ', σ = ⟨frame [x, Mo, fr, a, i, ((Mo * 2 ^ i : ℕ) : ℤ)], μ'⟩ ∧ Table μ μ' Mo fr i)
      (emodRounds a Mo) emodTableRound.blockCost ?start ?round ?done (by simp [emodTableRound]; omega)
  case start => exact ⟨μ, by simp, fun j hj => absurd hj (by omega), fun _ _ => rfl⟩
  case done =>
    rintro _ ⟨μ', rfl, tab⟩
    have hgt : ¬Mo * 2 ^ emodRounds a Mo ≤ a := fun h => absurd ((mul_two_pow_le_iff F.mod_pos).1 h) (lt_irrefl _)
    generalize Mo * 2 ^ emodRounds a Mo = t at hgt
    exact
      ⟨by (
          (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega), by simp; omega, μ', rfl, tab⟩
  case round =>
    rintro i _ hi ⟨μ', rfl, tab, below⟩
    have hle : Mo * 2 ^ i ≤ a := (mul_two_pow_le_iff F.mod_pos).2 hi
    have hnext : Mo * 2 ^ (i + 1) = Mo * 2 ^ i + Mo * 2 ^ i := by ring
    rw [hnext]
    generalize ht : Mo * 2 ^ i = t at hle
    refine
      ⟨by (
          (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega), by simp; omega, ?_⟩
    unfold emodTableRound
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.storeToThen (fr + i) t ?_ ?_ ?_
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
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (i + 1 : ℕ) ?_ ?_ ?_
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
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (t + t : ℕ) ?_ ?_ ?_
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
    refine ⟨_, rfl, fun j hj => ?_, fun b hb => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
      · rw [Function.update_of_ne (by omega)]
        exact tab j h
      · rw [Function.update_self, ht]
    · rw [Function.update_of_ne (by omega)]
      exact below b hb
end Light.Emod
