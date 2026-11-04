-- Prove2me | solution 1 for Light.Emod.reduce_ends_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:40:16.445658+00:00
-- url     : https://prove2.me/submissions/faa891e8-c05f-44d5-917b-9c617177da68

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Nat.Size
public import Mathlib.Tactic.NormNum
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Emod
public import Theorems.Thm_Light_mul_two_pow_le_iff
public import Theorems.Thm_Light_emodRounds_le
public import Theorems.Thm_Light_Ends_iteLast
public import Theorems.Thm_Light_Ends_setTo
public import Theorems.Thm_Light_Ends_skip
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
theorem _root_.solution (F : Pre lim Mo V fr) (haV : a ≤ V) {μ' : ℕ → ℤ} {t : ℤ}
    (tab : Table μ μ' Mo fr (emodRounds a Mo)) :
    Ends lim P d emodReduce ⟨frame [x, Mo, fr, a, emodRounds a Mo, t], μ'⟩ (24 * emodRounds a Mo + 4) fun σ' =>
      σ' = ⟨frame [x, Mo, fr, (a % Mo : ℕ), 0, t], μ'⟩ :=
  by
  (obtain ⟨⟩ := _root_.id F)
  have hK : emodRounds a Mo ≤ Nat.log 2 (V + 1) + 1 := emodRounds_le haV
  have hgt : a < Mo * 2 ^ emodRounds a Mo := not_le.1 fun h => absurd ((mul_two_pow_le_iff F.mod_pos).1 h) (lt_irrefl _)
  refine
    Ends.whileConst
      (fun i σ =>
        ∃ r : ℕ,
          σ = ⟨frame [x, Mo, fr, r, (emodRounds a Mo - i : ℕ), t], μ'⟩ ∧
            r < Mo * 2 ^ (emodRounds a Mo - i) ∧ r % Mo = a % Mo)
      (emodRounds a Mo) emodReduceRound.blockCost ?start ?round ?done (by simp [emodReduceRound]; omega)
  case start => exact ⟨a, by simp, by simpa using hgt, rfl⟩
  case done =>
    rintro _ ⟨r, rfl, hr, hmod⟩
    rw [Nat.sub_self] at hr ⊢
    have hra : r = a % Mo := by rw [← hmod, Nat.mod_eq_of_lt (by simpa using hr)]
    exact ⟨by simp; omega, by simp, by rw [hra]; rfl⟩
  case round =>
    rintro i _ hi ⟨r, rfl, hr, hmod⟩
    obtain ⟨c, hc⟩ : ∃ c, emodRounds a Mo - i = c + 1 := ⟨emodRounds a Mo - i - 1, by omega⟩
    rw [show emodRounds a Mo - (i + 1) = c by omega]
    rw [hc] at hr ⊢
    have hcell : μ' (fr + c) = ((Mo * 2 ^ c : ℕ) : ℤ) := tab.1 c (by omega)
    have hle : Mo * 2 ^ c ≤ a := (mul_two_pow_le_iff F.mod_pos).2 (by omega)
    have hsub : ∀ r' : ℕ, Mo * 2 ^ c ≤ r' → (r' - Mo * 2 ^ c) % Mo = r' % Mo := fun r' h => Nat.sub_mul_mod h
    rw [show Mo * 2 ^ (c + 1) = Mo * 2 ^ c + Mo * 2 ^ c by ring] at hr
    generalize Mo * 2 ^ c = m at hr hcell hle hsub ⊢
    refine
      ⟨by (
          (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega), by
        ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega), ?_⟩
    unfold emodReduceRound
    focus
      ((first
          | refine _root_.Light.Ends.seqSelf ?_
          | refine _root_.Light.Ends.skipLast ?_);
        repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_)
      refine _root_.Light.Ends.setToThen (c : ℕ) ?_ ?_ ?_
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
    refine Ends.iteLast (fun h => ?_) (fun h => ?_)
    · have hmr : m ≤ r := by
        simp [hcell] at h
        omega
      exact
        Ends.setTo (r - m : ℕ) ⟨r - m, rfl, by omega, by rw [hsub r hmr, hmod]⟩
          (by (
              (try have := _root_.Light.Std.space_le (by assumption))
              (try have := _root_.Light.Std.const_le (by assumption))
              simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcell] <;> omega))
    · have hrm : r < m := by
        simp [hcell] at h
        omega
      exact Ends.skip ⟨r, rfl, hrm, hmod⟩
end Light.Emod
