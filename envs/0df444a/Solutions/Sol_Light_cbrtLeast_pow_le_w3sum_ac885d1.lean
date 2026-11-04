-- Prove2me | solution 1 for Light.cbrtLeast_pow_le_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:39:27.457967+00:00
-- url     : https://prove2.me/submissions/1ac7687a-65e7-4ae0-b014-7609ed6fbf7f

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
public import Theorems.Thm_Light_pow_lt_of_lt_cbrtLeast
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
open Logs
namespace Light
theorem _root_.solution (n : ℕ) : cbrtLeast n ^ 3 ≤ 8 * n := by
  rcases Nat.eq_zero_or_pos (cbrtLeast n) with h | h
  · simp [h]
  obtain ⟨s, hs⟩ : ∃ s, cbrtLeast n = s + 1 := ⟨cbrtLeast n - 1, by omega⟩
  have h1 : s ^ 3 < n := pow_lt_of_lt_cbrtLeast (by omega)
  rw [hs]
  rcases Nat.eq_zero_or_pos s with h0 | h0
  · subst h0
    omega
  · calc (s + 1) ^ 3 ≤ (2 * s) ^ 3 := Nat.pow_le_pow_left (by omega) 3
      _ = 8 * s ^ 3 := by ring
      _ ≤ 8 * n := by omega
end Light
