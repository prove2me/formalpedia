-- Prove2me | solution 1 for MIPRE.Cost.Data.canonWalk_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:17:51.581084+00:00
-- url     : https://prove2.me/submissions/5367d972-3781-4b5f-9582-97f951a2b7be

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Lists.lean (solution of MIPRE.Cost.Data.canonWalk_iff);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Data
theorem _root_.solution (d : Data) (b : Bool) :
    canonWalk d b = true ↔
      ∃ l : BitStr, d = encode l ∧ (l = [] → b = true) ∧ (l ≠ [] → l.getLast? = some true) := by
  induction d generalizing b with
  | nil =>
    simp only [canonWalk]
    constructor
    · intro hb; exact ⟨[], rfl, fun _ => hb, fun h => absurd rfl h⟩
    · rintro ⟨l, hl, h1, -⟩
      cases l with
      | nil => exact h1 rfl
      | cons c l => simp [encode_bitStr_cons] at hl
  | cons h r _ ihr =>
    have key : ∀ (b' : Bool), canonWalk r b' = true ↔ ∃ l : BitStr, cons (ofBool b') r = encode (b' :: l) ∧
        ((b' :: l) = [] → b = true) ∧ ((b' :: l) ≠ [] → (b' :: l).getLast? = some true) := by
      intro b'
      rw [ihr]
      constructor
      · rintro ⟨l, rfl, h1, h2⟩
        refine ⟨l, rfl, fun h => absurd h (List.cons_ne_nil _ _), fun _ => ?_⟩
        cases l with
        | nil => simpa using h1 rfl
        | cons c l => rw [List.getLast?_cons_cons]; exact h2 (List.cons_ne_nil _ _)
      · rintro ⟨l, hl, -, h2⟩
        refine ⟨l, ?_, fun hnil => ?_, fun hne => ?_⟩
        · rw [encode_bitStr_cons] at hl; exact (cons.inj hl).2
        · subst hnil; simpa using h2 (List.cons_ne_nil _ _)
        · have := h2 (List.cons_ne_nil _ _)
          cases l with
          | nil => exact absurd rfl hne
          | cons c l => rw [List.getLast?_cons_cons] at this; exact this
    rcases h with _ | ⟨_ | ⟨a1, a2⟩, _ | ⟨b1, b2⟩⟩
    · -- `h = nil`
      simp only [canonWalk]
      rw [key false]
      constructor
      · rintro ⟨l, hl, h1, h2⟩; exact ⟨false :: l, hl, h1, h2⟩
      · rintro ⟨l, hl, h1, h2⟩
        cases l with
        | nil => simp [encode_bitStr_nil] at hl
        | cons c l =>
          rw [encode_bitStr_cons] at hl
          have hc : ofBool c = nil := ((cons.inj hl).1).symm
          cases c
          · exact ⟨l, by rw [encode_bitStr_cons]; exact hl, h1, h2⟩
          · simp [ofBool] at hc
    · -- `h = cons nil nil`
      simp only [canonWalk]
      rw [key true]
      constructor
      · rintro ⟨l, hl, h1, h2⟩; exact ⟨true :: l, hl, h1, h2⟩
      · rintro ⟨l, hl, h1, h2⟩
        cases l with
        | nil => simp [encode_bitStr_nil] at hl
        | cons c l =>
          rw [encode_bitStr_cons] at hl
          have hc : ofBool c = cons nil nil := ((cons.inj hl).1).symm
          cases c
          · simp [ofBool] at hc
          · exact ⟨l, by rw [encode_bitStr_cons]; exact hl, h1, h2⟩
    all_goals
      simp only [canonWalk, Bool.false_eq_true, false_iff, not_exists, not_and]
      rintro l hl
      cases l with
      | nil => simp [encode_bitStr_nil] at hl
      | cons c l =>
        rw [encode_bitStr_cons] at hl
        have hc := (cons.inj hl).1
        cases c <;> simp [ofBool] at hc
end MIPRE.Cost.Data
