-- Prove2me | solution 1 for MIPRE.Cost.Prog.okBits_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:30:40.830237+00:00
-- url     : https://prove2.me/submissions/70f159c8-624b-41c6-ab80-7e9dd507d488

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/DecLoop.lean (solution of MIPRE.Cost.Prog.okBits_iff);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_Repeat_MapLoop
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Repeat_DecLoop

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Data
section
/-- On a bit list and a list budget: the walk stops with the remainders. -/
theorem bitWalk_encode (x : BitStr) (u : List Data) :
    bitWalk (encode x) (list u) =
      cons (encode (x.drop u.length)) (list (u.drop x.length)) := by
  induction x generalizing u with
  | nil => simp [bitWalk, encode_bitStr_nil]
  | cons b x ih =>
    cases u with
    | nil => simp [bitWalk, encode_bitStr_cons]
    | cons c u => simp [bitWalk, encode_bitStr_cons, ih]
end
end MIPRE.Cost.Data

namespace MIPRE.Cost.Prog
section
open Data
theorem isBit_iff (d : Data) : isBit d = true ↔ ∃ b : Bool, d = ofBool b := by
  constructor
  · intro h
    rcases d with _ | ⟨_ | ⟨a, b⟩, _ | ⟨c, e⟩⟩
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
    all_goals simp [isBit] at h
  · rintro ⟨b, rfl⟩
    exact isBit_ofBool b
end
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
section
open Data
theorem okBits_encode (B : ℕ) (x : BitStr) : okBits B (encode x) = decide (x.length ≤ B) := by
  unfold okBits
  rw [ofNat_eq_list_replicate, bitWalk_encode, List.length_replicate]
  by_cases h : x.length ≤ B
  · rw [List.drop_of_length_le h]
    simp [h]
  · obtain ⟨c, l, hl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos (by
      rw [List.length_drop]; omega) : x.drop B ≠ [])
    rw [hl]
    simp [h, encode_bitStr_cons, ofBool]
end
end MIPRE.Cost.Prog

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution (B : ℕ) (d : Data) :
    okBits B d = true ↔ ∃ x : BitStr, d = encode x ∧ x.length ≤ B := by
  constructor
  · induction d generalizing B with
    | nil => intro _; exact ⟨[], rfl, by simp⟩
    | cons h l _ ih =>
      intro hok
      cases B with
      | zero => simp [okBits, bitWalk, ofNat] at hok
      | succ B =>
        simp only [okBits, ofNat, bitWalk] at hok
        by_cases hb : isBit h = true
        · rw [if_pos hb] at hok
          obtain ⟨b, rfl⟩ := (isBit_iff h).mp hb
          obtain ⟨x, rfl, hx⟩ := ih B (by unfold okBits; exact hok)
          exact ⟨b :: x, rfl, by simp; omega⟩
        · rw [if_neg hb] at hok
          simp at hok
  · rintro ⟨x, rfl, hx⟩
    rw [okBits_encode]
    simpa using hx
end MIPRE.Cost.Prog
