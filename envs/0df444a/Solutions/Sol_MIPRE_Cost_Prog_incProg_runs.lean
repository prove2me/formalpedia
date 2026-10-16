-- Prove2me | solution 1 for MIPRE.Cost.Prog.incProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:00:22.982029+00:00
-- url     : https://prove2.me/submissions/8caae84f-c836-4e4d-a979-fa7183095ff9

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Arith.lean (solution of MIPRE.Cost.Prog.incProg_runs);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Linarith
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
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Theorems.Thm_MIPRE_Cost_Prog_incLoop_runs
import Theorems.Thm_MIPRE_Cost_Prog_revOntoProg_runs

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Data
open Polynomial
theorem incAcc_spec (l acc : BitStr) :
    (incAcc l acc).1.reverse ++ (incAcc l acc).2 = acc.reverse ++ inc l := by
  induction l generalizing acc with
  | nil => simp [incAcc, inc]
  | cons b l ih =>
    cases b
    · simp [incAcc, inc]
    · simp only [incAcc, inc, ih (false :: acc), List.reverse_cons, List.append_assoc,
        List.singleton_append]
end MIPRE.Cost.Data

namespace MIPRE.Cost.Data
open Polynomial
theorem incAcc_length (l acc : BitStr) :
    (incAcc l acc).1.length + (incAcc l acc).2.length ≤ l.length + acc.length + 1 := by
  induction l generalizing acc with
  | nil => simp [incAcc]
  | cons b l ih =>
    cases b
    · simp only [incAcc, List.length_cons]; omega
    · have := ih (false :: acc)
      simp only [incAcc, List.length_cons] at this ⊢; omega
end MIPRE.Cost.Data

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Polynomial
open Data
theorem _root_.solution (l : BitStr) :
    ∃ t ≤ (l.length + 2) * (8 * (encode l : Data).size + 8 * l.length + 60),
      incProg.Runs (encode l) (encode (inc l)) t := by
  have hsz : (encode l : Data).size ≤ 4 * l.length + 1 := esize_bitStr_le l
  obtain ⟨t₁, ht₁, h₁⟩ := incLoop_runs l [] [encode l] ((encode l : Data).size + 3 * l.length + 1)
    (by simp only [encode_bitStr_nil, Data.size_nil]; omega)
  -- phase 2
  set a := (incAcc l []).1 with ha
  set r := (incAcc l []).2 with hr
  have hlen : a.length + r.length ≤ l.length + 1 := by
    have := incAcc_length l []; simp only [List.length_nil] at this; omega
  have hspec : a.reverse ++ r = inc l := by
    have := incAcc_spec l []; simpa using this
  obtain ⟨t₂, ht₂, h₂⟩ := revOntoProg_runs (a.map Data.ofBool) (r.map Data.ofBool)
    [Data.cons (encode l) .nil, encode l] (4 * (l.length + 1) + 2)
    (by
      rw [← encode_bitStr_eq_list, ← encode_bitStr_eq_list]
      have := esize_bitStr_le a
      have := esize_bitStr_le r
      simp only [esize] at *
      omega)
  have hpre := Eval.cons (Eval.var_of_get (env := [encode l]) (i := 0) (v := encode l) (by simp))
    (Eval.nil [encode l])
  have h₁' : Eval [Data.cons (encode l) .nil, encode l] (.loop incBody)
      (Data.cons (encode a) (encode r)) t₁ := by
    have : Data.cons (encode l) (encode ([] : BitStr)) = Data.cons (encode l) .nil := by
      simp [encode_bitStr_nil]
    rw [this] at h₁
    exact h₁
  have h₂' : Eval [Data.cons (encode a) (encode r), Data.cons (encode l) .nil, encode l]
      revOntoProg (encode (inc l)) t₂ := by
    rw [← hspec]
    simp only [encode_bitStr_eq_list, List.map_append, List.map_reverse] at h₂ ⊢
    exact h₂
  refine ⟨_, ?_, Eval.let_ hpre (Eval.let_ h₁' h₂')⟩
  · have hA : t₁ ≤ (l.length + 1) * ((encode l : Data).size + 3 * l.length + 22) := ht₁
    have hB : t₂ ≤ (l.length + 2) * (4 * l.length + 18) := by
      refine ht₂.trans ?_
      simp only [List.length_map]
      exact Nat.mul_le_mul (by omega) (by omega)
    have h3 : (l.length + 1) * ((encode l : Data).size + 3 * l.length + 22) ≤
        (l.length + 2) * ((encode l : Data).size + 3 * l.length + 22) :=
      Nat.mul_le_mul_right _ (by omega)
    have h4 : (l.length + 2) * ((encode l : Data).size + 3 * l.length + 22) +
        (l.length + 2) * (4 * l.length + 18) + (encode l : Data).size + 5 ≤
        (l.length + 2) * (8 * (encode l : Data).size + 8 * l.length + 60) := by
      nlinarith
    ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool, MIPRE.Cost.encode_bitStr_nil, Bool.toNat_false, Bool.toNat_true]) <;> omega)
end MIPRE.Cost.Prog
