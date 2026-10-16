-- Prove2me | solution 1 for MIPRE.Cost.Prog.incLoop_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T19:59:00.495085+00:00
-- url     : https://prove2.me/submissions/7873f044-2217-4b48-9e64-8aa6c1121efc

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Arith.lean (solution of MIPRE.Cost.Prog.incLoop_runs);
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Prog
open Polynomial
open Data
theorem incBody_wellScoped : incBody.WellScoped 1 := by simp [incBody, WellScoped]
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
open Polynomial
open Data
theorem incBody_nil (acc : BitStr) :
    ∃ t ≤ (encode acc : Data).size + 20,
      Eval [Data.cons (encode ([] : BitStr)) (encode acc)] incBody
        (Data.cons Data.nil (Data.cons (encode (true :: acc)) (encode ([] : BitStr)))) t := by
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := encode ([] : BitStr)) (b := encode acc) (by simp)
    (Eval.elim_nil (i := 0) (by simp [encode_bitStr_nil])
      (Eval.cons (Eval.nil _) (Eval.cons (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
        (Eval.var_of_get (i := 1) (v := encode acc) (by simp))) (Eval.nil _))))⟩
  ((try simp only [MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.Data.size_ofNat, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool, MIPRE.Cost.encode_bitStr_nil, Bool.toNat_false, Bool.toNat_true]) <;> omega)
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
open Polynomial
open Data
theorem incBody_false (r acc : BitStr) :
    ∃ t ≤ (encode r : Data).size + (encode acc : Data).size + 20,
      Eval [Data.cons (encode (false :: r)) (encode acc)] incBody
        (Data.cons Data.nil (Data.cons (encode (true :: acc)) (encode r))) t := by
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := encode (false :: r)) (b := encode acc) (by simp)
    (Eval.elim_cons (i := 0) (a := Data.nil) (b := encode r) (by simp [encode_bitStr_cons, ofBool])
      (Eval.elim_nil (i := 0) (by simp)
        (Eval.cons (Eval.nil _) (Eval.cons (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
          (Eval.var_of_get (i := 3) (v := encode acc) (by simp)))
          (Eval.var_of_get (i := 1) (v := encode r) (by simp))))))⟩
  omega
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
open Polynomial
open Data
theorem incBody_true (r acc : BitStr) :
    ∃ t ≤ (encode r : Data).size + (encode acc : Data).size + 20,
      Eval [Data.cons (encode (true :: r)) (encode acc)] incBody
        (Data.cons (Data.cons Data.nil Data.nil) (Data.cons (encode r) (encode (false :: acc)))) t := by
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := encode (true :: r)) (b := encode acc) (by simp)
    (Eval.elim_cons (i := 0) (a := Data.cons Data.nil Data.nil) (b := encode r)
      (by simp [encode_bitStr_cons, ofBool])
      (Eval.elim_cons (i := 0) (a := Data.nil) (b := Data.nil) (by simp)
        (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
          (Eval.cons (Eval.var_of_get (i := 3) (v := encode r) (by simp))
            (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 5) (v := encode acc) (by simp)))))))⟩
  omega
end MIPRE.Cost.Prog

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Polynomial
open Data
theorem _root_.solution (l acc : BitStr) (env : Env) (S : ℕ)
    (hS : (encode l : Data).size + (encode acc : Data).size + 3 * l.length ≤ S) :
    ∃ t ≤ (l.length + 1) * (S + 21),
      Eval (Data.cons (encode l) (encode acc) :: env) (.loop incBody)
        (Data.cons (encode (incAcc l acc).1) (encode (incAcc l acc).2)) t := by
  induction l generalizing acc with
  | nil =>
    obtain ⟨t, ht, hrun⟩ := incBody_nil acc
    have hstop := Eval.loop_stop (Eval.append_of_wellScoped hrun incBody_wellScoped env)
    refine ⟨t + 1, ?_, by simpa [incAcc] using hstop⟩
    simp only [List.length_nil, encode_bitStr_nil, Data.size_nil] at hS ⊢
    omega
  | cons b l ih =>
    cases b
    · obtain ⟨t, ht, hrun⟩ := incBody_false l acc
      have hstop := Eval.loop_stop (Eval.append_of_wellScoped hrun incBody_wellScoped env)
      refine ⟨t + 1, ?_, by simpa [incAcc] using hstop⟩
      have : S + 21 ≤ (l.length + 1 + 1) * (S + 21) := Nat.le_mul_of_pos_left _ (by omega)
      simp only [encode_bitStr_cons, Data.size_cons, List.length_cons] at hS ⊢
      omega
    · obtain ⟨t, ht, hrun⟩ := incBody_true l acc
      have hS' : (encode l : Data).size + (encode (false :: acc) : Data).size + 3 * l.length ≤ S := by
        simp only [encode_bitStr_cons, Data.size_cons, List.length_cons, ofBool, Data.size_nil]
          at hS ⊢
        omega
      obtain ⟨t', ht', hrun'⟩ := ih (false :: acc) hS'
      refine ⟨t + t' + 1, ?_, ?_⟩
      · have h2 : (l.length + 1 + 1) * (S + 21) = (l.length + 1) * (S + 21) + (S + 21) :=
          Nat.succ_mul _ _
        simp only [encode_bitStr_cons, Data.size_cons, List.length_cons] at hS ⊢
        omega
      · have := Eval.loop_step (Eval.append_of_wellScoped hrun incBody_wellScoped env) hrun'
        simpa [incAcc] using this
end MIPRE.Cost.Prog
