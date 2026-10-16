-- Prove2me | solution 1 for MIPRE.Cost.Prog.parseLoop_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:19:35.788473+00:00
-- url     : https://prove2.me/submissions/7d145bc1-00d6-4117-ae79-0303a78c27d0

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Serial.lean (solution of MIPRE.Cost.Prog.parseLoop_runs);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
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
import Definitions.Def_MIPRE_Foundations_Halting_Serial

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Prog
open Data
theorem parseBody_wellScoped : parseBody.WellScoped 1 := by simp [parseBody, WellScoped]
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
open Data
theorem parseBody_stop (s : List Data) :
    ∃ t ≤ (list s).size + 20,
      Eval [Data.cons (encode ([] : BitStr)) (list s)] parseBody (Data.cons Data.nil (s.headD Data.nil)) t := by
  cases s with
  | nil =>
    refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := encode ([] : BitStr)) (b := list ([] : List Data)) (by simp)
      (Eval.elim_nil (i := 0) (by simp [encode_bitStr_nil])
      (Eval.cons (Eval.nil _) (Eval.elim_nil (i := 1) (by simp) (Eval.nil _))))⟩
    ((try simp only [MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)
  | cons top s' =>
    refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := encode ([] : BitStr)) (b := list (top :: s')) (by simp)
      (Eval.elim_nil (i := 0) (by simp [encode_bitStr_nil])
      (Eval.cons (Eval.nil _) (Eval.elim_cons (i := 1) (a := top) (b := list s') (by simp) (Eval.var_of_get (i := 0) (v := top) (by simp)))))⟩
    ((try simp only [MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
open Data
theorem parseBody_false (x : BitStr) (s : List Data) :
    ∃ t ≤ (encode x : Data).size + (list s).size + 20,
      Eval [Data.cons (encode (false :: x)) (list s)] parseBody
        (Data.cons (Data.cons Data.nil Data.nil) (Data.cons (encode x) (list (stackStep s false)))) t := by
  simp only [stackStep_false, list_cons]
  refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := encode (false :: x)) (b := list s) (by simp)
    (Eval.elim_cons (i := 0) (a := Data.nil) (b := encode x) (by simp [encode_bitStr_cons, ofBool])
    (Eval.elim_nil (i := 0) (by simp)
    (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.cons (Eval.var_of_get (i := 1) (v := encode x) (by simp)) (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 3) (v := list s) (by simp)))))))⟩
  ((try simp only [MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
open Data
theorem parseBody_true (x : BitStr) (s : List Data) :
    ∃ t ≤ (encode x : Data).size + (list s).size + 20,
      Eval [Data.cons (encode (true :: x)) (list s)] parseBody
        (Data.cons (Data.cons Data.nil Data.nil) (Data.cons (encode x) (list (stackStep s true)))) t := by
  rcases s with _ | ⟨top, _ | ⟨top2, s''⟩⟩
  · rw [show stackStep [] true = [] by simp [stackStep]]
    refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := encode (true :: x)) (b := list ([] : List Data)) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.cons Data.nil Data.nil) (b := encode x) (by simp [encode_bitStr_cons, ofBool])
      (Eval.elim_cons (i := 0) (a := Data.nil) (b := Data.nil) (by simp)
      (Eval.elim_nil (i := 5) (by simp)
      (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.cons (Eval.var_of_get (i := 3) (v := encode x) (by simp)) (Eval.var_of_get (i := 5) (v := list ([] : List Data)) (by simp)))))))⟩
    ((try simp only [MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)
  · rw [show stackStep [top] true = [top] by simp [stackStep]]
    refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := encode (true :: x)) (b := list [top]) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.cons Data.nil Data.nil) (b := encode x) (by simp [encode_bitStr_cons, ofBool])
      (Eval.elim_cons (i := 0) (a := Data.nil) (b := Data.nil) (by simp)
      (Eval.elim_cons (i := 5) (a := top) (b := list ([] : List Data)) (by simp)
      (Eval.elim_nil (i := 1) (by simp)
      (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.cons (Eval.var_of_get (i := 5) (v := encode x) (by simp)) (Eval.var_of_get (i := 7) (v := list [top]) (by simp))))))))⟩
    ((try simp only [MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)
  · simp only [stackStep_true_cons_cons, list_cons]
    refine ⟨_, ?_, Eval.elim_cons (i := 0) (a := encode (true :: x)) (b := list (top :: top2 :: s'')) (by simp)
      (Eval.elim_cons (i := 0) (a := Data.cons Data.nil Data.nil) (b := encode x) (by simp [encode_bitStr_cons, ofBool])
      (Eval.elim_cons (i := 0) (a := Data.nil) (b := Data.nil) (by simp)
      (Eval.elim_cons (i := 5) (a := top) (b := list (top2 :: s'')) (by simp)
      (Eval.elim_cons (i := 1) (a := top2) (b := list s'') (by simp)
      (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.cons (Eval.var_of_get (i := 7) (v := encode x) (by simp)) (Eval.cons (Eval.cons (Eval.var_of_get (i := 0) (v := top2) (by simp)) (Eval.var_of_get (i := 2) (v := top) (by simp))) (Eval.var_of_get (i := 1) (v := list s'') (by simp)))))))))⟩
    ((try simp only [MIPRE.Cost.Data.list_cons, MIPRE.Cost.Data.list_nil, MIPRE.Cost.Data.size_cons, MIPRE.Cost.Data.size_nil, MIPRE.Cost.encode_bool, MIPRE.Cost.Data.ofBool]) <;> omega)
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
open Data
/-- The stack size grows by at most two per step. -/
theorem size_list_stackStep (s : List Data) (b : Bool) :
    (list (stackStep s b)).size ≤ (list s).size + 2 := by
  cases b
  · simp only [stackStep_false, list_cons, size_cons, size_nil]; omega
  · rcases s with _ | ⟨top, _ | ⟨top2, s''⟩⟩
    · simp [stackStep]
    · simp [stackStep]
    · simp only [stackStep_true_cons_cons, list_cons, size_cons]; omega
end MIPRE.Cost.Prog

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution (x : BitStr) (s : List Data) (env : Env) (S : ℕ)
    (hS : (encode x : Data).size + (list s).size + 2 * x.length ≤ S) :
    ∃ t ≤ (x.length + 1) * (S + 21),
      Eval (Data.cons (encode x) (list s) :: env) (.loop parseBody) ((stackRun x s).headD Data.nil) t := by
  induction x generalizing s with
  | nil =>
    obtain ⟨t, ht, hrun⟩ := parseBody_stop s
    have hstop := Eval.loop_stop (Eval.append_of_wellScoped hrun parseBody_wellScoped env)
    refine ⟨t + 1, ?_, by simpa using hstop⟩
    simp only [List.length_nil, encode_bitStr_nil, Data.size_nil] at hS ⊢
    omega
  | cons b x ih =>
    have hS' : (encode x : Data).size + (list (stackStep s b)).size + 2 * x.length ≤ S := by
      have := size_list_stackStep s b
      simp only [encode_bitStr_cons, Data.size_cons, List.length_cons] at hS
      have := size_pos (ofBool b)
      omega
    obtain ⟨t', ht', hrun'⟩ := ih (stackStep s b) hS'
    have h2 : (x.length + 1 + 1) * (S + 21) = (x.length + 1) * (S + 21) + (S + 21) := Nat.succ_mul _ _
    cases b
    · obtain ⟨t, ht, hrun⟩ := parseBody_false x s
      refine ⟨t + t' + 1, ?_, ?_⟩
      · simp only [encode_bitStr_cons, Data.size_cons, List.length_cons] at hS ⊢; omega
      · exact Eval.loop_step (Eval.append_of_wellScoped hrun parseBody_wellScoped env) hrun'
    · obtain ⟨t, ht, hrun⟩ := parseBody_true x s
      refine ⟨t + t' + 1, ?_, ?_⟩
      · simp only [encode_bitStr_cons, Data.size_cons, List.length_cons] at hS ⊢; omega
      · exact Eval.loop_step (Eval.append_of_wellScoped hrun parseBody_wellScoped env) hrun'
end MIPRE.Cost.Prog
