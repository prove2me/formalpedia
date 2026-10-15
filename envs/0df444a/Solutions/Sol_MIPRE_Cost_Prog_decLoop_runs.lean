-- Prove2me | solution 1 for MIPRE.Cost.Prog.decLoop_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:49:05.221992+00:00
-- url     : https://prove2.me/submissions/110f45a1-980c-448c-beb3-0992f8de2f50

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Numeric.lean (solution of MIPRE.Cost.Prog.decLoop_runs);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost
theorem size_encode_replicate_true (j : ℕ) :
    (encode (List.replicate j true)).size = 4 * j + 1 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [List.replicate_succ, encode_bitStr_cons, Data.size_cons, Data.ofBool_true,
      Data.size_nil, ih]
    omega
end MIPRE.Cost

namespace MIPRE.Cost
theorem size_encode_replicate_false_append (j : ℕ) (rest : BitStr) :
    (encode (List.replicate j false ++ true :: rest)).size = 2 * j + (encode rest).size + 4 := by
  induction j with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, encode_bitStr_cons, Data.size_cons,
      Data.ofBool_true, Data.size_nil]
    omega
  | succ j ih =>
    simp only [List.replicate_succ, List.cons_append, encode_bitStr_cons, Data.size_cons,
      Data.ofBool_false, Data.size_nil, ih]
    omega
end MIPRE.Cost

namespace MIPRE.Cost.Prog
theorem decBody_wellScoped : decBody.WellScoped 1 := by
  simp [decBody, WellScoped]
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
theorem decBody_false (l acc : BitStr) :
    Eval [.cons (encode (false :: l)) (encode acc)] decBody
      (.cons (.cons .nil .nil) (.cons (encode l) (encode (true :: acc))))
      ((encode l).size + (encode acc).size + 14) := by
  have e := Eval.elim_cons (env := [Data.cons (encode (false :: l)) (encode acc)]) (i := 0)
    (n := .nil) (a := encode (false :: l)) (b := encode acc) (by simp)
    (Eval.elim_cons (i := 0) (n := .cons .nil (.cons (.var 1) .nil)) (a := .nil)
      (b := encode l) (by simp)
      (Eval.elim_nil (i := 0) (c := .cons .nil (.cons (.cons .nil (.var 5)) (.var 3)))
        (by simp)
        (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
          (Eval.cons (Eval.var_of_get (i := 1) (v := encode l) (by simp))
            (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
              (Eval.var_of_get (i := 3) (v := encode acc) (by simp)))))))
  exact e.cast_cost (by omega)
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
theorem decBody_true (l acc : BitStr) :
    Eval [.cons (encode (true :: l)) (encode acc)] decBody
      (.cons .nil (.cons (encode (false :: acc)) (encode l)))
      ((encode l).size + (encode acc).size + 10) := by
  have e := Eval.elim_cons (env := [Data.cons (encode (true :: l)) (encode acc)]) (i := 0)
    (n := .nil) (a := encode (true :: l)) (b := encode acc) (by simp)
    (Eval.elim_cons (i := 0) (n := .cons .nil (.cons (.var 1) .nil)) (a := .cons .nil .nil)
      (b := encode l) (by simp)
      (Eval.elim_cons (i := 0)
        (n := .cons (.cons .nil .nil) (.cons (.var 1) (.cons (.cons .nil .nil) (.var 3))))
        (a := .nil) (b := .nil) (by simp)
        (Eval.cons (Eval.nil _)
          (Eval.cons
            (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 5) (v := encode acc) (by simp)))
            (Eval.var_of_get (i := 3) (v := encode l) (by simp))))))
  exact e.cast_cost (by omega)
end MIPRE.Cost.Prog

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
theorem solution (j : ℕ) (rest : BitStr) (i : ℕ) (env : Env) (S : ℕ)
    (hS : 2 * j + (encode rest).size + 4 + (4 * i + 1) + 2 * j ≤ S) :
    ∃ t ≤ (j + 1) * (S + 15),
      Eval (.cons (encode (List.replicate j false ++ true :: rest))
          (encode (List.replicate i true)) :: env) (.loop decBody)
        (.cons (encode (false :: List.replicate (i + j) true)) (encode rest)) t := by
  induction j generalizing i with
  | zero =>
    refine ⟨(encode rest).size + (encode (List.replicate i true)).size + 10 + 1, ?_, ?_⟩
    · rw [size_encode_replicate_true]
      simp only [Nat.zero_add, Nat.one_mul]
      omega
    · have := Eval.loop_stop
        (Eval.append_of_wellScoped (decBody_true rest (List.replicate i true))
          decBody_wellScoped env)
      simpa using this
  | succ j ih =>
    have hS' : 2 * j + (encode rest).size + 4 + (4 * (i + 1) + 1) + 2 * j ≤ S := by omega
    obtain ⟨t, ht, hrun⟩ := ih (i + 1) hS'
    refine ⟨(encode (List.replicate j false ++ true :: rest)).size +
        (encode (List.replicate i true)).size + 14 + t + 1, ?_, ?_⟩
    · rw [size_encode_replicate_false_append, size_encode_replicate_true]
      have h2 : (j + 1 + 1) * (S + 15) = (j + 1) * (S + 15) + (S + 15) := Nat.succ_mul _ _
      omega
    · have hstep := Eval.append_of_wellScoped
        (decBody_false (List.replicate j false ++ true :: rest) (List.replicate i true))
        decBody_wellScoped env
      have hrun' : Eval (Data.cons (encode (List.replicate j false ++ true :: rest))
          (encode (true :: List.replicate i true)) :: env) (.loop decBody)
          (.cons (encode (false :: List.replicate (i + (j + 1)) true)) (encode rest)) t := by
        rw [show i + (j + 1) = i + 1 + j by omega]
        simpa [List.replicate_succ] using hrun
      have := Eval.loop_step hstep hrun'
      simpa [List.replicate_succ] using this
