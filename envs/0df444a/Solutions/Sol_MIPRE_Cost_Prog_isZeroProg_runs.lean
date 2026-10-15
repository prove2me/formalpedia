-- Prove2me | solution 1 for MIPRE.Cost.Prog.isZeroProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:50:26.787984+00:00
-- url     : https://prove2.me/submissions/e352eb20-8fe6-4379-b8d9-10eedd5400af

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Numeric.lean (solution of MIPRE.Cost.Prog.isZeroProg_runs);
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
namespace MIPRE.Cost.Prog
theorem isZeroBody_wellScoped : isZeroBody.WellScoped 1 := by
  simp [isZeroBody, WellScoped]
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
theorem isZeroBody_stop : Eval [encode ([] : BitStr)] isZeroBody (.cons .nil .nil) 4 :=
  Eval.elim_nil (env := [encode ([] : BitStr)]) (i := 0)
    (c := .elim 0 (.cons (.cons .nil .nil) (.var 1)) (.cons .nil (.cons .nil .nil))) (by simp)
    (Eval.cons (Eval.nil _) (Eval.nil _))
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
theorem isZeroBody_false (l : BitStr) :
    Eval [encode (false :: l)] isZeroBody (.cons (.cons .nil .nil) (encode l))
      ((encode l).size + 7) := by
  have e := Eval.elim_cons (env := [encode (false :: l)]) (i := 0) (n := .cons .nil .nil)
    (a := .nil) (b := encode l) (by simp)
    (Eval.elim_nil (i := 0) (c := .cons .nil (.cons .nil .nil)) (by simp)
      (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
        (Eval.var_of_get (i := 1) (v := encode l) (by simp))))
  exact e.cast_cost (by omega)
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
theorem isZeroBody_true (l : BitStr) :
    Eval [encode (true :: l)] isZeroBody (.cons .nil (.cons .nil .nil)) 7 :=
  Eval.elim_cons (env := [encode (true :: l)]) (i := 0) (n := .cons .nil .nil)
    (a := .cons .nil .nil) (b := encode l) (by simp)
    (Eval.elim_cons (i := 0) (n := .cons (.cons .nil .nil) (.var 1)) (a := .nil) (b := .nil)
      (by simp)
      (Eval.cons (Eval.nil _) (Eval.cons (Eval.nil _) (Eval.nil _))))
end MIPRE.Cost.Prog

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
theorem solution (l : BitStr) (env : Env) (S : ℕ) (hS : (encode l).size ≤ S) :
    ∃ t ≤ (l.length + 1) * (S + 8),
      Eval (encode l :: env) isZeroProg (encode (l.any id)) t := by
  induction l with
  | nil =>
    refine ⟨5, ?_, ?_⟩
    · simp only [List.length_nil, Nat.zero_add, Nat.one_mul]; omega
    · simpa [isZeroProg] using Eval.loop_stop
        (Eval.append_of_wellScoped isZeroBody_stop isZeroBody_wellScoped env)
  | cons b l ih =>
    cases b with
    | false =>
      have hS' : (encode l).size ≤ S := by
        simp only [encode_bitStr_cons, Data.size_cons, Data.ofBool_false, Data.size_nil] at hS
        omega
      obtain ⟨t, ht, hrun⟩ := ih hS'
      refine ⟨(encode l).size + 7 + t + 1, ?_, ?_⟩
      · have h2 : (l.length + 1 + 1) * (S + 8) = (l.length + 1) * (S + 8) + (S + 8) :=
          Nat.succ_mul _ _
        simp only [List.length_cons]
        omega
      · have hstep := Eval.append_of_wellScoped (isZeroBody_false l) isZeroBody_wellScoped env
        have := Eval.loop_step hstep hrun
        simpa [isZeroProg] using this
    | true =>
      refine ⟨8, ?_, ?_⟩
      · have h1 : S + 8 ≤ ((true :: l).length + 1) * (S + 8) :=
          Nat.le_mul_of_pos_left _ (by omega)
        omega
      · have := Eval.loop_stop
          (Eval.append_of_wellScoped (isZeroBody_true l) isZeroBody_wellScoped env)
        simpa [isZeroProg] using this
