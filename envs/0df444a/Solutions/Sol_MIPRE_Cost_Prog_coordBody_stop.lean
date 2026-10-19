-- Prove2me | solution 1 for MIPRE.Cost.Prog.coordBody_stop
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:32:51.262209+00:00
-- url     : https://prove2.me/submissions/982626e7-a515-4d10-a786-50c9507ac865

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/DecLoop.lean (solution of MIPRE.Cost.Prog.coordBody_stop);
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
import Theorems.Thm_MIPRE_Cost_Prog_finalProg_runs

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Cost.Prog
section
open Data
theorem finalProg_wellScoped : finalProg.WellScoped 1 := by simp [finalProg, WellScoped]
end
end MIPRE.Cost.Prog

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution (univ : Prog) (remX remY remA remB : List Data) (ctx : Data) :
    ∃ t ≤ (list remX).size + (list remY).size + (list remA).size + (list remB).size + ctx.size + 24,
      Eval [decState (ofNat 0) remX remY remA remB ctx] (coordBody univ)
        (.cons .nil (ofBool (decide (remA = [] ∧ remB = [])))) t := by
  obtain ⟨t, ht, h⟩ := finalProg_runs remX remY remA remB ctx
  have run : Eval [decState (ofNat 0) remX remY remA remB ctx] (coordBody univ)
      (.cons .nil (ofBool (decide (remA = [] ∧ remB = [])))) _ :=
    Eval.elim_cons (i := 0) (n := .nil) (a := ofNat 0)
      (b := .cons (list remX) (.cons (list remY) (.cons (list remA) (.cons (list remB) ctx))))
      (by simp [decState])
      (Eval.elim_nil (i := 0) (by simp [ofNat])
        (callVar_eval finalProg_wellScoped (i := 1)
          (v := .cons (list remX) (.cons (list remY) (.cons (list remA) (.cons (list remB) ctx))))
          (by simp) h))
  refine ⟨_, ?_, run⟩
  simp only [size_cons]
  omega
end MIPRE.Cost.Prog
