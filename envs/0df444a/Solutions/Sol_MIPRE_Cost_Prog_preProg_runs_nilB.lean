-- Prove2me | solution 1 for MIPRE.Cost.Prog.preProg_runs_nilB
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:32:43.385065+00:00
-- url     : https://prove2.me/submissions/407bddb7-219c-4523-85b1-0aa7b3161969

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/DecLoop.lean (solution of MIPRE.Cost.Prog.preProg_runs_nilB);
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Prog
open Data
theorem _root_.solution (uk : Data) (remX remY : List Data) (a : Data) (remA : List Data)
    (ctx : Data) :
    ∃ t ≤ 8, Eval [decState uk remX remY (a :: remA) [] ctx] preProg .nil t :=
  ⟨8, le_rfl, Eval.elim_cons (i := 0) (n := .nil) (a := uk)
    (b := .cons (list remX) (.cons (list remY) (.cons (list (a :: remA)) (.cons (list []) ctx))))
    (by simp [decState])
    (Eval.elim_cons (i := 1) (n := .nil) (a := list remX)
      (b := .cons (list remY) (.cons (list (a :: remA)) (.cons (list []) ctx))) (by simp)
      (Eval.elim_cons (i := 1) (n := .nil) (a := list remY)
        (b := .cons (list (a :: remA)) (.cons (list []) ctx)) (by simp)
        (Eval.elim_cons (i := 1) (n := .nil) (a := list (a :: remA)) (b := .cons (list []) ctx)
          (by simp)
          (Eval.elim_cons (i := 1) (n := .nil) (a := list []) (b := ctx) (by simp)
            (Eval.elim_cons (i := 2) (n := .nil) (a := a) (b := list remA) (by simp)
              (Eval.elim_nil (i := 2) (by simp) (Eval.nil _)))))))⟩
end MIPRE.Cost.Prog
