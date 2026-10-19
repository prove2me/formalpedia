-- Prove2me | solution 1 for MIPRE.Cost.Prog.finalProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:30:41.707008+00:00
-- url     : https://prove2.me/submissions/1e9a6fc5-2e97-43c0-b61d-609d4d99ca24

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/DecLoop.lean (solution of MIPRE.Cost.Prog.finalProg_runs);
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
theorem _root_.solution (remX remY remA remB : List Data) (ctx : Data) :
    ∃ t ≤ 12, Eval [Data.cons (list remX) (.cons (list remY) (.cons (list remA)
      (.cons (list remB) ctx)))] finalProg
      (.cons .nil (ofBool (decide (remA = [] ∧ remB = [])))) t := by
  rcases remA with _ | ⟨a, remA⟩
  · rcases remB with _ | ⟨b, remB⟩
    · have run : Eval [Data.cons (list remX) (.cons (list remY) (.cons (list [])
          (.cons (list []) ctx)))] finalProg (.cons .nil (.cons .nil .nil)) _ :=
        Eval.elim_cons (i := 0) (n := .nil) (a := list remX)
          (b := .cons (list remY) (.cons (list []) (.cons (list []) ctx))) (by simp)
          (Eval.elim_cons (i := 1) (n := .nil) (a := list remY)
            (b := .cons (list []) (.cons (list []) ctx)) (by simp)
            (Eval.elim_cons (i := 1) (n := .nil) (a := list []) (b := .cons (list []) ctx) (by simp)
              (Eval.elim_nil (i := 0) (by simp)
                (Eval.elim_cons (i := 1) (n := .nil) (a := list []) (b := ctx) (by simp)
                  (Eval.elim_nil (i := 0) (by simp)
                    (Eval.cons (Eval.nil _) (Eval.cons (Eval.nil _) (Eval.nil _))))))))
      refine ⟨_, ?_, by simpa [ofBool] using run⟩
      norm_num
    · have run : Eval [Data.cons (list remX) (.cons (list remY) (.cons (list [])
          (.cons (list (b :: remB)) ctx)))] finalProg (.cons .nil .nil) _ :=
        Eval.elim_cons (i := 0) (n := .nil) (a := list remX)
          (b := .cons (list remY) (.cons (list []) (.cons (list (b :: remB)) ctx))) (by simp)
          (Eval.elim_cons (i := 1) (n := .nil) (a := list remY)
            (b := .cons (list []) (.cons (list (b :: remB)) ctx)) (by simp)
            (Eval.elim_cons (i := 1) (n := .nil) (a := list []) (b := .cons (list (b :: remB)) ctx)
              (by simp)
              (Eval.elim_nil (i := 0) (by simp)
                (Eval.elim_cons (i := 1) (n := .nil) (a := list (b :: remB)) (b := ctx) (by simp)
                  (Eval.elim_cons (i := 0) (n := .cons .nil (.cons .nil .nil)) (a := b)
                    (b := list remB) (by simp)
                    (Eval.cons (Eval.nil _) (Eval.nil _)))))))
      refine ⟨_, ?_, by simpa [ofBool] using run⟩
      norm_num
  · have run : Eval [Data.cons (list remX) (.cons (list remY) (.cons (list (a :: remA))
        (.cons (list remB) ctx)))] finalProg (.cons .nil .nil) _ :=
      Eval.elim_cons (i := 0) (n := .nil) (a := list remX)
        (b := .cons (list remY) (.cons (list (a :: remA)) (.cons (list remB) ctx))) (by simp)
        (Eval.elim_cons (i := 1) (n := .nil) (a := list remY)
          (b := .cons (list (a :: remA)) (.cons (list remB) ctx)) (by simp)
          (Eval.elim_cons (i := 1) (n := .nil) (a := list (a :: remA)) (b := .cons (list remB) ctx)
            (by simp)
            (Eval.elim_cons (i := 0) (n := _) (a := a) (b := list remA) (by simp)
              (Eval.cons (Eval.nil _) (Eval.nil _)))))
    refine ⟨_, ?_, by simpa [ofBool] using run⟩
    norm_num
end MIPRE.Cost.Prog
