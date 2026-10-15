-- Prove2me | solution 1 for MIPRE.Cost.Machine.stepData_toData
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:44:04.930063+00:00
-- url     : https://prove2.me/submissions/03b437ea-1da9-490e-bd64-f2d8c38e8a84

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/MachineData.lean (solution of MIPRE.Cost.Machine.stepData_toData);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost.Data
theorem getList_list (l : List Data) (i : ℕ) : getList (Data.list l) i = Env.get l i := by
  induction i generalizing l with
  | zero => cases l <;> rfl
  | succ i ih =>
    unfold getList
    rw [Function.iterate_succ_apply]
    cases l with
    | nil => simp [Function.iterate_fixed right_nil, Env.get_nil]
    | cons a l => simpa [getList, Function.iterate_succ_apply] using ih l
end MIPRE.Cost.Data

namespace MIPRE.Cost.Machine
theorem right_list (l : List Data) : (Data.list l).right = Data.list l.tail := by
  cases l <;> rfl
end MIPRE.Cost.Machine

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine
theorem solution (c : Cfg) : stepData c.toData = (step c).toData := by
  obtain ⟨ctrl, env, kont⟩ := c
  cases ctrl with
  | ev p =>
    cases p with
    | var i =>
      simp [stepData, Cfg.toData, Ctrl.toData, evD, retD, stepEv, Prog.toData, step,
        Data.getList_list]
    | nil => simp [stepData, Cfg.toData, Ctrl.toData, evD, retD, stepEv, Prog.toData, step]
    | const d => simp [stepData, Cfg.toData, Ctrl.toData, evD, retD, stepEv, Prog.toData, step]
    | cons h t =>
      simp [stepData, Cfg.toData, Ctrl.toData, evD, stepEv, Prog.toData, step, Frame.toData]
    | elim i n c =>
      rcases hget : env.get i with _ | ⟨a, b⟩
      · simp [stepData, Cfg.toData, Ctrl.toData, evD, stepEv, Prog.toData, step,
          Data.getList_list, hget]
      · simp [stepData, Cfg.toData, Ctrl.toData, evD, stepEv, Prog.toData, step,
          Data.getList_list, hget]
    | let_ e b =>
      simp [stepData, Cfg.toData, Ctrl.toData, evD, stepEv, Prog.toData, step, Frame.toData]
    | loop b =>
      simp [stepData, Cfg.toData, Ctrl.toData, evD, stepEv, Prog.toData, step, Frame.toData]
  | ret v =>
    cases kont with
    | nil => simp [stepData, Cfg.toData, Ctrl.toData, retD, stepRet, step]
    | cons f k =>
      cases f with
      | cons1 t env' =>
        simp [stepData, Cfg.toData, Ctrl.toData, evD, retD, stepRet, step, Frame.toData]
      | cons2 a =>
        simp [stepData, Cfg.toData, Ctrl.toData, retD, stepRet, step, Frame.toData]
      | let1 b env' =>
        simp [stepData, Cfg.toData, Ctrl.toData, evD, retD, stepRet, step, Frame.toData]
      | loop1 b env' =>
        rcases v with _ | ⟨_ | ⟨x, y⟩, v'⟩
        · simp [stepData, Cfg.toData, Ctrl.toData, retD, stepRet, step, Frame.toData]
        · simp [stepData, Cfg.toData, Ctrl.toData, retD, stepRet, step, Frame.toData]
        · simp [stepData, Cfg.toData, Ctrl.toData, evD, retD, stepRet, step, Frame.toData,
            right_list]
