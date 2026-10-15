-- Prove2me | solution 1 for MIPRE.Cost.Machine.stepCost_le_size
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:54:19.788756+00:00
-- url     : https://prove2.me/submissions/45c8f43c-6fde-4717-b597-3c26ebf12a08

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Universal.lean (solution of MIPRE.Cost.Machine.stepCost_le_size);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_Universal

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
open Prog
theorem size_left_le (d : Data) : d.left.size ≤ d.size := by cases d <;> simp; omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem size_right_le (d : Data) : d.right.size ≤ d.size := by cases d <;> simp; omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Prog
theorem size_getList_le (env : Data) (n : ℕ) : (Data.getList env n).size ≤ env.size := by
  unfold Data.getList
  refine (size_left_le _).trans ?_
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply']; exact (size_right_le _).trans ih
end MIPRE.Cost.Machine

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine
open Polynomial
open MIPRE.Cost.Prog
theorem solution (c : Cfg) : stepCost c ≤ (Cfg.toData c).size := by
  obtain ⟨ctrl, env, kont⟩ := c
  cases ctrl with
  | ev p =>
    cases p with
    | var i =>
      have h1 : (Env.get env i).size ≤ (Data.list env).size := by
        rw [← Data.getList_list]; exact size_getList_le _ _
      simp only [stepCost, Cfg.toData, Ctrl.toData, evD, Prog.toData, Data.size_cons,
        Data.size_nil, Data.size_ofNat]
      omega
    | nil => simp only [stepCost, Cfg.toData, Ctrl.toData, evD, Data.size_cons]; omega
    | const d =>
      simp only [stepCost, Cfg.toData, Ctrl.toData, evD, Prog.toData, Data.size_cons]; omega
    | cons h t => simp only [stepCost, Cfg.toData, Ctrl.toData, evD, Data.size_cons]; omega
    | elim i n c => simp only [stepCost, Cfg.toData, Ctrl.toData, evD, Data.size_cons]; omega
    | let_ e b => simp only [stepCost, Cfg.toData, Ctrl.toData, evD, Data.size_cons]; omega
    | loop b => simp only [stepCost, Cfg.toData, Ctrl.toData, evD, Data.size_cons]; omega
  | ret v =>
    cases kont with
    | nil => simp only [stepCost, Cfg.toData, Ctrl.toData, retD, Data.size_cons]; omega
    | cons f k =>
      cases f <;> simp only [stepCost, Cfg.toData, Ctrl.toData, retD, Data.size_cons] <;> omega
