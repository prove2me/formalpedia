-- Prove2me | solution 1 for MIPRE.Cost.Machine.subProg_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:53:41.740032+00:00
-- url     : https://prove2.me/submissions/1851f2a8-ec6b-4170-9843-16eae4f2aca4

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Universal.lean (solution of MIPRE.Cost.Machine.subProg_runs);
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

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine
open Polynomial
open MIPRE.Cost.Prog
theorem solution (a : ℕ) : ∀ (b : ℕ) (env : Env),
    ∃ t ≤ subBound a b,
      Eval (Data.cons (.ofNat a) (.ofNat b) :: env) subProg (subResult a b) t := by
  induction a with
  | zero =>
    intro b env
    have run : Eval (Data.cons (.ofNat 0) (.ofNat b) :: env) subBody
        (.cons .nil (.cons (.cons .nil .nil) (.ofNat b))) _ :=
      Eval.elim_cons (i := 0) (a := .ofNat 0) (b := .ofNat b) (by simp)
        (Eval.elim_nil (i := 0) (by simp [Data.ofNat])
          (Eval.cons (Eval.nil _) (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
            (Eval.var_of_get (i := 1) (v := .ofNat b) (by simp)))))
    refine ⟨_, ?_, by simpa [subResult, subProg] using Eval.loop_stop run⟩
    unfold subBound
    try simp only [Data.size_ofNat]
    nlinarith
  | succ a ih =>
    intro b env
    cases b with
    | zero =>
      have run : Eval (Data.cons (.ofNat (a + 1)) (.ofNat 0) :: env) subBody
          (.cons .nil .nil) _ :=
        Eval.elim_cons (i := 0) (a := .ofNat (a + 1)) (b := .ofNat 0) (by simp)
          (Eval.elim_cons (i := 0) (a := .nil) (b := .ofNat a) (by simp [Data.ofNat])
            (Eval.elim_nil (i := 3) (by simp [Data.ofNat])
              (Eval.cons (Eval.nil _) (Eval.nil _))))
      refine ⟨_, ?_, by simpa [subResult, subProg] using Eval.loop_stop run⟩
      unfold subBound
      nlinarith
    | succ b =>
      obtain ⟨t, ht, hrest⟩ := ih b env
      have run : Eval (Data.cons (.ofNat (a + 1)) (.ofNat (b + 1)) :: env) subBody
          (.cons (.cons .nil .nil) (.cons (.ofNat a) (.ofNat b))) _ :=
        Eval.elim_cons (i := 0) (a := .ofNat (a + 1)) (b := .ofNat (b + 1)) (by simp)
          (Eval.elim_cons (i := 0) (a := .nil) (b := .ofNat a) (by simp [Data.ofNat])
            (Eval.elim_cons (i := 3) (a := .nil) (b := .ofNat b) (by simp [Data.ofNat])
              (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
                (Eval.cons (Eval.var_of_get (i := 3) (v := .ofNat a) (by simp))
                  (Eval.var_of_get (i := 1) (v := .ofNat b) (by simp))))))
      have hres : subResult (a + 1) (b + 1) = subResult a b := by
        simp [subResult, Nat.succ_sub_succ]
      refine ⟨_, ?_, by rw [hres]; exact Eval.loop_step run hrest⟩
      unfold subBound at ht ⊢
      try simp only [Data.size_ofNat]
      nlinarith [ht]
