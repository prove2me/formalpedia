-- Prove2me | solution 1 for MIPRE.Cost.Prog.fixBody_runs
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T17:38:54.122859+00:00
-- url     : https://prove2.me/submissions/69bde971-0e49-4a22-a74f-c898676e6dc9

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/FromPartrec.lean (solution of MIPRE.Cost.Prog.fixBody_runs);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.TuringMachine.Config
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
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open Turing.ToPartrec (Code)
theorem solution {pf : Prog} (hpf : pf.WellScoped 1) (v fv : List ℕ) {t : ℕ}
    (h : pf.Runs (encL v) (encL fv) t) :
    ∃ s, Eval [encL v] (fixBody pf) (fixFlag fv) s := by
  have h1 := callVar_eval (env := [encL v]) (i := 0) hpf (v := encL v) (by simp) h
  rcases fv with _ | ⟨_ | y, t'⟩
  · exact ⟨_, Eval.let_ h1 (Eval.elim_nil (i := 0) (by simp) (Eval.cons (Eval.nil _) (Eval.nil _)))⟩
  · exact ⟨_, Eval.let_ h1 (Eval.elim_cons (i := 0) (a := .nil) (b := encL t') (by simp [Data.ofNat])
      (Eval.elim_nil (i := 0) (by simp)
        (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 1) (v := encL t') (by simp)))))⟩
  · exact ⟨_, Eval.let_ h1 (Eval.elim_cons (i := 0) (a := .cons .nil (.ofNat y)) (b := encL t')
      (by simp [Data.ofNat])
      (Eval.elim_cons (i := 0) (a := .nil) (b := .ofNat y) (by simp)
        (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
          (Eval.var_of_get (i := 3) (v := encL t') (by simp)))))⟩
