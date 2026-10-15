-- Prove2me | solution 1 for MIPRE.Cost.compressibility_criterion
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T17:36:05.523261+00:00
-- url     : https://prove2.me/submissions/122594b4-638c-4b77-a7b2-9573b8e1e3b6

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Compression.lean (solution of MIPRE.Cost.compressibility_criterion);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.ENat.Lattice
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
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Succinct
import Definitions.Def_MIPRE_Foundations_Cost_Clocked
import Definitions.Def_MIPRE_Foundations_Cost_Threshold
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Definitions.Def_MIPRE_Foundations_Compression
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Cost_Eval_of_append_of_wellScoped
import Theorems.Thm_MIPRE_Cost_compressibility_criterion_levels

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open Polynomial
theorem solution
    (A B : Set BitStr)
    (yYes : BitStr) (hyes : yYes ∈ A) (yNo : BitStr) (hno : yNo ∈ B)
    (S : Prog) (hSws : S.WellScoped 1) (hS : ∀ x : BitStr, Halts S (encode x) ↔ x ∉ B)
    (Compr : PolyTimeFun ((Prog × ℕ) × ℕ) BitStr)
    (hCompr : ∀ (c : Prog) (m : ℕ) (x : BitStr) (n : ℕ),
      IsSuccinctDesc c m x →
        (x ∈ A → Compr ((c, m), n) ∈ A) ∧ (x ∈ B → Compr ((c, m), n) ∈ B)) :
    ∃ g : PolyTimeFun Prog BitStr,
      ∀ e : Prog,
        (Halts e .nil → g e ∈ A) ∧
        (¬ Halts e .nil → g e ∈ B) := by
  -- the semidecider on pairs `(x, n)`: project to `x`
  have hS' : ∀ (x : BitStr) (n : ℕ), Halts (.let_ Prog.fstProg S) (encode (x, n)) ↔ x ∉ B := by
    intro x n
    rw [← hS x]
    have hpre := Prog.fstProg_runs (encode x) (encode n)
    constructor
    · rintro ⟨r, t, h⟩
      cases h with
      | let_ h₁ h₂ =>
        obtain ⟨rfl, -⟩ := h₁.deterministic hpre
        exact ⟨r, _, Eval.of_append_of_wellScoped (env := [_]) (extra := [_]) h₂ hSws⟩
    · rintro ⟨r, t, h⟩
      exact ⟨r, _, Eval.let_ hpre (Eval.append_of_wellScoped h hSws _)⟩
  obtain ⟨g, K, hg⟩ := compressibility_criterion_levels (fun _ => A) (fun _ => B) 0
    yYes (fun _ _ => hyes) yNo (fun _ _ => hno) (.let_ Prog.fstProg S)
    ⟨Prog.fstProg_wellScoped, hSws.mono (by omega) _⟩ hS'
    (Compr.comp (PolyTimeFun.pair (PolyTimeFun.id _) PolyTimeFun.snd))
    (fun c x n _ _ hsucc _ => by simpa using hCompr c n x n hsucc)
  exact ⟨g, fun e => ⟨(hg e).2.1, (hg e).2.2⟩⟩
