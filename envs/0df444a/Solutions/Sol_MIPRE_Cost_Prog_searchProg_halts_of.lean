-- Prove2me | solution 1 for MIPRE.Cost.Prog.searchProg_halts_of
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T17:03:58.661946+00:00
-- url     : https://prove2.me/submissions/5a14a587-6eab-4132-8d7c-8216bbac0baa

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Compression.lean (solution of MIPRE.Cost.Prog.searchProg_halts_of);
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
import Theorems.Thm_MIPRE_Cost_Eval_of_append_of_wellScoped
import Theorems.Thm_MIPRE_Cost_hardcode_time_rev

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost
theorem encode_prod {α β : Type*} [SizedEncoding α] [SizedEncoding β] (a : α) (b : β) :
    encode (a, b) = .cons (encode a) (encode b) := rfl
end MIPRE.Cost

namespace MIPRE.Cost.Prog
open Polynomial
/-- Inverting a call: a run of `callVar i q` is a run of the closed `q` on the value of
variable `i`. -/
theorem callVar_runs_rev {env : Env} {i : ℕ} {q : Prog} (hq : q.WellScoped 1) {r : Data}
    {t : ℕ} (h : Eval env (callVar i q) r t) : ∃ t' ≤ t, q.Runs (env.get i) r t' := by
  change Eval env (.let_ (.var i) q) r t at h
  cases h with
  | let_ h₁ h₂ =>
    cases h₁
    exact ⟨_, by omega,
      Eval.of_append_of_wellScoped (env := [env.get i]) (extra := env) h₂ hq⟩
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
open Polynomial
theorem searchProg_wellScoped {univ S : Prog} (hU : univ.WellScoped 1) (hS : S.WellScoped 1) :
    (searchProg univ S).WellScoped 1 :=
  ⟨Nat.zero_lt_one, trivial, by omega, trivial, callVar_wellScoped (by omega) hU,
    ⟨show 0 < 6 by omega, show 2 < 6 by omega⟩, callVar_wellScoped (by omega) hS⟩
end MIPRE.Cost.Prog

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open Polynomial
theorem solution (U : UniversalMachine) {S : Prog} (hS : S.WellScoped 1)
    {c' e : Prog} {m : ℕ} {r : Data} {T : ℕ}
    (h : (hardcode (searchProg U.univ S) (encode ((c', (e, (m, m))), m))).Runs .nil r T) :
    ∃ x tx, c'.Runs (encode (e, (m, m))) x tx ∧ Halts S (.cons x (encode m)) := by
  obtain ⟨T', -, h'⟩ := hardcode_time_rev (searchProg_wellScoped U.closed hS) h
  change Eval [Data.cons (encode ((c', (e, (m, m))), m)) Data.nil] (.elim 0 .nil _) r T' at h'
  cases h' with
  | elim_nil hget _ => simp at hget
  | elim_cons hget h₁ =>
    rw [Env.get_cons_zero] at hget
    obtain ⟨rfl, rfl⟩ := Data.cons.inj hget
    cases h₁ with
    | elim_nil hget₂ _ => simp [encode_prod] at hget₂
    | elim_cons hget₂ h₂ =>
      rw [Env.get_cons_zero, encode_prod] at hget₂
      obtain ⟨rfl, rfl⟩ := Data.cons.inj hget₂
      cases h₂ with
      | let_ h₃ h₄ =>
        obtain ⟨tU, -, hU⟩ := callVar_runs_rev U.closed h₃
        rw [Env.get_cons_zero] at hU
        obtain ⟨tx, hx⟩ := U.halts_of c' (encode (e, (m, m))) _ tU hU
        cases h₄ with
        | let_ h₅ h₆ =>
          cases h₅ with
          | cons h₅₁ h₅₂ =>
            cases h₅₁
            cases h₅₂
            obtain ⟨ts, -, hSr⟩ := callVar_runs_rev hS h₆
            simp only [Env.get_cons_zero, Env.get_cons_succ] at hSr
            exact ⟨_, tx, hx, _, ts, hSr⟩
