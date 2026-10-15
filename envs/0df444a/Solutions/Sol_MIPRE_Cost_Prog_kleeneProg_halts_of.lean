-- Prove2me | solution 1 for MIPRE.Cost.Prog.kleeneProg_halts_of
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:33:40.167333+00:00
-- url     : https://prove2.me/submissions/67dab4be-5024-46a8-8876-aee549ab5567

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Kleene.lean (solution of MIPRE.Cost.Prog.kleeneProg_halts_of);
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
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Cost_Eval_of_append_of_wellScoped

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
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
/-- The run of the pairing prefix of `kleeneProg`. -/
theorem kleeneProg_pair_eval (x : Prog) (v : Data) :
    Eval [encode x, v, Data.cons (encode x) v] (.cons (.var 0) (.var 0))
      (.cons (encode x) (encode x)) ((encode x).size + 1 + ((encode x).size + 1) + 1) :=
  Eval.cons (Eval.var_of_get (i := 0) (v := encode x) (by simp))
    (Eval.var_of_get (i := 0) (v := encode x) (by simp))
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
open Polynomial
/-- The run of the s-m-n step of `kleeneProg`. -/
theorem kleeneProg_smn_eval (x : Prog) (v : Data) :
    Eval [Data.cons (encode x) (encode x), encode x, v, Data.cons (encode x) v]
      (callVar 0 smnProg) (encode (hardcode x (encode x)))
      ((Data.cons (encode x) (encode x)).size + 1 + ((encode x).size + (encode x).size + 38) + 1) :=
  callVar_eval (i := 0) smnProg_wellScoped (v := .cons (encode x) (encode x)) (by simp)
    (smnProg_runs (encode x) (encode x))
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
open Polynomial
/-- The run of the final pairing step of `kleeneProg`. -/
theorem kleeneProg_pair2_eval (x : Prog) (v : Data) (F : PolyTimeFun Prog Prog) :
    Eval (encode (F (hardcode x (encode x))) :: encode (hardcode x (encode x)) ::
        [Data.cons (encode x) (encode x), encode x, v, Data.cons (encode x) v])
      (.cons (.var 0) (.var 4)) (.cons (encode (F (hardcode x (encode x)))) v)
      ((encode (F (hardcode x (encode x)))).size + 1 + (v.size + 1) + 1) :=
  Eval.cons (Eval.var_of_get (i := 0) (v := encode (F (hardcode x (encode x)))) (by simp))
    (Eval.var_of_get (i := 4) (v := v) (by simp))
end MIPRE.Cost.Prog

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open Polynomial
theorem solution (U : UniversalMachine) (F : PolyTimeFun Prog Prog) (x : Prog)
    {v r : Data} {T : ℕ} (h : (kleeneProg U.univ F).Runs (.cons (encode x) v) r T) :
    ∃ t, (F (hardcode x (encode x))).Runs v r t := by
  obtain ⟨tF, -, hF⟩ := F.computes (hardcode x (encode x))
  have s3 := callVar_eval
    (env := encode (hardcode x (encode x)) ::
      [Data.cons (encode x) (encode x), encode x, v, Data.cons (encode x) v])
    (i := 0) F.closed (v := encode (hardcode x (encode x))) (by simp) hF
  change Eval [Data.cons (encode x) v] (.elim 0 .nil _) r T at h
  cases h with
  | elim_nil hget _ => simp at hget
  | elim_cons hget h₁ =>
    rw [Env.get_cons_zero] at hget
    obtain ⟨rfl, rfl⟩ := Data.cons.inj hget
    cases h₁ with
    | let_ h₂ h₃ =>
      obtain ⟨rfl, -⟩ := h₂.deterministic (kleeneProg_pair_eval x v)
      cases h₃ with
      | let_ h₄ h₅ =>
        obtain ⟨rfl, -⟩ := h₄.deterministic (kleeneProg_smn_eval x v)
        cases h₅ with
        | let_ h₆ h₇ =>
          obtain ⟨rfl, -⟩ := h₆.deterministic s3
          cases h₇ with
          | let_ h₈ h₉ =>
            obtain ⟨rfl, -⟩ := h₈.deterministic (kleeneProg_pair2_eval x v F)
            obtain ⟨tU, -, hU⟩ := callVar_runs_rev U.closed h₉
            rw [Env.get_cons_zero] at hU
            exact U.halts_of _ _ _ _ hU
