-- Prove2me | solution 1 for MIPRE.Cost.Prog.ofCode_complete
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T17:40:41.058036+00:00
-- url     : https://prove2.me/submissions/875350d1-73e5-4723-97d7-237f770858aa

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/FromPartrec.lean (solution of MIPRE.Cost.Prog.ofCode_complete);
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
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Cost_Eval_of_append_of_wellScoped
import Theorems.Thm_MIPRE_Cost_Prog_fixBody_runs
import Theorems.Thm_MIPRE_Cost_Prog_ofCode_sound
import Theorems.Thm_MIPRE_Cost_Prog_ofCode_wellScoped

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
open Turing.ToPartrec (Code)
theorem consTail_runs (fv fsv v : List ℕ) :
    ∃ s, Eval [encL fsv, encL fv, encL v] consTail (encL (fv.headI :: fsv)) s := by
  rcases fv with _ | ⟨a, fv'⟩
  · exact ⟨_, Eval.cons (Eval.elim_nil (i := 1) (by simp) (Eval.nil _))
      (Eval.var_of_get (i := 0) (v := encL fsv) (by simp))⟩
  · exact ⟨_, Eval.cons (Eval.elim_cons (i := 1) (a := .ofNat a) (b := encL fv') (by simp)
      (Eval.var_of_get (i := 0) (v := .ofNat a) (by simp)))
      (Eval.var_of_get (i := 0) (v := encL fsv) (by simp))⟩
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
open Turing.ToPartrec (Code)
/-- The pairing step of the `case` translation, in an environment
`[nil, ofNat y, ofNat (y + 1), encL v', encL (y + 1 :: v')]`. -/
theorem casePair_runs (y : ℕ) (v' : List ℕ) :
    Eval [Data.nil, .ofNat y, .ofNat (y + 1), encL v', encL ((y + 1) :: v')]
      (.cons (.var 1) (.var 3)) (encL (y :: v')) ((Data.ofNat y).size + 1 + ((encL v').size + 1) + 1) :=
  Eval.cons (Eval.var_of_get (i := 1) (v := .ofNat y) (by simp))
    (Eval.var_of_get (i := 3) (v := encL v') (by simp))
end MIPRE.Cost.Prog

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open Turing.ToPartrec (Code)
theorem solution : ∀ (c : Code) (v : List ℕ) (r : Data) (t : ℕ),
    (ofCode c).Runs (encL v) r t → ∃ w, r = encL w ∧ w ∈ c.eval v
  | .zero', v, r, t, h => by
    obtain ⟨t', h'⟩ := ofCode_sound .zero' v (0 :: v) (by simp [Code.eval])
    obtain ⟨rfl, -⟩ := h.deterministic h'
    exact ⟨0 :: v, rfl, by simp [Code.eval]⟩
  | .succ, v, r, t, h => by
    obtain ⟨t', h'⟩ := ofCode_sound .succ v [v.headI.succ] (by simp [Code.eval])
    obtain ⟨rfl, -⟩ := h.deterministic h'
    exact ⟨[v.headI.succ], rfl, by simp [Code.eval]⟩
  | .tail, v, r, t, h => by
    obtain ⟨t', h'⟩ := ofCode_sound .tail v v.tail (by simp [Code.eval])
    obtain ⟨rfl, -⟩ := h.deterministic h'
    exact ⟨v.tail, rfl, by simp [Code.eval]⟩
  | .cons f fs, v, r, t, h => by
    change Eval [encL v] (.let_ (ofCode f) (.let_ (callVar 1 (ofCode fs)) consTail)) r t at h
    cases h with
    | let_ h₁ h₂ =>
      obtain ⟨fv, rfl, hfv⟩ := solution f v _ _ h₁
      cases h₂ with
      | let_ h₃ h₄ =>
        obtain ⟨t₃, -, h₃'⟩ := callVar_runs_rev (ofCode_wellScoped fs) h₃
        simp only [Env.get_cons_succ, Env.get_cons_zero] at h₃'
        obtain ⟨fsv, rfl, hfsv⟩ := solution fs v _ _ h₃'
        obtain ⟨s, h₅⟩ := consTail_runs fv fsv v
        obtain ⟨rfl, -⟩ := h₄.deterministic h₅
        refine ⟨fv.headI :: fsv, rfl, ?_⟩
        simp only [Code.eval, Part.bind_eq_bind, Part.mem_bind_iff, Part.pure_eq_some,
          Part.mem_some_iff]
        exact ⟨fv, hfv, fsv, hfsv, rfl⟩
  | .comp f g, v, r, t, h => by
    change Eval [encL v] (.let_ (ofCode g) (ofCode f)) r t at h
    cases h with
    | let_ h₁ h₂ =>
      obtain ⟨u, rfl, hu⟩ := solution g v _ _ h₁
      have h₂' := Eval.of_append_of_wellScoped (env := [encL u]) (extra := [encL v]) h₂
        (ofCode_wellScoped f)
      obtain ⟨w, rfl, hw⟩ := solution f u _ _ h₂'
      refine ⟨w, rfl, ?_⟩
      simp only [Code.eval]
      exact Part.mem_bind_iff.mpr ⟨u, hu, hw⟩
  | .case f g, v, r, t, h => by
    change Eval [encL v] (.elim 0 (callVar 0 (ofCode f))
      (.elim 0 (callVar 1 (ofCode f)) (.let_ (.cons (.var 1) (.var 3)) (callVar 0 (ofCode g))))) r t
      at h
    rcases v with _ | ⟨n, v'⟩
    · cases h with
      | elim_nil hget h₁ =>
        obtain ⟨t₁, -, h₁'⟩ := callVar_runs_rev (ofCode_wellScoped f) h₁
        simp only [Env.get_cons_zero] at h₁'
        obtain ⟨w, rfl, hw⟩ := solution f [] _ _ h₁'
        exact ⟨w, rfl, by simpa [Code.eval] using hw⟩
      | elim_cons hget _ => simp at hget
    · cases h with
      | elim_nil hget _ => simp at hget
      | elim_cons hget h₁ =>
        simp only [Env.get_cons_zero, encL_cons, Data.cons.injEq] at hget
        obtain ⟨rfl, rfl⟩ := hget
        rcases n with _ | y
        · cases h₁ with
          | elim_nil hget h₂ =>
            obtain ⟨t₂, -, h₂'⟩ := callVar_runs_rev (ofCode_wellScoped f) h₂
            simp only [Env.get_cons_succ, Env.get_cons_zero] at h₂'
            obtain ⟨w, rfl, hw⟩ := solution f v' _ _ h₂'
            exact ⟨w, rfl, by simpa [Code.eval] using hw⟩
          | elim_cons hget _ => simp [Data.ofNat] at hget
        · cases h₁ with
          | elim_nil hget _ => simp [Data.ofNat] at hget
          | elim_cons hget h₂ =>
            simp only [Env.get_cons_zero, Data.ofNat, Data.cons.injEq] at hget
            obtain ⟨rfl, rfl⟩ := hget
            cases h₂ with
            | let_ h₃ h₄ =>
              obtain ⟨rfl, -⟩ := h₃.deterministic (casePair_runs y v')
              obtain ⟨t₄, -, h₄'⟩ := callVar_runs_rev (ofCode_wellScoped g) h₄
              simp only [Env.get_cons_zero] at h₄'
              obtain ⟨w, rfl, hw⟩ := solution g (y :: v') _ _ h₄'
              exact ⟨w, rfl, by simpa [Code.eval] using hw⟩
  | .fix f, v, r, t, h => by
    induction t using Nat.strongRecOn generalizing v r with
    | ind t ih =>
    change Eval [encL v] (.loop (fixBody (ofCode f))) r t at h
    -- the body's run determines the value of `f`
    have body_inv : ∀ {res : Data} {s : ℕ}, Eval [encL v] (fixBody (ofCode f)) res s →
        ∃ fv, fv ∈ f.eval v ∧ res = fixFlag fv := by
      intro res s hb
      change Eval [encL v] (.let_ (callVar 0 (ofCode f)) _) res s at hb
      cases hb with
      | let_ h₁ h₂ =>
        obtain ⟨t₁, -, h₁'⟩ := callVar_runs_rev (ofCode_wellScoped f) h₁
        simp only [Env.get_cons_zero] at h₁'
        obtain ⟨fv, rfl, hfv⟩ := solution f v _ _ h₁'
        obtain ⟨s', hb'⟩ := fixBody_runs (ofCode_wellScoped f) v fv (h₁'.cast_cost rfl)
        change Eval [encL v] (.let_ (callVar 0 (ofCode f)) _) (fixFlag fv) s' at hb'
        cases hb' with
        | let_ h₁'' h₂'' =>
          obtain ⟨rfl, -⟩ := h₁.deterministic h₁''
          obtain ⟨rfl, -⟩ := h₂.deterministic h₂''
          exact ⟨fv, hfv, rfl⟩
    cases h with
    | loop_nil hb =>
      obtain ⟨fv, -, hres⟩ := body_inv hb
      rcases fv with _ | ⟨_ | y, t'⟩ <;> simp [fixFlag] at hres
    | loop_stop hb =>
      obtain ⟨fv, hfv, hres⟩ := body_inv hb
      rcases fv with _ | ⟨_ | y, t'⟩
      · simp only [fixFlag, Data.cons.injEq] at hres
        obtain ⟨-, rfl⟩ := hres
        refine ⟨[], rfl, ?_⟩
        simp only [Code.eval]
        refine PFun.mem_fix_iff.2 (Or.inl ?_)
        simp only [Part.mem_map_iff]
        exact ⟨[], hfv, by simp⟩
      · simp only [fixFlag, Data.cons.injEq] at hres
        obtain ⟨-, rfl⟩ := hres
        refine ⟨t', rfl, ?_⟩
        simp only [Code.eval]
        refine PFun.mem_fix_iff.2 (Or.inl ?_)
        simp only [Part.mem_map_iff]
        exact ⟨0 :: t', hfv, by simp⟩
      · simp [fixFlag] at hres
    | loop_step hb hrest =>
      obtain ⟨fv, hfv, hres⟩ := body_inv hb
      rcases fv with _ | ⟨_ | y, t'⟩
      · simp [fixFlag] at hres
      · simp [fixFlag] at hres
      · simp only [fixFlag, Data.cons.injEq] at hres
        obtain ⟨-, rfl⟩ := hres
        obtain ⟨w, rfl, hw⟩ := ih _ (by omega) t' r hrest
        refine ⟨w, rfl, ?_⟩
        simp only [Code.eval] at hw ⊢
        refine PFun.mem_fix_iff.2 (Or.inr ⟨t', ?_, hw⟩)
        simp only [Part.mem_map_iff]
        exact ⟨(y + 1) :: t', hfv, by simp⟩
