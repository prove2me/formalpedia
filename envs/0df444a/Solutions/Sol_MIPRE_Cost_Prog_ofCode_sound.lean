-- Prove2me | solution 1 for MIPRE.Cost.Prog.ofCode_sound
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T17:40:08.043805+00:00
-- url     : https://prove2.me/submissions/4c3c317e-0dc2-42e2-9820-9bded1b7f746

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/FromPartrec.lean (solution of MIPRE.Cost.Prog.ofCode_sound);
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
import Theorems.Thm_MIPRE_Cost_Prog_fixBody_runs
import Theorems.Thm_MIPRE_Cost_Prog_ofCode_wellScoped

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
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
theorem solution : ∀ (c : Code) (v w : List ℕ), w ∈ c.eval v →
    ∃ t, (ofCode c).Runs (encL v) (encL w) t
  | .zero', v, w, hw => by
    simp only [Code.eval, Part.pure_eq_some, Part.mem_some_iff] at hw
    subst hw
    exact ⟨_, Eval.cons (Eval.nil _) (Eval.var_of_get (i := 0) (v := encL v) (by simp))⟩
  | .succ, v, w, hw => by
    simp only [Code.eval, Part.pure_eq_some, Part.mem_some_iff] at hw
    subst hw
    rcases v with _ | ⟨n, v'⟩
    · exact ⟨_, Eval.elim_nil (i := 0) (by simp)
        (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _)) (Eval.nil _))⟩
    · exact ⟨_, Eval.elim_cons (i := 0) (a := .ofNat n) (b := encL v') (by simp)
        (Eval.cons (Eval.cons (Eval.nil _) (Eval.var_of_get (i := 0) (v := .ofNat n) (by simp)))
          (Eval.nil _))⟩
  | .tail, v, w, hw => by
    simp only [Code.eval, Part.pure_eq_some, Part.mem_some_iff] at hw
    subst hw
    rcases v with _ | ⟨n, v'⟩
    · exact ⟨_, Eval.elim_nil (i := 0) (by simp) (Eval.nil _)⟩
    · exact ⟨_, Eval.elim_cons (i := 0) (a := .ofNat n) (b := encL v') (by simp)
        (Eval.var_of_get (i := 1) (v := encL v') (by simp))⟩
  | .cons f fs, v, w, hw => by
    simp only [Code.eval, Part.bind_eq_bind, Part.mem_bind_iff, Part.pure_eq_some,
      Part.mem_some_iff] at hw
    obtain ⟨fv, hfv, fsv, hfsv, rfl⟩ := hw
    obtain ⟨t₁, h₁⟩ := solution f v fv hfv
    obtain ⟨t₂, h₂⟩ := solution fs v fsv hfsv
    obtain ⟨s, h₃⟩ := consTail_runs fv fsv v
    have h₂' := callVar_eval (env := [encL fv, encL v]) (i := 1) (ofCode_wellScoped fs)
      (v := encL v) (by simp) h₂
    exact ⟨_, Eval.let_ h₁ (Eval.let_ h₂' h₃)⟩
  | .comp f g, v, w, hw => by
    simp only [Code.eval] at hw
    obtain ⟨u, hu, hw⟩ := Part.mem_bind_iff.mp hw
    obtain ⟨t₁, h₁⟩ := solution g v u hu
    obtain ⟨t₂, h₂⟩ := solution f u w hw
    exact ⟨_, Eval.let_ h₁ (Eval.append_of_wellScoped h₂ (ofCode_wellScoped f) [encL v])⟩
  | .case f g, v, w, hw => by
    rcases v with _ | ⟨n, v'⟩
    · simp only [Code.eval, List.headI_nil, List.tail_nil] at hw
      obtain ⟨t, h⟩ := solution f [] w hw
      exact ⟨_, Eval.elim_nil (i := 0) (by simp)
        (callVar_eval (env := [encL []]) (i := 0) (ofCode_wellScoped f) (v := encL []) (by simp) h)⟩
    · rcases n with _ | y
      · simp only [Code.eval, List.headI_cons, List.tail_cons] at hw
        obtain ⟨t, h⟩ := solution f v' w hw
        exact ⟨_, Eval.elim_cons (i := 0) (a := .nil) (b := encL v') (by simp [Data.ofNat])
          (Eval.elim_nil (i := 0) (by simp)
            (callVar_eval (env := [Data.nil, encL v', encL (0 :: v')]) (i := 1)
              (ofCode_wellScoped f) (v := encL v') (by simp) h))⟩
      · simp only [Code.eval, List.headI_cons, List.tail_cons] at hw
        obtain ⟨t, h⟩ := solution g (y :: v') w hw
        exact ⟨_, Eval.elim_cons (i := 0) (a := .cons .nil (.ofNat y)) (b := encL v')
          (by simp [Data.ofNat])
          (Eval.elim_cons (i := 0) (a := .nil) (b := .ofNat y) (by simp)
            (Eval.let_ (casePair_runs y v')
              (callVar_eval (env := encL (y :: v') :: [Data.nil, .ofNat y, .ofNat (y + 1), encL v',
                encL ((y + 1) :: v')]) (i := 0) (ofCode_wellScoped g) (v := encL (y :: v'))
                (by simp) h)))⟩
  | .fix f, v, w, hw => by
    simp only [Code.eval] at hw
    refine PFun.fixInduction (C := fun v => ∃ t, (ofCode (.fix f)).Runs (encL v) (encL w) t) hw
      fun v hv ih => ?_
    rcases PFun.mem_fix_iff.1 hv with h1 | ⟨v'', h2, -⟩
    · simp only [Part.mem_map_iff] at h1
      obtain ⟨fv, hfv, hfl⟩ := h1
      obtain ⟨t₁, h₁⟩ := solution f v fv hfv
      obtain ⟨s, hb⟩ := fixBody_runs (ofCode_wellScoped f) v fv h₁
      rcases fv with _ | ⟨_ | y, t'⟩
      · simp only [List.headI_nil, Nat.default_eq_zero, List.tail_nil, ↓reduceIte,
          Sum.inl.injEq] at hfl
        subst hfl
        exact ⟨_, Eval.loop_stop hb⟩
      · simp only [List.headI_cons, List.tail_cons, ↓reduceIte, Sum.inl.injEq] at hfl
        subst hfl
        exact ⟨_, Eval.loop_stop hb⟩
      · simp at hfl
    · simp only [Part.mem_map_iff] at h2
      obtain ⟨fv, hfv, hfl⟩ := h2
      obtain ⟨t₁, h₁⟩ := solution f v fv hfv
      obtain ⟨s, hb⟩ := fixBody_runs (ofCode_wellScoped f) v fv h₁
      rcases fv with _ | ⟨_ | y, t'⟩
      · simp at hfl
      · simp at hfl
      · simp only [List.headI_cons, List.tail_cons, Nat.succ_ne_zero, ↓reduceIte,
          Sum.inr.injEq] at hfl
        subst hfl
        obtain ⟨t₂, h₂⟩ := ih t' (by
          simp only [Part.mem_map_iff]
          exact ⟨(y + 1) :: t', hfv, by simp⟩)
        exact ⟨_, Eval.loop_step hb h₂⟩
